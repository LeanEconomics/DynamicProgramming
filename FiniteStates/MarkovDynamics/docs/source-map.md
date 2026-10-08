# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 3, "Markov Dynamics" (pp. 81–104). Result, equation and exercise
numbers are the book's; page numbers are book pages. Lean names are relative
to `SargentStachurski.MarkovDynamics`. Where the Lean statement adds a
hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## Earlier-chapter facts restated (Basics)

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, p. 71, Ex 2.3.2 | Markov matrices; products and powers are Markov | `IsMarkov`, `IsMarkov.mul`, `IsMarkov.pow` |
| Vol. 1, p. 31 | Distributions on `X` | `IsDistribution` |
| Vol. 1, Ex 2.2.27, Ex 2.2.7 | `f ≤ g ⇒ Pf ≤ Pg`; `P𝟙 = 𝟙`; `|Ph(x)| ≤ ‖h‖`; `‖Pf − Pg‖ ≤ ‖f − g‖` | `IsMarkov.mulVec_le_mulVec`, `IsMarkov.mulVec_const`, `IsMarkov.abs_mulVec_le`, `IsMarkov.norm_mulVec_sub_le` |
| Vol. 1, p. 22, (1.17), Thm 1.2.3 | Global stability; contractions; uniqueness, rate, convergence, existence | `GloballyStable`, `globallyStable_of_tendsto`, `IsContractionOn`, `IsContractionOn.fixedPt_unique`, `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt`, `IsContractionOn.exists_fixedPt` |

## §3.1.1 Markov chains (pp. 81–86)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.1), p. 82 | `P`-Markov chain | Described through `P`; see [corrections](corrections.md) |
| Algorithm 3.1, p. 82 | Path probabilities `∏ P(Xₜ, Xₜ₊₁)` | `pathProb`, `paths`, `pathProb_snoc` |
| Ex 3.1.1, p. 83 | `{0, …, S + s}` is invariant for the inventory model | `Inventory.h`, `Inventory.h_le`, `Inventory.next` |
| p. 83 | `P(x, x') = ∑_d 1{h(x, d) = x'} φ(d)`, `φ` geometric | `Inventory.φ`, `Inventory.tsum_φ`, `Inventory.P`, `Inventory.isMarkov_P` |
| §3.1.1.3, p. 83 | `Pᵏ` is Markov | `IsMarkov.pow` |
| (3.2), Ex 3.1.2, p. 85 | `Pᵏ(x, x')` is the `k`-step transition probability; induction via `Pᵏ⁺¹ = ∑_z Pᵏ(x, z)P(z, x')` | `pow_apply_eq_sum_paths`, `pow_succ_apply` |
| Lemma 3.1.1, p. 85 | Irreducible iff every state reached from every state with positive probability | `Irreducible`, `IsMarkov.pow_add_apply_ge`, `IsMarkov.irreducible_iff` |
| Ex 3.1.3, p. 85 | The inventory chain is irreducible | `Inventory.P_pos`, `Inventory.next_eq_sState`, `Inventory.next_sState_zero`, `Inventory.next_fullState`, `Inventory.next_eq_SState`, `Inventory.irreducible_P` |

## §3.1.2 Stationarity and ergodicity (pp. 86–89)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.3)–(3.4), p. 86 | `ψₜ₊₁(x') = ∑ₓ P(x, x')ψₜ(x)`, i.e. `ψₜ₊₁ = ψₜP`; distributions map to distributions | `vecMul_apply`, `IsMarkov.isDistribution_vecMul`, `IsMarkov.isDistribution_vecMul_pow` |
| (3.5), p. 86 | `ψₜ = ψ₀Pᵗ` | `iterate_vecMul` |
| Ex 3.1.4, (3.6), p. 87 | `E h(Xₜ) = ψ₀Pᵗh = ⟨ψ₀Pᵗ, h⟩` | `expectation_eq_dotProduct` |
| p. 87 | Stationary distribution `ψ*P = ψ*`; `Xₜ ∼ ψ* ⇒ Xₜ₊ₖ ∼ ψ*` | `IsStationary`, `IsStationary.vecMul_pow` |
| (3.8), p. 88 | The day labourer's `P` is Markov | `DayLaborer`, `DayLaborer.P`, `DayLaborer.isMarkov_P` |
| Ex 3.1.6, (3.9), p. 88 | `ψ* = (β, α)/(α + β)` is the unique stationary distribution | `DayLaborer.ψstar`, `DayLaborer.isDistribution_ψstar`, `DayLaborer.isStationary_ψstar`, `DayLaborer.eq_ψstar_of_isStationary` |
| p. 88 | `ψPᵗ → ψ*` for every `ψ ∈ D(X)` | `DayLaborer.vecMul_zero_sub`, `DayLaborer.vecMul_pow_zero_sub`, `DayLaborer.abs_one_sub_lt_one`, `DayLaborer.tendsto_vecMul_pow` |
| Ex 3.1.7, p. 89 | Global stability of `ψ ↦ ψP` on `D(X)` for the day labourer, and for every `P ≫ 0` | `DayLaborer.P_pos`, `DayLaborer.globallyStable_distMap`; `l1`, `norm_le_l1`, `sum_vecMul`, `l1_vecMul_le`, `l1_vecMul_pow_le`, `tendsto_vecMul`, `globallyStable_of_pos`, `distMap`, `distMap_iterate`, `globallyStable_distMap` |

## §3.1.3 Approximation (pp. 89–91)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 90 | Equispaced grid `xᵢ₊₁ = xᵢ + s` | `Tauchen`, `Tauchen.x`, `Tauchen.x_mono` |
| p. 91, rules (i)–(iii) | Tauchen's transition probabilities | `Tauchen.Pnat`, `Tauchen.P`, `Tauchen.Pnat_zero`, `Tauchen.Pnat_last`, `Tauchen.Pnat_mid` |
| proof | Cell probabilities as differences of the counter-CDF `G`; `G` nonincreasing; tails telescope | `Tauchen.G`, `Tauchen.G_zero`, `Tauchen.G_n`, `Tauchen.Pnat_eq_G_sub`, `Tauchen.G_antitone`, `Tauchen.Pnat_nonneg`, `Tauchen.sum_Ico_Pnat`, `Tauchen.sum_filter_P` |
| Ex 3.1.12, p. 91 | `∑ⱼ P(xᵢ, xⱼ) = 1` | `Tauchen.sum_Pnat`, `Tauchen.isMarkov_P` |

## §3.2.1 Mathematical expectations (pp. 91–94)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.12)–(3.13), p. 92 | `(Ph)(x) = ∑ h(x')P(x, x')` | `mulVec_apply_eq` |
| (3.14), p. 92 | `(Pᵏh)(x) = ∑ h(x')Pᵏ(x, x')` | `pow_mulVec_apply_eq` |
| Ex 3.2.1, p. 92 | (i) constants are fixed points; (ii) `max |Ph| ≤ max |h|` | `IsMarkov.isFixedPt_const`, `IsMarkov.sup'_abs_mulVec_le`, `IsMarkov.norm_mulVec_le` |
| (3.15), pp. 92–93 | Law of iterated expectations `E[E_t h(X_{t+k})] = E h(X_{t+k})` | `iterated_expectations` |
| p. 93 | Monotone increasing Markov operators | `FOSD`, `MonotoneIncreasing` |
| Ex 3.2.2, p. 93 | Tauchen's `P` is monotone increasing when `ρ ≥ 0` | `Tauchen.sum_mul_nonneg_of_tails_nonneg`, `Tauchen.fosd_of_tails_le`, `Tauchen.monotoneIncreasing_P` |
| Ex 3.2.3, p. 93 | The two-state `P_w` is monotone increasing iff `α + β ≤ 1` | `monotoneIncreasing_two_state_iff` |
| Ex 3.2.4, p. 94 | Monotone increasing iff `P` preserves `iℝ^X` | `monotoneIncreasing_iff` |
| Ex 3.2.5, p. 94 | `Pᵗ` monotone increasing | `MonotoneIncreasing.pow` |

## §3.2.2 Geometric sums (pp. 94–97)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.16), (3.18), p. 94 | `v(x) = E_x ∑ βᵗh(Xₜ) = ∑ βᵗ(Pᵗh)(x)` | `lifetimeValue`, `lifetimeValue_eq_tsum_smul`, `IsMarkov.norm_smul_pow_mulVec_le`, `IsMarkov.summable_smul_pow_mulVec` |
| Lemma 3.2.1, (3.17), p. 94 | `β < 1 ⇒ I − βP` invertible and `v = ∑ (βP)ᵗh = (I − βP)⁻¹h` | `IsMarkov.one_sub_smul_mulVec_lifetimeValue`, `IsMarkov.isUnit_one_sub_smul`, `IsMarkov.lifetimeValue_eq_inv`, `IsMarkov.lifetimeValue_eq_add` |
| (3.19), p. 95 | Firm valuation with `β = 1/(1 + r)` | `firm_discount_mem`, `IsMarkov.firm_value` |
| Ex 3.2.6, p. 95 | `π ∈ iℝ^X`, `P` monotone `⇒ v` increasing | `isClosed_monotone`, `monotone_sum`, `IsMarkov.monotone_lifetimeValue` |
| (3.20)–(3.22), p. 96 | Consumption value `v = (I − βP)⁻¹(u ∘ c)`; CRRA utility | `IsMarkov.consumption_value`, `crra` |
| Ex 3.2.8, p. 96 | The CRRA value is increasing in `x` when `ρ ≥ 0` | `monotone_crra_exp`, `Tauchen.monotone_crra_value` |

## §3.3 Job search revisited (pp. 97–104)

| Book | Claim | Lean |
| --- | --- | --- |
| §3.3.1, p. 97 | Markov wages on finite `W ⊂ ℝ₊`, `c > 0`, `β ∈ (0, 1)`; `V = ℝ^W₊` | `MarkovJobSearch`, `MarkovJobSearch.V`, `MarkovJobSearch.isClosed_V`, `MarkovJobSearch.e` |
| (3.23), p. 97 | Bellman equation; Bellman operator `T` | `MarkovJobSearch.T`, `MarkovJobSearch.bellman_equation` |
| Ex 3.3.1, p. 98 | (i) `T` order-preserving self-map of `V`; (ii) contraction of modulus `β` | `MarkovJobSearch.T_mapsTo`, `MarkovJobSearch.T_monotone`, `MarkovJobSearch.abs_T_sub_le`, `MarkovJobSearch.isContractionOn_T` |
| p. 98 | `v*` is the unique fixed point in `V`; VFI converges | `MarkovJobSearch.vstar`, `MarkovJobSearch.vstar_mem`, `MarkovJobSearch.isFixedPt_vstar`, `MarkovJobSearch.eq_vstar_of_isFixedPt`, `MarkovJobSearch.tendsto_iterate_T`, `MarkovJobSearch.norm_iterate_T_sub_vstar_le` |
| p. 98 | `v`-greedy policies | `MarkovJobSearch.IsGreedy`, `MarkovJobSearch.isGreedy_vstar` |
| Lemma 3.3.1, p. 98 | `v*` increasing when `P` is monotone increasing | `MarkovJobSearch.monotone_vstar` |
| p. 100 | Continuation value `h* = c + βPv*`; `v* = e ∨ h*` | `MarkovJobSearch.hstar`, `MarkovJobSearch.hstar_mem`, `MarkovJobSearch.vstar_eq_max` |
| Ex 3.3.3, p. 100 | `h*(w) = c + β ∑ max{w'/(1 − β), h*(w')}P(w, w')` | `MarkovJobSearch.isFixedPt_hstar` |
| (3.24), Ex 3.3.4, p. 101 | `Q` is an order-preserving self-map of `V` and a `β`-contraction; `h*` its unique fixed point; iteration converges | `MarkovJobSearch.Q`, `MarkovJobSearch.Q_mapsTo`, `MarkovJobSearch.Q_monotone`, `MarkovJobSearch.isContractionOn_Q`, `MarkovJobSearch.eq_hstar_of_isFixedPt`, `MarkovJobSearch.tendsto_iterate_Q` |
| (3.25)–(3.26), p. 101 | Values with separation | `MarkovJobSearch.system_iff` |
| (3.27)–(3.28), p. 102 | `v_e* = (w + αβPv_u*)/(1 − β(1 − α))`; the operator of (3.28) | `MarkovJobSearch.denom_pos`, `MarkovJobSearch.employedValue`, `MarkovJobSearch.S`, `MarkovJobSearch.employed_recursion_iff` |
| Ex 3.3.5, p. 102 | Unique `v_u* ∈ V` solving (3.28); a convergent method | `MarkovJobSearch.sep_modulus_lt_one`, `MarkovJobSearch.S_mapsTo`, `MarkovJobSearch.isContractionOn_S`, `MarkovJobSearch.vuStar`, `MarkovJobSearch.isFixedPt_vuStar`, `MarkovJobSearch.eq_vuStar_of_isFixedPt`, `MarkovJobSearch.tendsto_iterate_S` |
| p. 102 | Unique solution `(v_u*, v_e*)` of (3.25)–(3.26) in `V × V`; `v_u* = s* ∨ h*_e` | `MarkovJobSearch.veStar`, `MarkovJobSearch.veStar_mem`, `MarkovJobSearch.system_unique`, `MarkovJobSearch.vuStar_eq_max` |
