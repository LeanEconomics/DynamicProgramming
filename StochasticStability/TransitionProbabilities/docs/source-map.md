# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 3, pp. 48–74. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.TransitionProbabilities`. Names marked "carried" are in the
modules copied from the Chapters 1–2 project `MarkovModels` (see the [README](../README.md)).
Where the Lean statement departs from the book, see [corrections](corrections.md).

## Chapter 3 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 48 | Two approaches to a Markov chain: from the sample paths, or from the probability laws | Not formalised (heuristic). Both are formalised: from the laws by Theorems 3.2.1 and 3.4.1, from the sample paths by `isMarkovChain_of_iid` and `isMarkovChain_of_regeneration` |
| p. 49 | Goals: the dynamics are determined by `P(x, A) = P(Φₙ ∈ A \| Φₙ₋₁ = x)`; the kernels of the models of Chapter 2; hitting times and the strong Markov property | Not formalised (outline); the one-step identity is `setLIntegral_succ` |

## §3.1 Defining a Markovian process

| Source | Claim | Lean |
| --- | --- | --- |
| p. 49 | `Φ` is a sequence of `X`-valued random variables; its paths lie in `Ω = X^∞` with the product σ-algebra; for each `x` a law `P_x` on `Ω` | `pathKernel` (the kernel `x ↦ P_x`), `isMarkovKernel_pathKernel`, `trajKernel`, `isMarkovKernel_trajKernel`; the coordinates `ω ↦ ω n` play `Φₙ` |
| p. 49 | "The initial condition requires, of course, that `P_x(Φ₀ = x) = 1`" | `pathKernel_map_zero` (the law of `Φ₀` under `P_x` is `δ_x`), `pathKernel_zero_mem` (`P_x(Φ₀ ∈ A) = 1_A(x)`), `ae_pathKernel_zero` (with measurable singletons); see [corrections](corrections.md) |
| p. 50 | `P(W ∈ A)` is used without naming the space on which `W` lives | Not formalised (notation). In Lean the noise lives on an explicit probability space (`IsIIDNoise`) |
| p. 50 | State space definitions: (i) countable, (ii) general (countably generated σ-algebra), (iii) topological (locally compact, separable, metrizable, Borel) | `IsCountableStateSpace`, `IsGeneralStateSpace`, `IsTopologicalStateSpace`; `IsCountableStateSpace.isGeneral`, `IsTopologicalStateSpace.isGeneral`. No result of the chapter uses them |
| pp. 50–51 | Why general spaces come before topological ones; one accessible atom often replaces a countable space | Not formalised (heuristic) |

## §3.2.1 The initial distribution and the transition matrix

| Source | Claim | Lean |
| --- | --- | --- |
| (3.1), p. 51 | `P_μ(Φ₀ = x₀) = μ(x₀)` and `P_μ(Φ ∈ A \| Φ₀ = x₀) = P_{x₀}(Φ ∈ A)` | `pathMeasure_map_zero`; `pathMeasure_inter_initial` (`P_μ(Φ ∈ B, Φ₀ = x₀) = μ(x₀) P_{x₀}(B)`); on a general space `pathMeasure_inter_zero` (`P_μ(B ∩ {Φ₀ ∈ C}) = ∫_C P_x(B) μ(dx)`) |
| (3.2)–(3.3), pp. 51–52 | Countable space Markov chain: `P_μ(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P_{x₀}(Φ₁ = x₁) ⋯ P_{xₙ₋₁}(Φ₁ = xₙ)`; time-homogeneity | `IsMarkovChain.fdd_points` (every Markov chain with a transition matrix satisfies (3.3)–(3.4)); the converse is not formalised. Only time-homogeneous chains are defined (`IsMarkovChain`) |
| (3.4)–(3.5), p. 52 | With `P(x, y) = P_x(Φ₁ = y)`, `P_μ(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯ P(xₙ₋₁, xₙ)`, equivalently `P_μ(Φₙ₊₁ = xₙ₊₁ \| Φₙ = xₙ, …, Φ₀ = x₀) = P(xₙ, xₙ₊₁)` | `theorem_3_2_1_fdd`, `cylFn_singletons`; `theorem_3_2_1` |
| p. 52 | Inhomogeneous chains are excluded | Not formalised (scope) |
| (3.6), p. 53 | Markov transition matrix: `P(x, y) ≥ 0`, `Σ_z P(x, z) = 1` | `IsTransitionMatrix` (entries in `[0, ∞]`); `matKernel`, `matKernel_singleton`, `matKernel_apply`, `isMarkovKernel_matKernel`, `lintegral_matKernel` |
| (3.7), p. 53 | `P⁰ = I`, `Pⁿ(x, z) = Σ_y P(x, y) Pⁿ⁻¹(y, z)` | `matPow`, `isTransitionMatrix_matPow`, `matKernel_pow_singleton` (the kernel powers are the matrix powers) |
| (3.8), p. 53 | `P_μ(Φₙ = y \| Φ₀ = x) = Pⁿ(x, y)`; `Pⁿ(x, A) = Σ_{y ∈ A} Pⁿ(x, y)` | `pathMeasure_initial_coord` (`P_μ(Φ₀ = x, Φₙ = y) = μ(x) Pⁿ(x, y)`), `matKernel_pow_apply`; on a general space `pathKernel_coord_mem`, `pathMeasure_map_coord`, `IsMarkovChain.map_eq` |

## §3.2.2 Developing Φ from the transition matrix

| Source | Claim | Lean |
| --- | --- | --- |
| p. 53 | `P_x(Φ₀ = x) = 1`, `P_x(Φ₁ = y) = P(x, y)`, `P_x(Φ₂ = z, Φ₁ = y) = P(x, y) P(y, z)`, …, consistent and extended to a law `P_x` on `Ω` | `pathKernel`, `theorem_3_2_1_fdd` with `μ = δ_x` (`pathMeasure_dirac`) |
| p. 53 | `P_μ(Φ ∈ A) := Σ_x μ(x) P_x(Φ ∈ A)`; (3.1) and (3.8) follow | `pathMeasure_eq_comp` (`P_μ = ∫ P_x μ(dx)`), `pathMeasure_inter_initial`, `pathMeasure_initial_coord` |
| Theorem 3.2.1, p. 54 | For an initial measure `μ` and a transition matrix `P` there is a Markov chain with `P_μ(Φₙ₊₁ = y \| Φₙ = x, …, Φ₀ = x₀) = P(x, y)` | `theorem_3_2_1` (when the conditioning event has positive probability), with `theorem_3_4_1` for the existence of the chain |

## §3.3.1 The forward and backward recurrence time chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 54 | `V⁺(n) = inf(Z_m − n : Z_m > n)`; from `k > 1` to `k − 1`, from `1` renewed with law `p`; the sub-diagonal matrix | `fwdRecMatrix` (state `k` stands for `V⁺ = k + 1`), `isTransitionMatrix_fwdRecMatrix`; the pathwise dynamics: `fwdTime`, `fwdTime_succ_of_one_lt`, `fwdTime_succ_of_eq_one` (carried) |
| (3.9), p. 54 | `p̄(n) = Σ_{j ≥ n+1} p(j)` | `ptail`, `ptail_eq` |
| p. 55 | `M = sup(m ≥ 1 : p(m) > 0)`; the state space is `{0, …, M − 1}` if `M < ∞`, `ℤ₊` otherwise | `ptail_ne_zero_iff` (`p̄(x) ≠ 0` iff `x < M`), `ptail_ne_zero_of_bwdRecMatrix` (this set is closed for `V⁻`) |
| (3.10), p. 55 | `P(x, x + 1) = p̄(x + 1)/p̄(x)`, `P(x, 0) = p(x + 1)/p̄(x)`, zero otherwise | `bwdRecMatrix`, `bwdRecMatrix_rowSum` (rows sum to one where `0 < p̄(x) < ∞`), `bwdRecMatrix_zero` (`P(x, 0) = b(x)`) |
| p. 55 | The superdiagonal matrix with rows `b(1), 1 − b(1)`; `b(2), 0, 1 − b(2)`; …, `b(j) = p(j + 1)/p̄(j)` | `bwdRecMatrix_display_counterexample`, with `halfHalf`; see [corrections](corrections.md) |
| p. 55 | These chains are a source of stable and unstable behaviour | Not formalised (heuristic) |

## §3.3.2 Random walk models

| Source | Claim | Lean |
| --- | --- | --- |
| (3.11), p. 55 | Random walk on `ℤ`: `P(x, y) = P(W₁ = y − x) = Γ(y − x)` | `rwMatrix`, `isTransitionMatrix_rwMatrix`, `rw_step_law`; from the recursion: `matKernel_rwMatrix`, `randomWalkInt_isMarkovChain` |
| p. 55 | The transition probabilities are translation invariant | `rwMatrix_translate` |
| (3.12)–(3.14), pp. 55–56 | Random walk on `ℤ₊`, `Φₙ = [Φₙ₋₁ + Wₙ]⁺`: `P(x, y) = Γ(y − x)` for `y > 0`, `P(x, 0) = Γ(−∞, −x]` | `rwhlMatrix`, `isTransitionMatrix_rwhlMatrix`; from the recursion: `matKernel_rwhlMatrix`, `rwhl_isMarkovChain`, with `reflectedWalkKernel` (carried) |
| p. 56 | The storage model with `r = 1` and integer inputs and inter-input times is random walk on `ℤ₊` | On `ℝ≥0`: `storageKernel_eq_halfLineWalk` (carried) |
| p. 56 | `Γ(x) = P(Sₙ − Jₙ = x) = Σ_{i ≥ 0} H(i) G(x + i)` | `storage_increment_singleton` (`Σᵢ H(i) G(i − x)`), `storage_increment_counterexample`; see [corrections](corrections.md) |

## §3.3.3 Embedded queueing models

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 3.3.1, p. 56 | GI/M/1: `N` is a Markov chain on `ℤ₊` with the matrix of rows `(qⱼ, pⱼ, …, p₀)`, `qⱼ = Σ_{i ≥ j+1} pᵢ`; hence a random walk on a half line | `proposition_3_3_1` (a transition matrix, equal to `rwhlMatrix` with `Γ(k) = p_{1−k}`); `giM1Matrix`, `giM1Increment`, `giM1Matrix_eq_rwhl`, `tsum_giM1Increment`; the chain: `proposition_3_3_1_of_recursion`, `proposition_3_3_1_derived`, `matKernel_giM1Matrix` |
| (3.14)–(3.15), p. 56 | `p₀ = P(S > T) = ∫ e^{−μt} G(dt)`, `pⱼ = ∫ e^{−μt}(μt)ʲ/j! G(dt)` | `poissonWeight`, `poissonWeight_eq`, `tsum_poissonWeight`; as probabilities of service counts: `eq_3_14`, `eq_3_15` |
| (3.16), p. 57 | `Nₙ₊₁` rises by at most one | `giM1Kernel_apply_up` (carried) |
| (3.17), p. 57 | `P(Nₙ₊₁ = j + 1 \| Nₙ = j, …) = ∫ e^{−μt} G(dt) = p₀` | `eq_3_14`; the memoryless property: `expMeasure_memoryless`, `expMeasure_prod_lt` (carried) |
| p. 57 | For `0 < i ≤ j`, `Nₙ₊₁ = i` when exactly `j − i + 1` services are completed | `giM1Kernel_apply_le` (carried), `matKernel_giM1Matrix` |
| (3.18), p. 57 | The number of exponential services completed in `[0, t]` is Poisson with parameter `μt` (cited from Çinlar) | `eq_3_18` (proved), with `countEvent`, `poissonCount`, `lintegral_poissonCount`; the printed form: `eq_3_18_counterexample`; see [corrections](corrections.md) |
| p. 57 | `P(j, 0) = qⱼ`: the queue empties if more than `j + 1` customers complete service | `giM1Matrix`, `giM1Kernel_apply_zero` (carried), `measure_Ici_succ_eq_tsum` |
| p. 57 | The chain is built from `P` by Theorem 3.2.1 | `theorem_3_2_1`, with `proposition_3_3_1` |
| Proposition 3.3.2, (3.19), pp. 57–58 | M/G/1: `N*` is a Markov chain on `ℤ₊` with rows `(q₀, q₁, …)`, `(q₀, q₁, …)`, `(0, q₀, …)`, …, `qⱼ = ∫ e^{−λt}(λt)ʲ/j! H(dt)` | `proposition_3_3_2`, `mG1Matrix`, `isTransitionMatrix_mG1Matrix`; `eq_3_19`; the chain: `proposition_3_3_2_of_recursion`, `proposition_3_3_2_derived`, `matKernel_mG1Matrix`. On the range of `j`, see [corrections](corrections.md) |
| p. 58 | `N*` is similar to random walk on a half line, with a different modification away from zero | Not formalised (comparison); the kernel is `mG1Kernel` (carried) |

## §3.3.4 Linear models on the rationals

| Source | Claim | Lean |
| --- | --- | --- |
| p. 58 | For AR(1), the Markovian nature is immediate | On `ℝ`: `ar1_isMarkovChain`, with `ar1Kernel` (carried) |
| Proposition 3.3.3, pp. 58–59 | For `α ∈ ℚ` and noise on `ℚ`, `X` is a Markov chain on `ℚ` with `P(r, q) = Γ(q − αr)` | `proposition_3_3_3`, `arMatrix`; the chain: `proposition_3_3_3_of_recursion`, `matKernel_arMatrix` |
| p. 59 | The countable structure is unnatural for this model | Not formalised (heuristic) |

## §3.4.1 Developing Φ from transition probabilities

| Source | Claim | Lean |
| --- | --- | --- |
| p. 59 | `B(X)` is countably generated | Not assumed (see [corrections](corrections.md)) |
| p. 59 | Transition probability kernel: `P(·, A)` measurable, `P(x, ·)` a probability | A Markov kernel `P : Kernel X X` (Mathlib) |
| pp. 59–60 | Substochastic kernels, `T(x, X) ≤ 1`; general kernels | `IsSubstochasticKernel`, `isSubstochasticKernel_of_markov`; a general kernel is a `Kernel X X` |
| p. 60 | The finite-dimensional set functions `Pⁿ_x(A₁ × ⋯ × Aₙ) = ∫_{A₁} P(x, dy₁) ⋯ P(yₙ₋₁, Aₙ)` | `cylFn`, `measurable_cylFn`, `boxSet`, `measurableSet_boxSet`, `pathKernel_boxSet` |
| Theorem 3.4.1, (3.20), p. 60 | For every initial measure `μ` and kernel `P` there is a process `Φ` on `Ω` and a law `P_μ` with the finite-dimensional distributions (3.20) | `theorem_3_4_1`, `pathMeasure_boxSet`, `isProbabilityMeasure_pathMeasure`; uniqueness: `theorem_3_4_1_unique`, with `generateFrom_boxSets`, `isPiSystem_boxSets` |
| p. 60 | Proof: consistency and extension, by Revuz or by Kolmogorov's theorem on a topological space | By the Ionescu-Tulcea theorem in Mathlib, with no condition on `X` |
| p. 61 | Markov chain on a general space: the finite-dimensional distributions satisfy (3.20) | `IsMarkovChain` (`IsMarkovChain.mk`, `IsMarkovChain.measurable`, `IsMarkovChain.fdd`); every such chain has law `P_μ`: `law_eq_pathMeasure` |

## §3.4.2 The n-step transition probability kernel

| Source | Claim | Lean |
| --- | --- | --- |
| (3.21)–(3.22), p. 61 | `P⁰(x, A) = δ_x(A)`, `Pⁿ(x, A) = ∫ P(x, dy) Pⁿ⁻¹(y, A)` | `pow_zero_apply`, `pow_succ_apply`, `pow_succ_apply'`, `isMarkovKernel_pow` |
| Theorem 3.4.2, (3.23), p. 61 | Chapman–Kolmogorov: `Pⁿ(x, A) = ∫ Pᵐ(x, dy) Pⁿ⁻ᵐ(y, A)` | `theorem_3_4_2` |
| (3.24), p. 61 | `P_x(Φₙ ∈ A) = ∫ P_x(Φₘ ∈ dy) P_y(Φₙ₋ₘ ∈ A)` | `pathKernel_coord_chapmanKolmogorov`, with `pathKernel_map_coord`, `pathKernel_coord_mem` |
| (3.25), pp. 61–62 | The `m`-skeleton `Φᵐ` is a Markov chain with `P_x(Φᵐₙ ∈ A) = Pᵐⁿ(x, A)` | `skeleton`, `skeleton_pow`, `skeleton_isMarkovChain` (with `skeletonFilt`, `isMarkovChain_of_step`) |
| (3.26), p. 62 | The resolvent `K_{a_ε} = (1 − ε) Σᵢ εⁱ Pⁱ` | `resolvent`, `resolvent_apply`, `tsum_geometric_weights`, `isMarkovKernel_resolvent`; the sampled kernels `K_a`: `sampledKernel`, `sampledKernel_apply`, `isMarkovKernel_sampledKernel` |
| p. 62 | `Pⁿ` acts on functions, `Pⁿf(x) = ∫ Pⁿ(x, dy) f(y)`, and on measures, `μPⁿ(A) = ∫ μ(dx) Pⁿ(x, A)` | `kfun`, `measurable_kfun`, `kfun_indicator`, `kfun_one`, `kfun_mono`, `kfun_add`, `kfun_const_mul`, `kfun_comp`, `kfun_pow_succ`; `kfunR`, `measurable_kfunR`, `abs_kfunR_le`; `measure_kernel_apply`, `measure_kernel_assoc`, `isProbabilityMeasure_measure_kernel`, `dirac_kernel`, `lintegral_kfun` |
| p. 62 | `P^{m+n} = PᵐPⁿ` | `pow_add_eq` |
| p. 62 | `E_μ` is defined on cylinder sets and extended by linearity | Not formalised (notation): `E_μ` is the Lebesgue or Bochner integral against `pathMeasure P μ` |
| Proposition 3.4.3, (3.27), p. 63 | `E_μ[h(Φₙ₊₁, Φₙ₊₂, …) \| Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]` for bounded measurable `h` | `proposition_3_4_3` |
| p. 63 | `𝓕ₙ^Φ = σ(Φ₀, …, Φₙ)` | `natFilt`, `measurable_coord_natFilt`, `measurableSet_coord_natFilt`, `adapted_coord` |
| p. 63 | The shift `θ`, `θᵏ`, `θᵏH = h(Φₖ, Φₖ₊₁, …)` | `shift`, `measurable_shift`, `shift_zero`, `shift_shift`, `shift_apply` |
| (3.28), p. 63 | `E_μ[θⁿH \| 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for bounded measurable `h` | `markov_property` (every `H` with `θⁿH` integrable), `markov_property_bdd`; with `stronglyMeasurable_expect_coord`, `integrable_expect_coord`, `integrable_shift_of_bdd`. Other forms: `markov_measure`, `markov_lintegral`, `markov_lintegral_mul`, `markov_lintegral_univ`, `markov_setIntegral`, `setLIntegral_succ`, `measure_inter_shift_box` |
| p. 63 | `𝓕ₙ^Φ` need not be complete; "`A` occurs `P_μ`-a.s."; `P_*`-a.s. | Not formalised (notation); almost-sure statements are with respect to `pathMeasure P μ` |

## §3.4.3 Occupation, hitting and stopping times

| Source | Claim | Lean |
| --- | --- | --- |
| p. 64 | The occupation time `η_A = Σ_{n ≥ 1} 1{Φₙ ∈ A}`; `τ_A = min{n ≥ 1 : Φₙ ∈ A}`, `σ_A = min{n ≥ 0 : Φₙ ∈ A}`, measurable | `occTime`, `firstReturn`, `firstHit`, `measurable_occTime`, `measurableSet_firstReturn_eq`, `measurableSet_firstReturn_ne_top`, `measurableSet_le_firstReturn`; `one_le_firstReturn`, `le_firstReturn_iff`, `firstReturn_eq_iff`, `le_firstReturn_succ_iff`, `firstHit_eq_zero_iff`, `firstHit_eq_firstReturn` |
| (3.29), p. 64 | `τ_A(1) = τ_A`, `τ_A(k) = min{n > τ_A(k − 1) : Φₙ ∈ A}` | `returnTimeK`, `returnTimeK_one`, `returnTimeK_succ_of_eq`, `returnTimeK_succ_of_top` |
| (3.30), p. 64 | `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A) = E_x[η_A]` | `potKernel`, `potKernel_apply`, `potKernel_eq_lintegral_occTime` |
| (3.31), p. 64 | `L(x, A) = P_x(τ_A < ∞) = P_x(Φ ever enters A)` | `hitProb`, `firstReturn_ne_top_iff`, `measurable_hitProb` |
| p. 65 | A stopping time: `{ζ = n} ∈ 𝓕ₙ^Φ` for all `n` | Mathlib's stopping times for `natFilt` |
| Proposition 3.4.4, p. 65 | `τ_A` and `σ_A` are stopping times | `proposition_3_4_4`; all `τ_A(k)`: `isStoppingTime_returnTimeK` |
| Proposition 3.4.5, p. 65 | (i) `P_x(τ_A = 1) = P(x, A)`, `P_x(τ_A = n) = ∫_{Aᶜ} P(x, dy) P_y(τ_A = n − 1)`, and the nested integral; (ii) `P_x(σ_A = 0) = 1_A(x)`, `P_x(σ_A = n) = P_x(τ_A = n)` for `x ∈ Aᶜ` | `proposition_3_4_5_i`, `proposition_3_4_5_i_succ`, `nestedTaboo`, `firstReturn_eq_nestedTaboo`, `proposition_3_4_5_ii`; with `pathKernel_first_step` |
| p. 66 | `I_B(x, A) = 1_{A ∩ B}(x)`; `P_x(τ_A = k) = [(P I_{Aᶜ})^{k−1} P](x, A)` | `indKernel`, `indKernel_apply`, `comp_indKernel_apply`, `comp_indKernel_eq_restrict`, `isSubstochasticKernel_comp_indKernel`; `tabooKernel`, `tabooKernel_zero`, `tabooKernel_succ_apply`, `firstReturn_eq_tabooKernel` |
| p. 66 | `L(x, A) = Σ_{k ≥ 1} [(P I_{Aᶜ})^{k−1} P](x, A)` | `hitProb_eq_tsum`; the first-step equation `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`: `hitProb_first_step` |
| p. 66 | `Φ_ζ = Φₙ` on `{ζ = n}`; `𝓕_ζ^Φ = {A : {ζ = n} ∩ A ∈ 𝓕ₙ^Φ}`; `θ^ζ H = h(Φ_ζ, Φ_{ζ+1}, …)` on `{ζ < ∞}` | `stoppedState`, `stoppedState_of_eq`, `measurable_stoppedState`; `measurableSet_stoppedField_iff`, `measurableSet_stoppedField_ne_top`, `measurableSet_ne_top`, `iSup_natFilt`; `shiftAt`, `shiftAt_of_eq`, `measurable_shiftAt`; `measurable_of_stopping_pieces`, `measurable_stoppedField_indicator` |
| (3.32), p. 66 | Strong Markov property: `E_μ[θ^ζH \| 𝓕_ζ^Φ] = E_{Φ_ζ}[H]` a.s. on `{ζ < ∞}`, for bounded measurable `h` | `strong_markov_property` (as an identity of `1_{ζ<∞}`-weighted functions, for every `H` with `1_{ζ<∞} θ^ζH` integrable), `StrongMarkovProperty`; other forms: `strong_markov_measure`, `strong_markov_lintegral`, `strong_markov_lintegral_mul`, `strong_markov_setIntegral`. See [corrections](corrections.md) |
| Proposition 3.4.6, p. 66 | A Markov chain in discrete time always has the strong Markov property | `proposition_3_4_6` |
| p. 66 | Proof: decompose over `{ζ = n}` and use (3.28) at each `n` | As in the book: `inter_ne_top_eq_iUnion`, `pairwise_disjoint_inter_eq`, `setOf_le_eq_biUnion`, `setOf_ne_top_eq_iUnion`, with `markov_lintegral`, `markov_setIntegral` |
| p. 67 | Taboo probabilities `_APⁿ(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)`; `_AP¹ = P`; (3.33); `_APⁿ = (P I_{Aᶜ})^{n−1} P` | `tabooProb`, `tabooProb_one`, `tabooProb_succ`, `tabooProb_eq_tabooKernel`, `firstReturn_eq_tabooProb` |
| (3.34), p. 67 | `U_A = Σ_{n ≥ 1} _APⁿ`, with `U_A(x, A) = L(x, A)` | `tabooPotKernel`, `tabooPotKernel_apply`, `tabooPotKernel_self` |

## §3.5.1 Random walk on a half line

| Source | Claim | Lean |
| --- | --- | --- |
| (3.35), p. 67 | For `A ⊆ (0, ∞)`, `P(x, A) = Γ(A − x)` | `eq_3_35` (on `ℝ≥0`, with `0 ∉ A`), with `halfLineWalkKernel` (carried); on `ℝ`: `randomWalkKernel_apply_image` |
| (3.36), p. 67 | `P(x, {0}) = Γ(−∞, −x]` | `eq_3_36` |
| p. 67 | The walk is a Markov chain with this kernel | `halfLineWalk_isMarkovChain`; random walk on `ℝ`: `randomWalkReal_isMarkovChain` |

## §3.5.2 Storage and queueing models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 68 | The Moran dam with release rate `r > 0` is random walk on a half line | `storage_isMarkovChain`, with `storageKernel`, `storageKernel_eq_halfLineWalk` (carried) |
| (3.37), p. 68 | `Γ(A) = P(Sₙ − Jₙ ∈ A) = ∫ G(A/r + y/r) H(dy)` | `eq_3_37` (`∫ G{t : y − rt ∈ A} H(dy)`), `eq_3_37_div` (`∫ G((y − A)/r) H(dy)` for `r > 0`), `eq_3_37_counterexample`; see [corrections](corrections.md) |
| p. 68 | The same law serves inventories, insurance and the residual service of a GI/G/1 queue | The GI/G/1 waiting time chain: `waitingTime_isMarkovChain`, with `waitingTimeKernel`, `storageKernel_one` (carried); the other models are not formalised |

## §3.5.3 Renewal processes and related chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 68 | The delayed renewal process `Zₙ = Y₀ + ⋯ + Yₙ`, `Y₀ ∼ Γ₀`, `Y₁, Y₂, … ∼ Γ` on `ℝ₊` | `renewalReal_isMarkovChain`, `renewalReal_map_eq` |
| (3.38), p. 68 | `Γ₀ ∗ Γ(dt) = ∫ Γ(dt − s) Γ₀(ds) = ∫ Γ₀(dt − s) Γ(ds)` | `eq_3_38`, `conv_apply_eq_lintegral`, `image_sub_const_eq_setOf` |
| p. 68 | `P(Zₙ ∈ dt) = Γ₀ ∗ Γ^{n∗}(dt)` | `renewalReal_map_eq`; `convPow` (carried), `isProbabilityMeasure_convPow` |
| p. 69 | The renewal measure `U = Σₙ Γ^{n∗}`; `U[0, t] = E₀[number of renewals in [0, t]]`, `Γ₀ ∗ U[0, t] = E_{Γ₀}[⋯]` | `renewalMeasure`, `sFinite_renewalMeasure`, `renewal_expected_count_undelayed`, `renewal_expected_count` (for every measurable set) |
| p. 69 | `Zₙ` is a random walk, `P(x, A) = Γ(A − x)`, and moves to infinity | `renewalReal_isMarkovChain`; the divergence of the partial sums of i.i.d. nonnegative variables not concentrated at `0`: `tendsto_partialSum_atTop_ae` (stated for service times) |
| (RT3)–(RT4), p. 69 | The forward and backward recurrence time processes `V⁺(t)`, `V⁻(t)` and their `δ`-skeletons | `fwdTimeCts`, `bwdTimeCts`, `fwdSkeleton`, `bwdSkeleton` (carried); on the canonical space: `fwdSkel`, `measurable_fwdSkel`, `bwdSkel`, `measurable_bwdSkel`, `measurable_fwdTimeCts`, `measurable_bwdTimeCts` |
| p. 69 | The recurrence time chains grow, diminish and grow again | Not formalised (heuristic) |
| p. 69 | "No matter what the structure of the renewal sequence", `V⁺_δ` and `V⁻_δ` are Markovian | `fwdSkeleton_isMarkovChain`, `fwdSkeleton_isMarkovChain_delayed`, `fwdSkeleton_isMarkovChain_undelayed`, `bwdSkeleton_isMarkovChain`, for `Γ` on `[0, ∞)` not concentrated at `0`; the backward skeleton starts at age `0`. The proofs regenerate the renewal sequence: `fwdSkel_succ`, `bwdSkel_succ`, `fwdIndex`, `bwdIndex`, `bwdIndex_spec`, `bwdSkel_eq`, with `isMarkovChain_of_regeneration` |
| p. 69 | For `x > δ`, `P^δ(x, {x − δ}) = 1` | `fwdSkelKernel_of_lt`; pathwise: `fwdTimeCts_add_of_lt`, `fwdTimeCts_set_eq`, `fwdSkeleton_succ_of_lt` |
| (3.39), p. 70 | For `x ≤ δ`, `P^δ(x, A) = ∫_0^{δ−x} Σₙ Γ^{n∗}(dt) Γ(A − [δ − x] − t) = ∫_0^{δ−x} U(dt) Γ(A − [δ − x] − t)` | `eq_3_39` (for `A ⊆ (0, ∞)`, equal to `eq_3_39_corrected`), with `fwdSkelKernel`, `indicator_fwdTimeCts_eq_tsum`, `lintegral_partialSum_pair`; the printed form: `eq_3_39_printed`, `eq_3_39_counterexample`; see [corrections](corrections.md) |
| p. 70 | `P(V⁻(nδ) = x + δ \| V⁻((n − 1)δ) = x) = Γ(x + δ, ∞)/Γ(x, ∞)` | `bwdSkelKernel_apply_add`, with `bwdSkelKernel`; pathwise: `bwdTimeCts_add_of_no_renewal`, `bwdSkelStep_of_gt` |
| p. 70 | For `dv ⊂ [0, δ]`, `P(V⁻(nδ) ∈ dv \| V⁻((n − 1)δ) = x) = ∫_x^{x+δ} Γ(du) U(dv − (u − x) − δ) Γ(v, ∞)/[Γ(x, ∞)]⁻¹` | `bwdSkelKernel_apply_of_subset` (for `A ⊆ [0, δ)`), with `bwdInner`, `bwd_inner`, `bwdSkelStep_split`; the printed normalisation: `bwd_display_counterexample`, with `halfOneTwo`; see [corrections](corrections.md) |

## §3.5.4 Ladder chains and the GI/G/1 queue

| Source | Claim | Lean |
| --- | --- | --- |
| p. 70 | Without exponential assumptions the queue length at arrivals or departures is not Markovian | Not formalised as a statement about `N`; for a non-exponential service law the conditional probabilities of (2.30) differ: `dirac_not_memoryless` (carried) |
| (3.40), p. 70 | The ladder chain on `ℤ₊ × ℝ`: `P(i, x; j × A) = 0` for `j > i + 1`, `Λ_{i−j+1}(x, A)` for `j = 1, …, i + 1`, `Λ*ᵢ(x, A)` for `j = 0`, with substochastic `Λᵢ`, `Λ*ᵢ` | `ladderRow`, `ladderKernel`, `ladderKernel_apply`, `ladderRow_apply_prod`, `eq_3_40_zero`, `eq_3_40_mid`, `eq_3_40_up`; a Markov kernel when every row has mass one: `isMarkovKernel_ladderKernel` |
| p. 71 | Translation invariance and the skip-free structure; the matrix display with entries `Λ*ᵢ`, `Λᵢ` | `ladderKernel_translate`, `eq_3_40_up`. On the label "(3.41)", see [corrections](corrections.md) |
| p. 71 | `Φₙ = (Nₙ, Rₙ)`, `Nₙ` the number of customers at `Tₙ−`, `Rₙ` the "total residual service time in the system at `Tₙ+`" | `queueN`, `queueR` (the residual service of the customer in service), with `arrT`, `depT`, `inService`; see [corrections](corrections.md) |
| p. 71 | The service renewal process `Z₁, Z₂, …` and its forward recurrence time `R_t`, with `Z₁ = x` when `R₀ = x` | `resEpoch`, `measurable_resEpoch`, `resEpoch_mono`, `resEpoch_succ_eq`, `numDone`, `numDone_eq_iff` |
| (3.41), p. 71 | `Pⁿₜ(x, y) = P(Zₙ ≤ t < Zₙ₊₁, R_t ≤ y \| R₀ = x)` | `ladderP`, `gig1Set`, `measurableSet_gig1Set` |
| (3.42), p. 71 | `Λₙ(x, [0, y]) = ∫ Pⁿₜ(x, y) G(dt)` | `gig1Lambda`, `gig1LambdaMeasure`, `gig1LambdaMeasure_apply`, `eq_3_42` |
| (3.43), p. 71 | `Λ*ₙ(x, [0, y]) = [Σ_{j ≥ n+1} Λⱼ(x, [0, ∞))] H[0, y]` | `gig1LambdaStar`, `eq_3_43` |
| p. 71 | The kernels are substochastic, and together they give the ladder kernel of `Φ` | `gig1Ladder`, `gig1Ladder_rowSum`, `isMarkovKernel_gig1Ladder`; the rows have mass one: `gig1Lambda_tsum_univ`, `isMarkovKernel_gig1Ladder_of_pos` |
| p. 71 | "It is easy to verify that the chain `Φ` has the form (3.41)" with these kernels | `gig1_isMarkovChain`, from `gig1_step_eq` (the pathwise recursion), `depT_chain`, `gig1Ladder_eq_map` (the law of one step) and `gig1_law_past_future` (the future at an arrival is independent of the past), with `isMarkovChain_of_regeneration` |

## §3.5.5 State space models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 72 | For SNSS(F), `Ph(x) = E[h(Xₙ₊₁) \| Xₙ = x] = ∫ h(F(x, w)) Γ(dw)` for bounded measurable `h` | `kfun_recursionKernel` (`h ≥ 0`), `kfunR_recursionKernel` (real measurable `h`), with `recursionKernel` (carried) |
| p. 72 | `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)` | `recursionKernel_eq_lintegral_indicator` |
| p. 72 | "Since `{Wₙ}` is assumed i.i.d. in (SNSS2)": the recursion is a Markov chain with this kernel | `isMarkovChain_of_iid`, with `IsIIDNoise`, `IsIIDNoise.map_eq`; `isMarkovChain_of_recursion`, `isMarkovChain_canonPath` (on the canonical space, with `canonPath`, `histFilt`, `canon_step`, `law_hist_next`) |
| p. 72 | The maps `F₀(x) = x`, `F_{k+1}(x₀, w₁, …, w_{k+1}) = F(Fₖ(x₀, w₁, …, wₖ), w_{k+1})`; `Xₖ = Fₖ(x₀, W₁, …, Wₖ)` | `controlMap`, `controlMap_zero`, `controlMap_succ` (carried); `recursion_eq_controlMap` |
| (3.44), p. 72 | `Pᵏ(x, A) = ∫ ⋯ ∫ 1{Fₖ(x, w₁, …, wₖ) ∈ A} Γ(dw₁) ⋯ Γ(dwₖ)` | `eq_3_44`; the iterated form `recursionKernel_pow_succ_apply`; the law of the path: `recursionKernel_pow_apply`, `law_orbit` (carried) |

## §3.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| p. 72 | "The one real assumption in the general case is that the σ-field `B(X)` is countably generated" | Not needed anywhere (see [corrections](corrections.md)) |
| pp. 72–74 | Chapman–Kolmogorov and semigroups; operator-theoretic approaches; topological spaces; notation for hitting times; the strong Markov property; references for queues, storage and control | Not formalised (commentary) |

## Supporting results without a source in the text

| Source | Claim | Lean |
| --- | --- | --- |
| — | Regeneration of an i.i.d. sequence at a random index | `truncSeq`, `tailSeq`, `indepFun_truncSeq_tailSeq`, `infinitePi_map_tailSeq`, `infinitePi_map_trunc_tail`, `iIndep_coords`, `lintegral_regeneration`, `lintegral_cond_eq`, `mul_lintegral_cond`, `pastFilt`, `isMarkovChain_of_regeneration` |
| — | A process whose one-step conditional laws are given by a kernel is a Markov chain | `isMarkovChain_of_step` |
| — | The Markov property as an identity of measures on path space | `markov_measure`, `strong_markov_measure`, `integral_measure_comp` |
