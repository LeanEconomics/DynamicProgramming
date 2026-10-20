# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 6, pp. 131–161. Lean names are relative to
`StokeyLucasPrescott.DeterministicDynamics`. Where the Lean statement departs from the book, see
[corrections](corrections.md).

## Carried over from Chapters 3–5

| Source | Claim | Lean |
| --- | --- | --- |
| Chapter 3 | Theorem 3.2 and corollaries, hemi-continuity, the Theorem of the Maximum, interior points | `Contraction`, `Correspondences`, `Maximum`, `InteriorPoints` |
| Chapter 4 | Lemma 4.1, Theorems 4.2–4.11 and 4.15, sufficient conditions for Assumption 4.2 | `ExtendedReals`, `Principle`, `Assumption42`, `BoundedReturns`, `Concavity`, `Envelope`, `ValueDifferentiability`, `EulerEquations` (see the [Chapter 4 source map](../../DeterministicDP/docs/source-map.md)) |
| Chapter 5 | Exercises 5.1, 5.9 and 5.11–5.12 | `OneSectorGrowth`, `WeakConcavity`, `GrowthDifferentiability`, `GrowthDiscount`, `ConvexInvestment`, `AdjustmentCosts`, `RecursivePreferences`, `ConsumerRecursive` (see the [Chapter 5 source map](../../DeterministicApplications/docs/source-map.md)) |

## §6.1 The one-sector model of optimal growth

| Source | Claim | Lean |
| --- | --- | --- |
| §6.1 | The setting: Exercise 5.1 with an Inada condition, `k̄`, and the unique solution `v` of (1) | `GrowthDyn`, `exists_kbar`, `growthHyp_kbar`, `Setting61`, `exists_setting61`, `gpol`, `gpol_of_mem`, `gpol_mem`, `gpol_zero`, `gpol_interior`, `gpol_lt_kbar`, `continuousOn_gpol`, `strictConcaveOn_liftR`, `strictConcave_v` |
| Ex 6.1a | Interior maxima; `v` is `C¹` on `(0, k̄)` with (3); the Euler equation (2) | `hasDerivAt_v`, `foc`, `ex_6_1a` |
| Ex 6.1b | `g` strictly increasing | `ex_6_1b` |
| Proposition, p. 136 | Stationary points `0` and `k*`; monotone convergence to `k*` from every `k₀ > 0` | `exists_kstar`, `fixed_iff`, `prop_6_1` |
| Ex 6.2 | The Cobb–Douglas problem: interior, unique maximizers; `v′` and the first-order condition | `CDValue`, `CDValue.argmax_pos`, `argmax_lt_one`, `argmax_unique`, `hasDerivAt_V`, `foc`, `ex_6_2`, `cdValue_of_fixed`, `ex_6_2_fixed` |

## §6.2 Global stability: Liapounov functions

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 6.1, p. 138 | Boldrin and Montrucchio: every `C²` map of a compact interval is an optimal policy | `bmF`, `bmK`, `bmF_gap`, `bm_gap_ge`, `bmFs`, `bm_assumption43`, `bm_assumption44`, `bm_assumption47`, `bm_assumption48`, `bm_assumption49`, `bmV`, `bm_obj`, `bellman_bm`, `theorem_6_1` |
| Ex 6.3 | The logistic map `g(x) = 4x(1 − x)`: stationary points, `g²`, a two-cycle and a three-cycle | `logistic`, `ex_6_3a`, `ex_6_3b_values`, `ex_6_3b_two_cycle`, `logistic_sin_sq`, `ex_6_3b_three_cycle` |
| Lemma 6.2, p. 140 | A Liapounov function gives global stability | `lemma_6_2`, `lemma_6_2_book`, `globally_stable` |
| (6)–(8), pp. 140–142 | The value loss `L(x) = (x − x̄)(v′(x) − v′(x̄))` and conditions under which it is a Liapounov function | `valueLoss`, `valueLoss_nonpos`, `LossFacts`, `valueLoss_beta_one`, `valueLoss_of_eight`, `valueLoss_of_eight_strict` |
| Ex 6.4, p. 143 | The quadratic case: when (8) holds; uniqueness of the stationary point | `ex_6_4_form`, `ex_6_4`, `ex_6_4_book_condition_fails`, `ex_6_4_stationary`, `ex_6_4_not_unique`, `ex_6_4_unique_of_eight` |

## §6.3 Linear systems and linear approximations

| Source | Claim | Lean |
| --- | --- | --- |
| §6.3 | Stable and unstable subspaces of `A` | `stableSubspace`, `unstableSubspace`, `convSubspace`, `tendsto_of_mem_maxGenEigenspace`, `not_tendsto_of_eigen`, `stable_sup_unstable`, `disjoint_stable_unstable`, `tendsto_iff_mem_stable`, `stable_eq_top`, `cplx`, `cplxEnd`, `hasEigenvalue_cplxEnd_iff` |
| Theorem 6.3, p. 145 | `x_t → x̄` from every `x₀` iff every root of `A` is inside the unit circle | `deviation_eq`, `theorem_6_3` |
| Theorem 6.4, p. 146 | The stable initial conditions of a triangularized system | `triangular_step`, `triangular_invariant`, `triangular_tendsto_iff`, `solution_eq`, `theorem_6_4` |
| Theorem 6.5, p. 147 | Local stability of `x_{t+1} = h(x_t)` from the roots of `Dh(x̄)` | `matCLM`, `tendsto_opNorm_pow`, `theorem_6_5` |
| Theorem 6.6, p. 147 | The local stable manifold | `theorem_6_6`, `local_stable_family`, with the three rows below |
| — | Real stable and unstable subspaces, by conjugation closure | `conjV`, `conjV_mem_maxGenEigenspace`, `stableR`, `unstableR`, `mem_stableR_iff`, `isCompl_stableR_unstableR`, `finrank_stableR`, `unstableR_ker` |
| — | The exponential dichotomy | `projS`, `projU`, `stable_bound`, `shiftM`, `invB`, `isUnit_shift`, `unstable_bound` |
| — | The Lyapunov–Perron fixed point | `LPData`, `lpHead`, `lpTail`, `lpZ`, `lyapunov_perron`, `lp_lipschitz`, `exists_lip_remainder`, `lpData_of` |

## §6.4 Euler equations

| Source | Claim | Lean |
| --- | --- | --- |
| (4)–(5), pp. 148–149 | The linearized Euler equation and its first-order form `A` | `eulerJ`, `eulerK`, `eulerA`, `fxy_mul_eulerJ`, `fxy_mul_eulerK` |
| Ex 6.5, p. 149 | `A` and `I − A` are nonsingular | `det_fromBlocks_one_zero`, `ex_6_5` |
| Lemma 6.7, p. 150 | If `λ` is a root of `A`, so is `(βλ)⁻¹` | `det_char_block`, `det_char_eq`, `root_inv_of_root`, `lemma_6_7` |
| Ex 6.6, p. 150 | The scalar case: real roots of the sign of `F_xy` | `quadRoot`, `quadRoot_real`, `ex_6_6` |
| Theorem 6.8, p. 151 | The linear-quadratic problem: a unique optimal plan, satisfying (2) and converging | `lqQ`, `lqF`, `lqF_add`, `lqQ_neg`, `exists_lqQ_bound`, `lq_assumption42`, `lq_sufficient`, `lq_unique`, `finrank_stableSubspace`, `hom_euler_eq_zero`, `stable_real_inr_zero`, `exists_stable_start`, `lqBar`, `lqBar_stationary`, `theorem_6_8` |
| Theorem 6.9, p. 153 | Local stability of the nonlinear problem | `exists_eulerZeta`, `stackH`, `hasStrictFDerivAt_stackH`, `exists_convergent_euler_path`, `total_eq_tsum_of_bdd`, `optimal_unique`, `theorem_6_9` |
| pp. 154–155 | The growth model: `λ₁ < 1 < β⁻¹ < λ₂` | `growth_roots` |
| p. 155 | The optimal policy has slope `g′(k*) = λ₁` | `growthC`, `euler_linearization`, `hasDerivAt_of_slope_contraction`, `Setting61.gpol_between`, `Setting61.hasDerivAt_gpol_of_root`, `growth_policy_deriv` |

## §6.5 Applications (Exercises 6.7–6.10)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 6.7a, p. 156 | Cobb–Douglas with `k^a(1 − y)^b`: existence and uniqueness of the optimal plan | `cdF`, `geomMean_concave`, `cd_concave`, `cd_not_strict`, `cdFs`, `cd_assumption43`, `cd_assumption44`, `mem_argmax_iff`, `ex_6_7a` |
| Ex 6.7b | The unique interior stationary point `k* = βa/(b + βa)` | `euler_steady`, `ex_6_7b`, `kstar_eq` |
| Ex 6.7c | The roots of the linearization | `linearization_B`, `ex_6_7c`, `ex_6_7c_stable_iff` |
| Ex 6.7d | `β = 0.1`, `α = 0.8`, `θ = 0.75`: `k*` is not locally stable | `ex_6_7d` |
| Ex 6.7e | A two-cycle is optimal iff it satisfies the two Euler equations | `cdΓ`, `cyc`, `cd_assumption42`, `cyc_sufficient`, `cyc_necessary`, `ex_6_7e` |
| Ex 6.7f, p. 158 | The optimal two-cycle | `cycP`, `euler_iff_poly`, `polyRoot`, `cycle_q_eq`, `ex_6_7f_book_box`, `ex_6_7f` |
| Ex 6.7g, p. 158 | Saddle-path stability of the two-cycle | `linJ`, `linK`, `linJK_eq`, `ex_6_7g` |
| Ex 6.8, p. 159 | The firm with adjustment costs: a unique steady state and monotone convergence | `FirmDyn`, `fpol`, `FirmDyn.fpol_mem`, `continuousOn_fpol`, `monotoneOn_fpol`, `fpol_zero_pos`, `fpol_K_lt`, `steady_eq`, `ex_6_8a_unique`, `orbit_tendsto_of_crossing`, `ex_6_8` |
| Ex 6.8c | The roots of the linearization: one in `(0, 1)`, one above `1` | `roots_split`, `ex_6_8c` |
| Ex 6.9a, p. 160 | A constant-returns industry: existence, uniqueness, strict concavity | `crsQ`, `crsF`, `CRSHyp`, `crsQ_concave`, `crsQ_strict`, `crs_unbounded`, `crsΓ`, `crsFs`, `crs_assumption43`, `crs_assumption44`, `crsValue_of_fixed`, `crs_mem_argmax_iff`, `ex_6_9a`, `CRSValue`, `CRSValue.strictConcaveOn` |
| Ex 6.9b | `g` is nondecreasing | `argmax_lt`, `argmax_unique`, `hasDerivAt_V`, `foc`, `argmax_mono` |
| Ex 6.9c | The stationary point | `stationary_eq`, `stationary_unique`, `no_stationary`, `sqrtPhi`, `expS`, `sqrtPhi_hyp`, `ex_6_9c_counterexample` |
| Ex 6.9d | The roots of the linearization | `ex_6_9d` |
| Ex 6.9e | Convergence to `x̄` | `ex_6_9e` |
| Ex 6.10a, p. 161 | A consumer with recursive preferences: stationary wealth | `cv`, `exists_unique_fixed_z`, `hasDerivAt_dir`, `nextWealth_bar`, `ex_6_10a_if`, `ex_6_10a_only_if` |
| Ex 6.10b | Sufficient conditions for a stationary point | `exists_unique_fixed_z` (a reduction to one equation) |
| Ex 6.10c | Additive preferences: `β = R` and `β ≠ R` | `ex_6_10c_eq`, `ex_6_10c_ne` |
| Ex 6.10d | The Euler equation | `ex_6_10d` |
| Ex 6.10e–f | Local and global stability | Not formalized (open-ended) |
