# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 9, "Approximation and Learning" (pp. 295–321). Result, equation and exercise numbers are
the book's; page numbers are book pages. Lean names are relative to
`SargentStachurski.ApproximationAndLearning`. Where the Lean statement adds a hypothesis the book
leaves implicit, or departs from the printed statement, see [corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 | `GloballyStable`, contractions |
| `SupContraction`, `ContractingDP` | Volume 2, Chapter 1 | `bX` as a set, the contracting optimality template |
| `OrderTheory`, `ADP`, `Algorithms` | Volume 2, Chapter 2 | ADPs, optimality, VFI/OPI/HPI |
| `Minimization`, `FiniteMDP`, `MDPADP`, `Pospace`, `MetricADP`, `MinPospace`, `BoundedMeasurable`, `MDPQFactors` | Volume 2, Chapter 3 | Min-ADPs, finite MDPs, Q-factors, Theorem 3.1.5, `bX` as a Banach lattice (`BM`) |
| `Conjugacy`, `Semiconjugacy`, `FactoredDP`, `QFactorFDP` | Volume 2, Chapter 5 | FDPs, Theorems 5.2.13 and 5.2.18, Proposition 5.3.1 |

## §9.1.1 Approximation methods (pp. 296–299)

| Book | Claim | Lean |
| --- | --- | --- |
| (9.2)–(9.3) | Kernel averagers | `KernelAverager`, `KernelAverager.Lfun`, `KernelAverager.κ_le_one`, `KernelAverager.abs_Lfun_le`, `KernelAverager.Lfun_sub`, `KernelAverager.Lfun_const`, `KernelAverager.measurable_Lfun` |
| Example 9.1.1, p. 297 | Gaussian kernel averagers satisfy (9.2) | `gaussKernel`, `gaussianAverager` |
| Example 9.1.2, p. 297 | Hat functions satisfy (9.2); `Lf` interpolates, is piecewise linear and unique | `hat`, `Hat.hat_nonneg`, `Hat.hat_on`, `Hat.hat_left`, `Hat.hat_right`, `Hat.exists_interval`, `Hat.sum_two`, `Hat.sum_hat`, `Hat.hat_grid`, `Hat.continuous_hat`, `hatAverager`, `example_9_1_2_interpolates`, `example_9_1_2_linear`, `example_9_1_2_unique` |
| Lemma 9.1.1, p. 298 | `L` maps `bX` into itself and is nonexpansive | `KernelAverager.L`, `KernelAverager.L_apply`, `KernelAverager.lemma_9_1_1` |
| §9.1.1.2, p. 299 | Least squares: `θ̂ = (ZᵀZ)⁻¹Zᵀy` | `lsq`, `ssr`, `least_squares` |

## §9.1.2 Error bounds (pp. 299–303)

| Book | Claim | Lean |
| --- | --- | --- |
| (9.4), Assumption 9.1.1, p. 299 | Nonexpansive maps; the standing assumption and its consequences | `ADP.Nonexpansive`, `ADP.Assumption911`, `ADP.Assumption911.bellman_contraction`, `ADP.Assumption911.T_eq_bellman`, `ADP.assumption_9_1_1` |
| Lemma 9.1.2, p. 300 | `T̂ = L ∘ T` is a contraction | `ADP.approxBellman`, `ADP.lemma_9_1_2`, `ADP.approxBellman_globallyStable` |
| Algorithm 9.1, p. 300 | FVI terminates | `ADP.fvi_terminates` |
| Thm 9.1.3, (9.5)–(9.9), p. 301 | The first error bound | `ADP.Assumption911.one_sub_mul_dist_fixed_le`, `ADP.Assumption911.one_sub_mul_dist_vσ_le`, `ADP.theorem_9_1_3`, `ADP.theorem_9_1_3_fvi` |
| Thm 9.1.4, (9.10)–(9.12), p. 301 | The second error bound | `ADP.theorem_9_1_4`, `ADP.theorem_9_1_4_fvi` |
| Prop 9.1.5, p. 303 | `(L(V), 𝕋̂)` is an ADP | `ADP.approxADP`, `ADP.proposition_9_1_5` |
| Lemma 9.1.6, p. 303 | Kernel averagers are order preserving | `KernelAverager.lemma_9_1_6` |
| Remark 9.1.2, p. 303 | Kernel averagers satisfy the hypotheses of §9.1.2 | `KernelAverager.remark_9_1_2` |

## §9.1.3 Stochastic approximation (pp. 304–309)

| Book | Claim | Lean |
| --- | --- | --- |
| (9.13), Lemma 9.1.7, p. 304 | Damped iteration | `damped`, `damped_eq`, `lemma_9_1_7`, `damped_iterate_le`, `lemma_9_1_7_needs_convex` |
| (9.14), Thm 9.1.8, p. 306 | Robbins–Monro convergence (Hilbert-space contractions) | `robbins_siegmund`, `robbins_monro` |
| §9.1.3.4, Ex 9.1.1, p. 307 | Asset pricing: `T` is a `β`-contraction, order preserving, `v* = (I − K)⁻¹Kd` | `AssetPricing`, `AssetPricing.T`, `AssetPricing.T_mono`, `AssetPricing.abs_sum_le`, `AssetPricing.exercise_9_1_1`, `AssetPricing.K`, `AssetPricing.T_eq_mulVec`, `AssetPricing.fixedPoint` |
| (9.15), footnote 1, p. 308 | `T̂` is unbiased; (9.15) is (9.14); the noise bounds | `AssetPricing.That`, `AssetPricing.That_unbiased`, `AssetPricing.update_eq`, `AssetPricing.abs_noise_le`, `AssetPricing.sum_sq_noise_le` |
| Thm 9.1.8, Remark 9.1.3, p. 306 | Asynchronous stochastic approximation for max-norm pseudo-contractions (Tsitsiklis, 1994): boundedness and almost sure convergence | `navg`, `navg_restart`, `tendsto_prod_one_sub`, `prod_one_sub_mem`, `stronglyMeasurable_partialSum`, `robbins_siegmund_rand`, `noiseAverage_tendsto_zero`, `noiseAverage_mul_tendsto_zero`, `det_converge`, `runMax`, `scale`, `le_scale`, `det_bounded`, `tsitsiklis` |
| Thm 9.1.8, p. 306 | Robbins–Monro convergence for supremum-norm contractions | `theorem_9_1_8` |
| (9.15)–(9.18), Remark 9.1.3 | Asynchronous updates towards sampled targets | `sampled_tsitsiklis` |
| §9.1.3.4, p. 308 | The batch update (9.15) converges to `v*` almost surely | `AssetPricing.norm_T_sub_le`, `AssetPricing.measurable_T`, `AssetPricing.abs_sample_le`, `AssetPricing.batch_converges` |
| (9.16), §9.1.3.5, p. 309 | The sequential update converges to `v*` almost surely | `AssetPricing.sequential_converges` |

## §9.2 Simulation and learning (pp. 309–321)

| Book | Claim | Lean |
| --- | --- | --- |
| (9.17), §9.2.1.1, p. 310 | `S`, its fixed point `q*`, and Proposition 5.3.1 | `FiniteMDP.qmax`, `FiniteMDP.le_qmax`, `FiniteMDP.abs_qmax_sub_le`, `FiniteMDP.S`, `FiniteMDP.bellman_qadp`, `FiniteMDP.section_9_2_1` |
| §9.2.1.3, p. 311 | `S` is a contraction of modulus `β` | `FiniteMDP.S_contraction` |
| (9.18), p. 310 | The Q-learning update; the sample is unbiased | `FiniteMDP.Shat`, `FiniteMDP.Shat_unbiased`, `FiniteMDP.noise_mean_zero`, `FiniteMDP.qUpdate`, `FiniteMDP.qUpdate_apply` |
| Thm 9.2.1, p. 313 | Q-learning converges to `q*` almost surely | `FiniteMDP.qmax_zero`, `FiniteMDP.abs_qmax_le`, `FiniteMDP.norm_S_sub_le`, `FiniteMDP.measurable_qmax`, `FiniteMDP.theorem_9_2_1` |
| (9.20)–(9.21), Ex 9.2.1, p. 314 | The order-reversing FDP | `FiniteMDP.QPos`, `FiniteMDP.expSum`, `FiniteMDP.Fexp`, `FiniteMDP.Glog`, `FiniteMDP.qmin`, `FiniteMDP.rsfdp`, `FiniteMDP.exercise_9_2_1`, `FiniteMDP.monotonic` |
| §9.2.2.3, (9.19), p. 314 | Primary policy operators and Bellman equation | `FiniteMDP.Gsup_eq`, `FiniteMDP.primary_T`, `FiniteMDP.primary_bellman_eq`, `FiniteMDP.primary_contraction` |
| (9.22), p. 314 | The subordinate Bellman min-equation | `FiniteMDP.sub_bellman_eq` |
| p. 315 | Optimality of the argmin policy (Theorem 5.2.18) | `FiniteMDP.section_9_2_2_3` |
| Ex 9.2.2, p. 315 | `T̂_σ` is a `β`-contraction for `‖ln q − ln q'‖∞` | `FiniteMDP.log_expSum_le`, `FiniteMDP.exercise_9_2_2` |
| (9.23), Remark 9.2.1, p. 317 | The update keeps `q > 0`; `T̂_σ` is order preserving | `FiniteMDP.update_9_23_pos`, `FiniteMDP.remark_9_2_1` |
| Thm 9.2.2, (9.27), p. 320 | Optimality at one state implies optimality under irreducibility | `FiniteMDP.Pσ_pow_nonneg`, `FiniteMDP.Pσ_pow_mulVec_mono`, `FiniteMDP.theorem_9_2_2`, `absorbingMDP`, `theorem_9_2_2_needs_irreducible` |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Remark 9.1.1 | Neural networks are not nonexpansive in general | Informal. |
| Remark 9.2.1 | Convergence of risk-sensitive Q-learning | An open question (the book says so). |
| §9.2.1.4, §9.2.2.4, Figures 9.1–9.10 | Inventory examples and numerical illustrations | Numerical. |
| §9.2.3.1–9.2.3.2 | Policy gradient ascent and the Monte Carlo estimate (9.26) | Algorithms with no mathematical claim beyond differentiability. |
| §9.3 | Chapter notes | Not mathematical claims. |
