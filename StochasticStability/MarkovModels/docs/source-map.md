# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 1, pp. 3–20; Chapter 2, pp. 21–47; Appendix C, pp. 543–551. Equation numbers
and assumption labels are the book's. Lean names are relative to `MeynTweedie.MarkovModels`. Where
the Lean statement departs from the book, see [corrections](corrections.md).

## Chapter 1 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| (1.1), p. 3 | A time-homogeneous Markov chain has transition probabilities `Pⁿ(x, A)` with `P(Φₙ₊ₘ ∈ A \| Φⱼ, j ≤ m; Φₘ = x) = Pⁿ(x, A)` | Transition laws are Mathlib's `Kernel X X`, and `Pⁿ` is the kernel power `P ^ n`. The Markov property itself is Chapter 3's (project `TransitionProbabilities`) |

## §1.1 A range of Markovian environments

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 3–6 | Examples (a)–(h): cruise control, queues, exchange rates, storage, populations, Markov chain Monte Carlo, word usage, networks | Not formalised (heuristic) |

## §1.2 Basic models in practice

| Source | Claim | Lean |
| --- | --- | --- |
| (1.2), p. 6 | A process with finite memory is Markov on the vectors `Φₙ = (Yₙ, …, Yₙ₋ₖ)` | For autoregressions: `arVec`, `arVec_succ`; for ARMA and NARMA, the lag-vector states of `armaStep` and `narmaStep` |
| p. 7 | Embedded regeneration points: a dam viewed at input times | §2.4 below |
| (1.3), p. 7 | The deterministic linear system `xₖ₊₁ = F xₖ` | `recursionKernel_const_noise` (a recursion that ignores its disturbance is the deterministic kernel `Kernel.deterministic`) |
| Figure 1.1, p. 8 | For `F = I + ΔA`, `A = [[−0.2, 1], [−1, −0.2]]`, `Δ = 0.02`, the trajectory spirals in; with `F⁻¹` it spirals out | `fig11F`, `fig11F_eq`, `sqNorm2`, `fig11_sqNorm_mulVec` (`\|F x\|² = 0.992416 \|x\|²`), `fig11_tendsto_zero`, `fig11_inv_tendsto_atTop`. The plotted sample paths are not formalised |
| (LCM1)–(LCM2), (1.4), p. 9 | The linear control model LCM(F, G), `xₖ₊₁ = F xₖ + G uₖ₊₁` | `lcmTrajectory`, `lcmTrajectory_eq`, `linear_controlMap` |
| (LSS1)–(LSS2), p. 9 | The linear state space model LSS(F, G), `Xₖ₊₁ = F Xₖ + G Wₖ₊₁`, with i.i.d. noise of finite mean and variance | `lssKernel`, `measurable_lssStep`, `lssKernel_apply'`, `isMarkovKernel_lssKernel`; with matrices: `lssMatrixKernel`, `measurable_mulVec`, `measurable_lssMatrixStep`, `isMarkovKernel_lssMatrixKernel`; the moment condition: `HasFiniteMeanVariance` |
| (LSS1), p. 9 | The paths are `Xₖ = Fᵏ x₀ + Σⱼ Fᵏ⁻ʲ G Wⱼ` (not printed; it follows from (LSS1)) | `orbit_linear`, `orbit_lss`, `orbit_lssMatrix`, `clm_pow_apply`, `matrix_pow_mulVec`, `mulVecHom`, `coe_mulVecHom`; the `n`-step laws: `lssKernel_pow_apply`, `lssMatrixKernel_pow_apply` |
| p. 10, Figure 1.1 | A path of LSS(F, G) with Gaussian noise behaves differently from the deterministic model | Not formalised (simulation) |
| p. 10 | If LCM(F, G) is stable and `Γ` is reasonable, LSS(F, G) is stable | Not formalised (proved in later chapters) |
| (1.5), p. 10 | The gambler's fortune `Φₖ₊₁ = Φₖ + Wₖ₊₁` is a Markov chain | `randomWalkKernel` |
| (RW1), (1.6), p. 11 | Random walk on `ℝ` | `randomWalkKernel`, `measurable_add_step`, `randomWalkKernel_apply`, `randomWalkKernel_apply'`, `isMarkovKernel_randomWalkKernel`, `randomWalkKernel_real_apply_Iic`; paths: `controlMap_add`, `orbit_randomWalk`; `n` steps: `convPow`, `measurable_sum_fin`, `randomWalkKernel_pow_apply` |
| Figure 1.2, pp. 11–12 | Paths with increments `N(0, 1)`, `N(−0.2, 1)`, `N(0.2, 1)`; when is ruin certain? | Not formalised (simulation; ruin in later chapters) |
| p. 12 | Random walk is LSS(F, G) in one dimension with trivial `F`, `G` | `randomWalkKernel_eq_lssKernel` |
| (RWHL1), (1.7), p. 12 | Random walk on a half line, `Φₖ₊₁ = [Φₖ + Wₖ₊₁]⁺` | `halfLineStep`, `measurable_halfLineStep`, `halfLineWalkKernel`, `isMarkovKernel_halfLineWalkKernel`, `halfLineWalkKernel_apply'`, `halfLineWalkKernel_apply_zero`, `halfLineWalkKernel_apply_Iic`, `halfLineWalkKernel_apply_Ioi` |
| p. 12 | The chain follows the random walk, is held at zero, and leaves zero only at a positive increment | `halfLineOrbit`, `partialSum`, `halfLineOrbit_succ_coe`, `halfLineOrbit_eq_of_nonneg`, `halfLineOrbit_succ_of_eq_zero`, `halfLineOrbit_eq_lindley` |
| p. 12, Figure 1.3, p. 13 | Random walk on a half line models storage and queues; reflected paths | Storage and queues in §2.4 below; the figure is not formalised |

## §1.3 Stochastic stability for Markov models

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 13–14 | What "stability" means | Not formalised (heuristic) |
| p. 14 | `Pₓ`, the law of the chain started at `x` | `trajKernel`, `isMarkovKernel_trajKernel`, `pathMeasure`, `isProbabilityMeasure_pathMeasure` |
| p. 14 | The hitting time `τ_A = inf(n ≥ 1 : Φₙ ∈ A)` | `hittingTime`, `hitEvent`, `hittingTime_lt_top_iff`, `measurableSet_hitEvent` |
| (I), p. 14 | φ-irreducibility: `φ(A) > 0 ⇒ Pₓ(τ_A < ∞) > 0` | `IsPhiIrreducible`. On a countable space it is irreducibility with counting measure: not formalised (Chapter 4) |
| p. 14 | LCM(F, G) is controllable if every state can be steered to every other | `IsControllable` |
| (II), (1.8)–(1.9), p. 15 | `φ(A) > 0 ⇒ Pₓ(τ_A < ∞) = 1`; `φ(A) > 0 ⇒ Eₓ[τ_A] < ∞` | `IsPhiRecurrent`, `HasFiniteMeanHitting` |
| (1.10), p. 15 | Evanescence `{Φ → ∞}` for open precompact sets `Oₙ` | `evanescenceEvent`, `IsNonEvanescent` |
| (1.11), p. 15 | Tightness: `lim inf_k Pᵏ(x, C) ≥ 1 − ε` for some compact `C` | `IsTightChain` |
| p. 15 | For T-chains, (1.8) is equivalent to non-evanescence and (1.9) to tightness; for deterministic models (1.8) and (1.9) agree | Not formalised (proved in later chapters) |
| (III), p. 15 | Ergodic behaviour: an invariant regime `π` and convergence to it | Not formalised (heuristic; Part III) |
| Theorem 1.3.1, (1.12)–(1.16), p. 16 | Four equivalent conditions: a unique invariant `π`; `sup_{x ∈ C} Eₓ[τ_C] ≤ M_C`; the drift condition `PV ≤ V − 1 + b 1_C`; local convergence; each gives `sup_A \|Pⁿ(x, A) − π(A)\| → 0` for aperiodic chains | The conditions: (1.12) is Mathlib's `Kernel.Invariant`, with `invariant_iff_eq_lintegral`; `IsSmallSet`; (1.13) `BoundedMeanReturn`; (1.14) `SatisfiesDrift`; (1.15) `IsLocallyConvergent`; (1.16) `tvDist`, `ConvergesInTotalVariation`. The theorem is a forward reference (Chapter 13), not formalised |
| §1.3.2, p. 17 | A (semi) dynamical system `(T, X, d)` with `T` continuous | `IsSemiDynamicalSystem` |
| p. 17 | The dynamical system `μ ↦ μP` on probability measures; the Feller property | `distStep`, `IsWeakFeller` |
| (i), p. 17 | Lagrange stability; for `(P, M, d)` it is tightness (1.11) | `IsLagrangeStable`; the identification with (1.11) is not formalised |
| (ii), p. 18 | Stability in the sense of Lyapunov | `IsLyapunovStable` |
| (iii), p. 18 | Asymptotic stability; the fixed points of `(P, M, d)` are the solutions of (1.12) | `IsAsymptoticallyStable`, `fixedPoint_distStep_iff` |
| (iv), (1.17), p. 18 | Global asymptotic stability | `IsGloballyAsymptoticallyStable` |
| p. 18 | `xₖ₊₁ = xₖ + 1` is stable in the sense of Lyapunov but not stable in the other senses | `iterate_add_one`, `succ_isLyapunovStable`, `succ_not_isLagrangeStable`, `succ_not_isGloballyAsymptoticallyStable` |
| Theorem 1.3.2, p. 18 | For a φ-irreducible aperiodic Feller chain with `supp φ` containing an open set, `(P, M, d)` is globally asymptotically stable iff `{Pᵏ(x, ·)}` is tight, and then (1.16) holds | The conditions: `IsPhiIrreducible`, `IsWeakFeller`, `IsTightChain`, `ConvergesInTotalVariation`. The theorem is a forward reference (Chapters 6 and 18), not formalised |
| pp. 18–19 | Relations between the recurrence and dynamical-system approaches | Not formalised (heuristic) |

## §1.4 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 19–20 | Continuous time and multi-parameter models are excluded; terminology; notation; other notions of stability | Not formalised (commentary) |

## Chapter 2 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 21–22 | Noise convention: an error, noise, innovation, disturbance or increment sequence is i.i.d. with law `Γ` | Each model is a `recursionKernel Γ F` or is built from one: `recursionKernel`, `recursionKernel_apply`, `recursionKernel_apply'`, `isMarkovKernel_recursionKernel`. An i.i.d. sequence is `Measure.infinitePi`: `infinitePi_map_shift`, `law_orbit` |
| p. 22 | Initialization: `Φ₀` is independent of the noise, with an arbitrary distribution | Chains start at a point `x` (`orbit`, `orbit_zero`, `orbit_succ`, `pathMeasure`); an initial law `μ` enters as `μ.bind P` (`distStep`, `bind_renewalKernel_singleton`, `renewal_law`) |

## §2.1 Markov models in time series

| Source | Claim | Lean |
| --- | --- | --- |
| (SLM1)–(SLM2), p. 23 | The simple linear model AR(1), `Xₙ₊₁ = αXₙ + Wₙ₊₁` | `ar1Kernel`, `measurable_ar1Step`, `isMarkovKernel_ar1Kernel`, `ar1Kernel_apply'`, `orbit_ar1` |
| p. 23 | AR(1) extends random walk and is LSS(α, 1) | `ar1Kernel_one`, `ar1Kernel_eq_lssKernel` |
| p. 23, Figure 2.1, p. 24 | For `\|α\| < 1` the chain is ergodic; for `\|α\| > 1` it is evanescent; paths for `α = 0.85, 1.05` | Not formalised (proved in later chapters; simulation) |
| (AR1)–(AR2), p. 24 | The AR(k) model | `shiftIn`, `shiftIn_apply_zero`, `shiftIn_apply_succ`, `measurable_shiftIn`, `shiftIn_add`, `arStep`, `measurable_arStep`, `arKernel`, `isMarkovKernel_arKernel` |
| p. 24 | `Xₙ = (Yₙ, …, Yₙ₋ₖ₊₁)` is a Markov chain whose first coordinate has the AR paths | `arVec`, `arVec_succ` |
| (2.1), p. 25 | AR(k) as LSS with the companion matrix | `companion`, `firstUnit`, `arStep_eq_companion`, `arKernel_eq_lssMatrixKernel` |
| (ARMA1)–(ARMA2), p. 25 | The ARMA(k, ℓ) model, Markov on `(Yₙ, …, Yₙ₋ₖ₊₁, Wₙ, …, Wₙ₋ℓ₊₁)` | `armaStep`, `measurable_armaStep`, `armaKernel`, `isMarkovKernel_armaKernel` |
| (2.2), p. 25 | If `Z` is the AR(k) recursion (2.2), then `Yₙ = Zₙ + β₁Zₙ₋₁ + ⋯ + β_ℓZₙ₋ℓ` is ARMA(k, ℓ), "by simple algebra and an inductive argument" | `arma_of_ar` |

## §2.2 Nonlinear state space models

| Source | Claim | Lean |
| --- | --- | --- |
| (2.3), p. 26 | A semi-dynamical system `xₙ₊₁ = F(xₙ)` | `IsSemiDynamicalSystem`, `recursionKernel_const_noise` |
| (2.4), p. 26 | `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` with `F` smooth | `recursionKernel`, `nssKernel`, `IsSmoothModel` |
| (SNSS1)–(SNSS2), p. 26 | The scalar nonlinear state space model SNSS(F) | `nssKernel` with `X = W = ℝ`, `IsSmoothModel`, `HasDensityOnControlSet`, `isMarkovKernel_nssKernel_of_contDiff` |
| (2.5)–(2.6), p. 27 | The control maps `Fₖ` and the control model CM(F) | `controlMap`, `controlMap_zero`, `controlMap_one`, `controlMap_succ`, `controlMap_succ_cons`, `measurable_controlMap`, `measurable_controlMap_right`, `orbit`, `orbit_eq_controlMap`; the `n`-step kernel through `Fₙ`: `recursionKernel_pow_apply`, `recursionKernel_pow_apply'` |
| (SBL1), (2.7), p. 27 | The simple bilinear model, `F(x, w) = θx + bxw + w` | `bilinearStep`, `contDiff_bilinearStep`, `bilinearKernel`, `isMarkovKernel_bilinearKernel`, `bilinearKernel_apply'` |
| Figure 2.2, pp. 27–28 | A path of `F(x, w) = (0.707 + w)x + w` | `bilinearStep_eq` (the form `(θ + bw)x + w`); the path is not formalised |
| (SETAR1), p. 28 | The SETAR model, `Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)` for `r_{j−1} < Xₙ₋₁ ≤ r_j` | `setarP`, `setarP_exists`, `setarRegime`, `setarRegime_eq_iff`, `setarRegime_eq_iff_Ioc`, `measurable_setarRegime`, `setarStep`, `measurable_setarStep`, `setarKernel`, `isMarkovKernel_setarKernel`, `setarKernel_apply'`; zero-mean noises: `SatisfiesSETAR1Noise` |
| p. 28 | SETAR models are not continuous, so they are not NSS(F) models | `setar_not_continuous` |
| (NSS1)–(NSS2), p. 29 | The nonlinear state space model NSS(F) | `nssKernel`, `isMarkovKernel_nssKernel_of_contDiff`, `HasDensityOnControlSet` |
| (CM1), (2.8), p. 29 | The associated control system CM(F) | `controlMap` |
| (NARMA1)–(NARMA2), (2.9), p. 30 | The NARMA(k, ℓ) model and its Markovian realization | `narmaStep`, `measurable_narmaStep`, `narmaKernel`, `isMarkovKernel_narmaKernel`, `armaKernel_eq_narmaKernel` |
| (2.10), p. 30 | `vₙ = 1/vₙ₋₁ − 1/vₙ₋₂`, and `xₙ = (vₙ, vₙ₋₁)` follows `F(a, b) = (1/a − 1/b, a)` | `gumleafMap`, `gumleafMap_of_recursion` |
| p. 30 | `[z] = (1 + \|z\|)⁻¹ z` lies in the open unit disk and is one-to-one | `eNorm2`, `eNorm2_smul`, `squash`, `eNorm2_squash`, `eNorm2_squash_lt_one`, `unsquash`, `unsquash_squash`, `squash_unsquash` |
| (2.11), p. 30 | The transformed model `[xₙ] = F([xₙ₋₁])` | `gumleaf_printed_ne`; corrected: `squash_gumleafMap` |
| Figure 2.3, p. 31 | The gumleaf attractor, without and with noise | Not formalised (simulation) |
| (2.12), p. 31 | The gumleaf recursion perturbed by noise | `gumleafNoisyStep`, `measurable_gumleafNoisyStep`, `gumleafKernel`, `isMarkovKernel_gumleafKernel` |
| p. 31 | The path structure of such models (Chapter 7) | Not formalised (Chapter 7) |
| (DBL1), (2.13)–(2.14), p. 32 | The dependent parameter bilinear model, `Yₖ₊₁ = θₖYₖ + Wₖ₊₁`, `θₖ₊₁ = αθₖ + Zₖ₊₁` | `dblStep`, `dblStep_fst` (2.14), `dblStep_snd` (2.13), `contDiff_dblStep`, `dblKernel`, `isMarkovKernel_dblKernel` |
| (DBL2), p. 32 | Independent `Z`, `W` with lower semicontinuous densities, `E[W²] < ∞`, `E[log(1 + \|Z\|)] < ∞` | `SatisfiesDBL2`; independence is the product law in `dblKernel` |
| (2.15), p. 32 | The model map `F` | `dblPrinted`, `dbl_printed_ne`; corrected: `dblStep` |
| Figure 2.4, pp. 32–33 | Paths with `α = 0.933` | Not formalised (simulation) |

## §2.3 Models in control and systems theory

| Source | Claim | Lean |
| --- | --- | --- |
| §2.3.1, (2.16)–(2.17), pp. 33–34 | The ARX model; sample mean square stabilizing inputs; minimum variance control laws | Not formalised |
| §2.3.2, (2.18)–(2.19), pp. 34–35 | The control with known `θ`; the stochastic gradient algorithm; its state `(r_k⁻¹, φ_k, θ̂_k)` is a Markov chain | Not formalised |
| (SAC1)–(SAC3), p. 35 | The simple adaptive control model, (2.20)–(2.21), Gaussian noise, causal inputs | (2.20)–(2.21) are hypotheses of `sac_closed_loop`; (SAC2): `SatisfiesSAC2`, `sacGaussianKernel`; (SAC3) holds for the certainty equivalence control built into `sacStep` |
| p. 36 | `θ̂ₖ = E[θₖ \| 𝒴ₖ]` is given by the Kalman filter recursion for `θ̂ₖ₊₁` and `Σₖ₊₁`, and `Σₖ = E[θ̃ₖ² \| 𝒴ₖ]` | The recursion enters `sac_closed_loop` and `sacStep`; that it computes the conditional mean and variance is not formalised |
| p. 36 | With `α = 1`, `σ_w = 1`, `σ_z = 0` the recursion is recursive least squares | `sac_rls` |
| (2.22)–(2.24), p. 36 | The closed loop equations under the certainty equivalence control `Uₖ = −θ̂ₖYₖ` | `sac_closed_loop`, `sacStep`, `measurable_sacStep` |
| (2.25), p. 36 | `Φₖ = (Σₖ, θ̃ₖ, Yₖ)` is a Markov chain on `[σ_z², σ_z²/(1 − α²)] × ℝ²` | `sacKernel`, `isMarkovKernel_sacKernel`, `sacGaussianKernel`, `isMarkovKernel_sacGaussianKernel`, `sacStep_sigma_mem`, `sacKernel_apply_Icc` |
| Figures 2.5–2.6, pp. 37–38 | Paths for `σ_z = 0.2, 1.1`; the mean square performance (2.17) (Chapter 16) | Not formalised (simulation; Chapter 16) |

## §2.4 Markov models with regeneration times

| Source | Claim | Lean |
| --- | --- | --- |
| p. 38 | The (delayed) renewal process `Zₙ = Y₀ + ⋯ + Yₙ` on `ℤ₊`, `p(0) = 0`; it is evanescent | `renewalKernel`, `isMarkovKernel_renewalKernel`, `renewalKernel_apply_singleton`, `renewalKernel_apply_Ioi`, `le_renewal` |
| p. 38 | `P(Z₁ = n) = Σ_{j ≤ n} a(j) p(n − j)` | `bind_renewalKernel_singleton`, `renewal_law_one` |
| p. 39 | The convolution `a ∗ b` in its two forms; `a^{k∗}` | `seqConv`, `seqConv_eq_sum_range`, `seqConv_comm`, `seqConvPow`, `seqConvPow_succ`, `mk_coeff_eq`, `mk_seqConv`, `mk_seqConvPow` |
| p. 39 | `P(Z_k = n) = a ∗ p^{k∗}(n)` | `renewal_law` |
| (RT1)–(RT2), p. 39 | The forward and backward recurrence times `V⁺(n)`, `V⁻(n)` | `fwdTime`, `fwdTime_set_nonempty`, `one_le_fwdTime`, `bwdTime`; the empty infimum in (RT2): `bwdTime_set_empty`, `bwdTime_set_empty_example` |
| p. 39 | `V⁺` counts down and is renewed with law `p` at `1`; `V⁻` ages by one or drops to zero with the conditional renewal probability | Pathwise: `fwdTime_succ_of_one_lt`, `fwdTime_succ_of_eq_one`, `bwdTime_succ_of_renewal`, `bwdTime_succ_of_not_renewal`. Kernels: `fwdStep`, `forwardKernel`, `isMarkovKernel_forwardKernel`, `forwardKernel_of_one_lt`, `forwardKernel_one`, `hazard`, `hazard_le_one`, `backwardKernel`, `backwardKernel_apply`, `isMarkovKernel_backwardKernel`, `backwardKernel_apply_zero`, `backwardKernel_apply_succ` |
| p. 39 | `V⁺` and `V⁻` are stable under straightforward conditions | Not formalised (proved in later chapters) |
| (Q1)–(Q3), p. 40 | The GI/G/1 queue | `waitingTimeKernel` (service and interarrival laws `H ⊗ G`) |
| pp. 40–41, (2.26)–(2.27), Figure 2.7 | The queue length `N(t)` in continuous time; arrival and service epochs | Not formalised |
| (2.28), p. 41 | `P(Nₙ₊₁ = j + k \| Nₙ = j, …) = p_k` for `k ≥ −j`: the queue length at arrivals is a random walk on `ℤ₊` | `giM1Step`, `giM1Kernel`, `isMarkovKernel_giM1Kernel`, `giM1Kernel_apply'`. Read literally: `not_down_of_eq_2_28`, `giM1Kernel_not_2_28`, `twoPointLaw`, `reflectedWalk_2_28_fails`. Corrected: `giM1Kernel_apply_le`, `giM1Kernel_apply_zero`; random walk on `ℤ₊`: `reflectStep`, `reflectedWalkKernel`, `isMarkovKernel_reflectedWalkKernel`, `reflectedWalkKernel_apply_pos`, `reflectedWalkKernel_apply_zero` |
| p. 41 | `Nₙ₊₁` exceeds `Nₙ` by at most one | `giM1Kernel_apply_up` |
| (2.29)–(2.30), pp. 41–42 | For most service laws the residual service depends on the elapsed service, so `N` is not Markov | `dirac_not_memoryless` ((2.30) for a deterministic service time); that `N` is not Markov is not formalised |
| (Q4), p. 42 | Exponential service: the GI/M/1 queue | `IsGIM1Service`, `cdf_of_isGIM1Service` |
| p. 42 | The memoryless property `P(S > t + z \| S > z) = e^{−μt}` | `expMeasure_Ioi`, `expMeasure_memoryless` |
| pp. 42–43 | `P(Nₙ₊₁ = j + 1 \| Nₙ = j, …) = ∫ e^{−μt} G(dt)` | `expMeasure_prod_lt` |
| p. 43 | From `j`, `Nₙ₊₁ = i` for `0 < i ≤ j` when `j − i + 1` customers leave | `giM1Kernel_apply_le` |
| p. 43 | The queue length `N*ₙ` after departures is Markov for the M/G/1 queue | `mG1Step`, `mG1Kernel`, `isMarkovKernel_mG1Kernel`, `mG1Kernel_apply`, `mG1Kernel_zero` |
| (Q5), p. 43 | Exponential interarrival times: the M/G/1 queue | `IsMG1Arrivals` |
| p. 43 | The Moran dam: inputs `S ~ H` at interarrival times `T ~ G`, release at rate `r` | `storageStep`, `measurable_storageStep` |
| (SSM1)–(SSM2), (2.31), p. 44 | The simple storage model, `Φₙ₊₁ = [Φₙ + Sₙ − Jₙ]⁺`, `P(Jₙ ≤ x) = G(−∞, x/r]` | `storageKernel`, `isMarkovKernel_storageKernel`, `releaseLaw_Iic` |
| p. 44 | It is random walk on a half line with `Wₙ = Sₙ − Jₙ` | `storageKernel_eq_halfLineWalk`, `recursionKernel_comp_noise` |
| p. 44 | Sampled at other times the process is not Markov | Not formalised |
| p. 44 | The mean input `α` and mean output `β`; the ratio `α/β` decides stability (Figure 2.8, p. 45) | `storage_mean_increment` (mean increment `α − β`); the role of `α/β` and the figure are not formalised |
| p. 45 | Level-dependent inputs `H_x` and release rate `r(x)`; `R(x) = ∫₀ˣ r(y)⁻¹ dy` (2.32) is strictly increasing | `releaseTime`, `continuous_releaseTime`, `releaseTime_strictMono`, `releaseTime_strictMonoOn` |
| p. 45 | `R⁻¹(t)` is defined for all `t`, and `q(x, t) = R⁻¹(R(x) − t)` | `releaseTime_one_add_sq`, `releaseTime_not_surjective`; corrected: `releaseTime_bijOn` |
| (CSM1)–(CSM2), (2.33), p. 46 | The content-dependent storage model at the times `Tₙ−` before inputs | `inputKernel`, `inputKernel_apply`, `contentKernel`, `isMarkovKernel_contentKernel`, `contentKernel_apply'`, `contentRelease_Iic`; `contentKernel_ne_storageKernel`; corrected: `contentPreInputKernel`, `contentPreInputKernel_eq_storageKernel` |
| p. 46 | The model also describes waiting times with level-dependent service | Not formalised |
| (not in Chapters 1–2) | The birth–death chain on `ℤ₊`, for later chapters | `birthDeathKernel`, `birthDeathKernel_apply`, `isMarkovKernel_birthDeathKernel`, `birthDeathKernel_apply_succ`, `birthDeathKernel_apply_pred` |

## §2.5 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 46–47 | Literature; (2.13)–(2.14) is the DSAR(1) process; state-dependent models; Markov chain Monte Carlo | Not formalised (commentary) |
| p. 47 | The storage model with unit release rate is the residual service (workload) of the GI/G/1 queue | `lindleyStep`, `measurable_lindleyStep`, `waitingTimeKernel`, `isMarkovKernel_waitingTimeKernel`, `waitingTimeKernel_eq_halfLineWalk`, `storageKernel_one` |

## Appendix C.1 Regenerative models

| Source | Claim | Lean |
| --- | --- | --- |
| (RT1)–(RT2), p. 543 | Forward and backward recurrence time chains | `fwdTime`, `bwdTime`, `forwardKernel`, `backwardKernel` (see §2.4) |
| (RT3), p. 543 | `V⁺(t) = inf(Zₙ − t : Zₙ > t, n ≥ 1)` and its `δ`-skeleton | `fwdTimeCts`, `fwdSkeleton` |
| (RT4), p. 543 | `V⁻(t) = inf(t − Zₙ : Zₙ ≤ t, n ≥ 1)` and its `δ`-skeleton | `bwdTimeCts`, `bwdSkeleton` |
| (RW1), (1.6), p. 544 | Random walk on `ℝ` | `randomWalkKernel` |
| (RW2), p. 544 | Spread out: some `Γ^{n∗}` is non-singular with respect to Lebesgue measure | `IsSpreadOut` |
| (RWHL1), (1.7), p. 544 | Random walk on a half line | `halfLineWalkKernel` |
| (Q1)–(Q3), p. 544 | The GI/G/1 queue | `waitingTimeKernel`; at arrivals and departures: `giM1Kernel`, `mG1Kernel` |
| (Q4), p. 545 | `H(−∞, t] = 1 − e^{−μt}`: GI/M/1 | `IsGIM1Service`, `cdf_of_isGIM1Service` |
| (Q5), p. 545 | `G(−∞, t] = 1 − e^{−λt}`: M/G/1 | `IsMG1Arrivals` |
| (SSM1)–(SSM2), (2.31), p. 545 | The simple storage model with release rate `r` | `storageKernel`, `releaseLaw_Iic` |
| (CSM1)–(CSM2), (2.33), p. 545 | The content-dependent storage model | `contentKernel`, `contentRelease_Iic`; see [corrections](corrections.md) |
| p. 545 | These models also represent state-dependent queues | Not formalised |

## Appendix C.2 State space models

| Source | Claim | Lean |
| --- | --- | --- |
| (SLM1)–(SLM2), p. 546 | The simple linear model | `ar1Kernel` |
| (LSS1), p. 546 | LSS(F, G) | `lssKernel`, `lssMatrixKernel` |
| (LSS2), p. 546 | i.i.d. noise with finite mean | `HasFiniteMeanVariance` (finite mean and variance, the form of p. 9) |
| (LSS3), p. 546 | `W ~ N(0, I)` | `IsStdGaussianNoise`, `isMarkovKernel_lssMatrixKernel_of_stdGaussian` |
| (LSS4), p. 546 | `Γ` non-singular with respect to Lebesgue measure | `IsNonsingularNoise` |
| (LSS5), p. 546 | The eigenvalues of `F` lie in the open unit disk | `HasStableEigenvalues` |
| (LCM1)–(LCM2), (1.4), pp. 546–547 | LCM(F, G) | `lcmTrajectory` |
| (AR1)–(AR2), p. 547 | AR(k) | `arKernel` |
| (ARMA1)–(ARMA2), p. 547 | ARMA(k, ℓ) | `armaKernel` |
| (DS1), p. 547 | A semi-dynamical system with `F` continuous | `IsSemiDynamicalSystem`, `recursionKernel_const_noise` |
| (DS2), p. 547 | `V(F(x)) − V(x) ≤ −1` off a compact `C`, `sup_C V ∘ F ≤ M` | `SatisfiesDS2` |
| (SNSS1), (NSS1), pp. 547–548 | SNSS(F) and NSS(F) with `F` smooth | `nssKernel`, `IsSmoothModel`, `isMarkovKernel_nssKernel_of_contDiff` |
| (SNSS2), (NSS2), p. 548 | A density supported on the open control set `O_w` | `HasDensityOnControlSet` |
| (SNSS3), (NSS3), p. 548 | A lower semicontinuous density; `O_w = {γ_w > 0}` | `HasLscDensity`, `isOpen_controlSet`, `hasDensityOnControlSet_of_lsc` |
| (CM1), (2.8), p. 548 | CM(F) | `controlMap` |
| (CM2), (7.4), p. 548 | Some control sequence makes the derivative of `Fₖ` in the controls non-zero | `SatisfiesCM2` |
| (CM3), (7.13), p. 549 | Some control sequence makes `rank C_x^k(u) = n` | `SatisfiesCM3` |
| (NARMA1)–(NARMA2), p. 549 | NARMA(k, ℓ) | `narmaKernel` |
| (SAC1)–(SAC3), (2.22)–(2.24), p. 549 | The simple adaptive control model, with `σ_z < 1`, and its closed loop | `sacKernel`, `sacGaussianKernel`, `SatisfiesSAC2`, `sac_closed_loop` |
| (SETAR1), p. 550 | SETAR | `setarKernel`, `SatisfiesSETAR1Noise` |
| (SETAR2), p. 550 | Each regime noise has a density positive on `ℝ` | `SatisfiesSETAR2` |
| (SETAR3), p. 550 | The end-regime noises have finite variance | `SatisfiesSETAR3` |
| (SBL1), p. 550 | The simple bilinear model | `bilinearKernel` |
| (SBL2), p. 550 | Finite second moment and a lower semicontinuous density | `SatisfiesSBL2` |
| (DBL1), (2.13)–(2.14), p. 550 | The dependent parameter bilinear model | `dblKernel` |
| (DBL2), p. 550 | Densities and moments of `Z` and `W` | `SatisfiesDBL2` |
| p. 550, (RCA1), p. 551 | The random coefficient autoregression `Xₖ₊₁ = (A + Γₖ₊₁)Xₖ + Wₖ₊₁` with `Γ`, `W` i.i.d. and independent | `rcaStep`, `measurable_rcaStep`, `rcaKernel`, `isMarkovKernel_rcaKernel`, `rcaKernel_dirac_zero` |
| (RCA2), p. 551 | The moments of `W` and `Γ`; the eigenvalues of `A ⊗ A + C` in the open unit disk | `SatisfiesRCA2` |
| (RCA3), p. 551 | `(Γₖ, Wₖ)` has an everywhere positive density | `SatisfiesRCA3` |
