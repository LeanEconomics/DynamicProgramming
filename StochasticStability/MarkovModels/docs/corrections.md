# Corrections and conventions

Places where a Lean statement differs from the book: a claim corrected, a hypothesis made
explicit, or a convention chosen. Every false claim below is refuted in Lean by a counterexample,
and a corrected statement is proved. The last section lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| (2.15), p. 32 | The dependent parameter bilinear model is NSS(F) with `F((Y, θ), (Z, W)) = (αθ + Z, θY + W)`. | The argument is written in the order `(Y, θ)` but the value is `(θ′, Y′)`. Read as a map of the state `(Y, θ)`, the printed `F` (`dblPrinted`) does not reproduce (2.13)–(2.14): at `α = 0`, `(Y, θ) = (1, 2)`, `Z = W = 0` it returns `(0, 2)`, while the next state is `(θY + W, αθ + Z) = (2, 0)` (`dbl_printed_ne`). The consistent map is `F((θ, Y), (Z, W)) = (αθ + Z, θY + W)` on the state `(θ, Y)` (`dblStep`, with `dblStep_fst` for (2.14) and `dblStep_snd` for (2.13)). |
| (2.11), p. 30 | After the transformation `[z] = (1 + \|z\|)⁻¹ z`, the gumleaf model is `[xₙ] = F([xₙ₋₁])`. | The printed recursion applies `F` to the transformed state, which is not the transformed chain: from `v₀ = v₁ = 1`, the next transformed state `[(0, 1)]` has second coordinate `1/2`, while the printed recursion gives `1/(2 + √2)` (`gumleaf_printed_ne`). The transformed states follow `[xₙ] = [F(unsquash [xₙ₋₁])]`, where `unsquash y = (1 − \|y\|)⁻¹ y` inverts `[·]` on the open unit disk (`squash_gumleafMap`, `unsquash_squash`, `squash_unsquash`). |
| (2.28), p. 41 | `P(Nₙ₊₁ = j + k \| Nₙ = j, Nₙ₋₁, …) = p_k` for `k ≥ −j`, so the queue length at arrivals is a random walk on `ℤ₊`. | Taken literally, for every `j`, this forces the chain never to move down: row `0` already has total mass `Σ_{k ≥ 0} p_k = 1`, so `P(j, {i}) = 0` for every `i < j` (`not_down_of_eq_2_28`). The GI/M/1 chain does move down, so whenever two service completions in an interarrival time have positive probability no `p` satisfies (2.28) for it (`giM1Kernel_not_2_28`). For random walk on `ℤ₊`, `Nₙ₊₁ = [Nₙ + ξₙ₊₁]⁺`, the identity holds for `j + k ≥ 1` (`reflectedWalkKernel_apply_pos`), and the boundary state receives the lower tail, `P(j, {0}) = p(−∞, −j]` (`reflectedWalkKernel_apply_zero`); `reflectedWalk_2_28_fails` is an instance with increments `ξ ∈ {−2, 1}` where `P(1, {0}) = 1/2 ≠ p_{−1} = 0`. For the GI/M/1 chain, with `q` the law of the number of service completions possible in one interarrival time, `P(j, {j + 1 − i}) = q{i}` for `i ≤ j` (`giM1Kernel_apply_le`) and `P(j, {0}) = q[j + 1, ∞)` (`giM1Kernel_apply_zero`). |
| p. 45 | "Since `R` is strictly increasing the inverse function `R⁻¹(t)` is well defined for all `t`." | False: for the release rate `r(y) = 1 + y²`, `R(x) = arctan x < π/2` for every level `x` (`releaseTime_one_add_sq`), so `R⁻¹(t)` is undefined for `t ≥ π/2` (`releaseTime_not_surjective`). What the model uses is true: for a positive continuous `r` and `x ≥ 0`, `R` maps `[0, x]` one-to-one onto `[0, R(x)]` (`releaseTime_bijOn`), so `q(x, t) = R⁻¹(R(x) − t)` is well defined for `0 ≤ t ≤ R(x)`. |
| (CSM2), pp. 46, 545 | `Φₙ₊₁ = [Φₙ − Jₙ + Sₙ(Φₙ − Jₙ)]⁺` gives the contents at the times `Tₙ−` immediately before each input. | Release over an interarrival time followed by an input gives the contents just after inputs. With constant release rate `1`, unit inputs and unit interarrival times, (CSM2) moves from `0` to `1` with probability one, while the contents before inputs, the simple storage model, stay at `0` (`contentKernel_ne_storageKernel`). The contents before inputs are given by the input followed by the release (`contentPreInputKernel`). With constant release rate `r ≥ 0`, a level-independent input law and interarrival times on `[0, ∞)`, this is the simple storage model (`contentPreInputKernel_eq_storageKernel`). `contentKernel` is kept as printed. |
| (RT2), pp. 39, 543 | `V⁻(n) := inf(n − Zₘ : Zₘ ≤ n)`, `n ≥ 0`. | For `n < Z₀` there is no renewal at or before `n`, and the infimum is over the empty set (`bwdTime_set_empty`). Since `p(0) = 0`, `Z₀ ≥ 1` even for an undelayed renewal process, so this already happens at `n = 0`, for example for the epochs `Zₘ = m + 1` (`bwdTime_set_empty_example`). `V⁻(n)` is defined from the first renewal on. The results about `V⁻` assume `Z₀ ≤ n` where it matters (`bwdTime_succ_of_not_renewal`). The infimum in (RT1) is always over a nonempty set (`fwdTime_set_nonempty`). |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| (LSS2), pp. 9, 546 | §1.2.2 asks for noise with finite mean and variance; Appendix C asks only for a finite mean. | `HasFiniteMeanVariance` is the stronger form, a finite second moment. The kernels `lssKernel` and `lssMatrixKernel` need no moment condition. |
| (SNSS1), (NSS1), pp. 26, 29 | `F` is smooth on `X × O_w`, with `X` and `O_w` open, and the chain is Markov. | A random recursion is a Markov kernel when `F` is measurable and `Γ` is a probability measure (`isMarkovKernel_recursionKernel`). On second-countable Borel normed spaces a smooth `F`, indeed a continuous one, is measurable (`isMarkovKernel_nssKernel_of_contDiff`). The open sets `X` and `O_w` are not part of the kernel; the control set enters through `HasDensityOnControlSet`. |
| (SETAR1), p. 28 | The regime is `r_{j−1} < Xₙ₋₁ ≤ r_j` for thresholds `−∞ = r₀ < r₁ < ⋯ < r_M = ∞`. | `setarRegime` is defined for any thresholds, as the least index `j` with `x ≤ r_j` (`setarRegime_eq_iff`). It is the book's interval condition when the thresholds are nondecreasing (`setarRegime_eq_iff_Ioc`). |
| (2.2), p. 25 | "When the initial conditions are defined appropriately", `Yₙ = Zₙ + Σⱼ βⱼ Zₙ₋ⱼ` is ARMA(k, ℓ). | No condition on the initial values is needed after `ℓ` steps: if `Z` satisfies (2.2) at every `m ≥ n₀`, then `Y` satisfies (ARMA1) at every `n ≥ n₀ + ℓ` (`arma_of_ar`). |
| p. 36 | The Kalman filter gives `θ̂ₖ`, and the certainty equivalence control gives the closed loop equations (2.22)–(2.24). | The Kalman recursion for `θ̂ₖ₊₁` is taken as given; (2.22)–(2.23) then follow from (2.20)–(2.21) and `Uₖ = −θ̂ₖYₖ` by algebra (`sac_closed_loop`), and (2.24) is the `Σ` recursion of the filter (`sacStep`). |
| (2.25), p. 36 | `Φₖ = (Σₖ, θ̃ₖ, Yₖ)` is a Markov chain on `X = [σ_z², σ_z²/(1 − α²)] × ℝ²`. | `X` is invariant when `\|α\| < 1` and `σ_w ≠ 0`: from `Σ ∈ [σ_z², σ_z²/(1 − α²)]` the next `Σ` stays in the interval (`sacStep_sigma_mem`), and the chain started in `X` is in `X` at the next step with probability one (`sacKernel_apply_Icc`). The kernel `sacKernel` is defined on all of `ℝ³`. |
| (SAC2), pp. 35, 549 | Gaussian noises with variances `σ_z²`, `σ_w²`; Appendix C adds `σ_z < 1`. | `SatisfiesSAC2` is `0 < σ_z < 1` and `0 < σ_w`: the noises are non-degenerate. |
| p. 38 | "It is customary to assume that `p(0) = 0`." | Assumed where it is used: the renewal process moves up at every step when `p{0} = 0` (`renewalKernel_apply_Ioi`), and `Zₙ ≥ n` holds for strictly increasing epochs (`le_renewal`). The pathwise dynamics of `V⁺` on p. 39 are proved for strictly increasing epochs (`fwdTime_succ_of_one_lt`, `fwdTime_succ_of_eq_one`). |
| (2.28), pp. 41–43 | The chain `Nₙ` of the GI/M/1 queue and `N*ₙ` of the M/G/1 queue. | `giM1Kernel q` takes as data the law `q` of the number of service completions possible in one interarrival time, and `mG1Kernel a` the law `a` of the number of arrivals in one service time. Under (Q4) and (Q5) these are mixed Poisson laws; that derivation, from the continuous-time queue, is not formalised. |
| pp. 42–43 | `P(S > T + z \| S > z) = ∫ e^{−μt} G(dt)`. | `expMeasure_prod_lt` takes `S` and `T` independent (the product law) and interarrival times non-negative, `G(−∞, 0) = 0`. The memoryless property is proved for `t, z ≥ 0` (`expMeasure_memoryless`). |
| p. 44 | The mean input `α = ∫ x H(dx)` and mean output `β = ∫ rx G(dx)`. | `storage_mean_increment` assumes `H` and `G` integrable. |
| (2.32), p. 45 | `R(x)` is finite for all `x`, and `R` is strictly increasing. | The release rate `r` is positive and continuous on `ℝ` (`continuous_releaseTime`, `releaseTime_strictMono`, `releaseTime_strictMonoOn`, `releaseTime_bijOn`). |
| (CM2), (CM3), pp. 548–549 | "For each initial condition `x₀⁰ ∈ ℝ`", also for the multidimensional model in (CM3). | The state space is meant: `SatisfiesCM3` quantifies over `x₀ ∈ ℝⁿ`. |
| (DBL2), p. 32 | `Z` and `W` are mutually independent. | Independence is built into `dblKernel` through the product law `Γz ⊗ Γw`; `SatisfiesDBL2` holds the conditions on densities and moments. |
| (1.14), (1.15), p. 16 | `V` is finite `φ`-almost everywhere; `P^∞(C) > 0` is a number attached to `C`. | `SatisfiesDrift` takes `V : X → [0, ∞]` with no finiteness condition; `IsLocallyConvergent` asks for some constant `c > 0` in place of `P^∞(C)`. |

## Conventions

* Every model is a Mathlib `Kernel X X`. Most are `recursionKernel Γ F`, the image of
  `Kernel.id ×ₖ Kernel.const X Γ` under `F`, so that `P(x, A) = Γ{w : F(x, w) ∈ A}`. The book's
  noise and initialization conventions (p. 22) are realized by driving the recursion with an
  i.i.d. sequence `ω ~ Γ^{⊗ℕ}` (Mathlib's `Measure.infinitePi`) from a fixed start `x`
  (`law_orbit`); an initial law `μ` enters as `μ.bind P`. `orbit` follows the book's indexing,
  `Φₙ₊₁ = F(Φₙ, ωₙ₊₁)`, so the coordinate `ω₀` is unused.
* Independent noises are encoded by product laws: `H ⊗ G` for service (or input) and interarrival
  times in `waitingTimeKernel` and `storageKernel`, `Γz ⊗ Γw` in `dblKernel`, `ΓΓ ⊗ ΓW` in
  `rcaKernel`, and `⊗ⱼ Γ j`, one noise per regime, in `setarKernel`, whose kernel uses only the
  noise of the current regime (`setarKernel_apply'`). The zero-mean condition of (SETAR1) is
  `SatisfiesSETAR1Noise`, separate from the kernel.
* State spaces: `ℤ₊` is `ℕ`; the half line `[0, ∞)` is `ℝ≥0` (half-line walk, waiting time,
  storage); `ℝⁿ` is `Fin n → ℝ`. LSS(F, G) is defined both for continuous linear maps between
  second-countable Borel normed spaces (`lssKernel`) and for matrices (`lssMatrixKernel`).
* AR(k), ARMA(k, ℓ) and NARMA(k, ℓ) act on lag vectors updated by `shiftIn`; the state before the
  step at time `n` is `(Yₙ₋₁, …, Yₙ₋ₖ)` (and `(Wₙ₋₁, …, Wₙ₋ℓ)`), and sequences in `arVec` and
  `arma_of_ar` are indexed by `ℤ`.
* SETAR has `m + 1` regimes indexed `0, …, m` and finite thresholds `r₀, …, r_{m−1}`; these are
  the book's `r₁, …, r_{M−1}` with `M = m + 1`.
* The dependent parameter bilinear model has state `(θ, Y)` (see above).
* Real division follows Lean's convention `x/0 = 0`, in `gumleafMap` (`F(a, b) = (1/a − 1/b, a)`)
  and in `sacStep`. `hazard` is computed in `[0, ∞]`, where `0/0 = 0`: an age `j` with
  `p(j, ∞) = 0` has hazard `0`, and from it the age chain moves up by one.
* The infimum of an empty set is `0` in `ℕ` and in `ℝ`; `bwdTime`, `fwdTimeCts` and `bwdTimeCts`
  take that value where their set is empty. `fwdTimeCts` and `bwdTimeCts` follow (RT3)–(RT4)
  literally, with `n ≥ 1`.
* The forward recurrence time kernel is defined on all of `ℕ`: from `0`, as from `1`, the chain is
  renewed with law `p` (`fwdStep`). From an empty queue the M/G/1 chain moves as from one customer
  (`mG1Kernel_zero`).
* `IsSmallSet` uses the minorization `Pᵐ(x, ·) ≥ ν` with `ν ≠ 0`, which the book defines in
  Chapter 5; §1.3 uses the word only in quotation marks.
* The hitting time `τ_A` takes values in `ℕ∞`; expectations of `τ_A` are lower Lebesgue integrals.
  The sets `Oₙ` of (1.10) are a parameter of `IsNonEvanescent`. `IsTightChain` takes `ε` in
  `[0, ∞]`. `tvDist` is the supremum over measurable sets of `\|μ(A) − ν(A)\|`.
* `IsWeakFeller` asks that `Pf` be continuous for every bounded continuous `f : X → ℝ`.
  `IsLyapunovStable` is the book's `lim sup_{y → x} sup_k d(Tᵏy, Tᵏx) = 0` in `ε`–`δ` form, and
  `IsLagrangeStable` asks that the closure of each orbit be compact.
* `pathMeasure` is Mathlib's `Kernel.traj`, as in `RecursiveMethods/LawsOfLargeNumbers` of this
  repository, from which the definition is copied.
* Exponential laws are Mathlib's `expMeasure`, Gaussian laws `gaussianReal`. `HasStableEigenvalues`
  is stated through the spectrum of `F` as a complex matrix.
* Figure 1.1 is formalised through its matrix: the squared Euclidean norm `sqNorm2` contracts by
  `0.992416` under `F`, so paths of `F` tend to `0` and paths of `F⁻¹` from `x ≠ 0` tend to
  infinity. The plotted paths are not formalised.
* The birth–death chain (`birthDeathKernel`) is not in Chapters 1–2; it is included for the later
  chapter projects, and is a Markov kernel when `bᵢ + dᵢ ≤ 1` (`isMarkovKernel_birthDeathKernel`).

## Not formalised

* **Theorems 1.3.1 and 1.3.2.** They are forward references: Theorem 1.3.1 is proved in
  Chapter 13, Theorem 1.3.2 in Chapters 6 and 18. Their conditions are defined here (§1.3 of the
  [source map](source-map.md)).
* **Heuristic stability claims proved in later chapters.** That a stable LCM(F, G) with reasonable
  noise gives a stable LSS(F, G) (p. 10); when ruin is certain for random walk (p. 12); the
  equivalence of (1.8) with non-evanescence and of (1.9) with tightness for T-chains, and the
  agreement of (1.8) and (1.9) for deterministic models (p. 15); the identification of Lagrange
  stability of `μ ↦ μP` with tightness (p. 17); that φ-irreducibility on a countable space is
  irreducibility (p. 14); ergodicity for `\|α\| < 1` and evanescence for `\|α\| > 1` in the
  simple linear model (p. 23); the path structure of the gumleaf model (p. 31, Chapter 7); the
  mean square performance of the simple adaptive control model (p. 37, Chapter 16); the stability
  of the recurrence time chains (p. 39); the role of `α/β` in the storage model (p. 44).
* **The ARX and adaptive control material (2.16)–(2.19).** The ARX model, sample mean square
  stabilizing inputs and minimum variance control laws (§2.3.1), the control (2.18) with known
  parameters, and the stochastic gradient algorithm (2.19) with its Markov state (pp. 34–35).
* **Kalman optimality.** That the filter recursion of p. 36 computes `θ̂ₖ = E[θₖ \| 𝒴ₖ]` and
  `Σₖ = E[θ̃ₖ² \| 𝒴ₖ]` under Gaussian initial conditions. The recursion itself is used as given.
* **The continuous-time queue.** The process `N(t)`, the epochs (2.26)–(2.27) and Figure 2.7; the
  derivation of the GI/M/1 and M/G/1 chains from it under (Q4) and (Q5), including the mixed
  Poisson laws of the number of departures and arrivals; that `N` is not Markov for a general
  GI/G/1 queue (only the inequality (2.30) for a deterministic service time is proved,
  `dirac_not_memoryless`). Likewise the storage process in continuous time and the claim that it
  is not Markov when sampled at other times (p. 44), and the state-dependent queues of pp. 46
  and 545.
* **The simulation figures.** The sample paths of Figures 1.1–1.3, 2.1–2.6 and 2.8.
* **The Markov property (1.1)** and the strong Markov property are Chapter 3's (project
  `TransitionProbabilities`). Here the recursions are shown to have the right `n`-step laws
  (`recursionKernel_pow_apply`, `law_orbit`).
* **§1.1, §1.4 and §2.5** (except the residual-service remark of p. 47), and the chapter
  introductions apart from the conventions of p. 22.
