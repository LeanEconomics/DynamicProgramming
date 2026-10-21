# Meyn and Tweedie, Chapters 1–2: Markov Models, in Lean

This is the `StochasticStability/MarkovModels` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapters 1–2 and Appendix C of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd
edition (Cambridge University Press, 2009), and it is the model library that the later chapter
projects copy from. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 1 introduces Markov chains through linear control and state space models and random
walks, and previews the book's stability notions and two of its main theorems. Chapter 2
introduces the models the book returns to throughout: linear and nonlinear time series and state
space models, adaptive control, renewal processes, queues and storage models. Appendix C collects
their assumptions. Every model is defined here as a Mathlib Markov kernel, most of them as an
instance of one random recursion `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)` (`recursionKernel`), and the facts the text
states about the models are proved. Every assumption of Appendix C has a Lean counterpart, a
model definition or a predicate on the model data, and the stability notions of §1.3 are defined,
so that later chapters can state their results against them. The chapters have no numbered
results apart from Theorems 1.3.1 and 1.3.2, which are previews of results proved in Chapters 13,
6 and 18. Six claims are false as printed.
Each is refuted in Lean by a counterexample, and a corrected statement is proved: the state order
in (2.15); the transformed gumleaf recursion (2.11); (2.28) read for every `k ≥ −j`; the claim
that `R⁻¹(t)` is defined for all `t` (p. 45); the order of release and input in (CSM2); and the
infimum in (RT2), which is over an empty set before the first renewal. The ARX and adaptive
control material (2.16)–(2.19), the optimality of the Kalman filter, the continuous-time queue and
the simulation figures are not formalised. See [corrections](docs/corrections.md). The library
contains **203 theorems**.

* **Random recursions** (§1.2.2, §2.2, p. 22). The kernel `P(x, A) = Γ{w : F(x, w) ∈ A}` of a
  recursion driven by i.i.d. disturbances, and its control maps `Fₖ` of (2.5). The `n`-step
  kernel is the image of `Γ^{⊗n}` under `Fₙ(x, ·)`, and the path driven by an i.i.d. sequence has
  law `Pⁿ(x, ·)` (`recursionKernel_pow_apply`, `law_orbit`). A recursion that ignores its noise is
  the deterministic system (1.3).
* **Linear models** (§1.2.2, §2.1). LSS(F, G) on normed spaces and with matrices, with the closed
  form of its paths and its `n`-step laws; the control model LCM(F, G) and controllability.
  Figure 1.1: `F = I + ΔA` contracts `|x|²` by `0.992416`, so its paths spiral in and those of
  `F⁻¹` spiral out. AR(1) as LSS(α, 1) and random walk as LSS(1, 1); AR(k) in the state space form
  (2.1); ARMA(k, ℓ), and the low-dimensional realization `Yₙ = Zₙ + Σ βⱼ Zₙ₋ⱼ` of p. 25.
* **Random walks** (§1.2.3). Random walk on any measurable additive commutative monoid, with
  `Pⁿ(x, ·)` the convolution power `Γ^{n∗}` shifted by `x`; spread out increments (RW2); random
  walk on a half line, held at zero with probability `Γ(−∞, −x]`, with Lindley's representation
  of its paths.
* **Nonlinear state space models** (§2.2). NSS(F) and SNSS(F); the simple bilinear model; SETAR,
  whose map need not be continuous; NARMA, with ARMA as its linear case; the gumleaf attractor,
  with the squashing map onto the open unit disk and the corrected (2.11); the dependent parameter
  bilinear model with the corrected (2.15); the random coefficient autoregression.
* **Adaptive control** (§2.3). The closed loop equations (2.22)–(2.23) derived from (2.20)–(2.21),
  the Kalman filter recursion and the certainty equivalence control, with the `Σ` recursion
  (2.24); the closed loop chain (2.25) stays in `[σ_z², σ_z²/(1 − α²)] × ℝ²`; recursive least
  squares as a special case.
* **Regenerative models** (§2.4). The renewal process and `P(Z_k = n) = a ∗ p^{k∗}(n)` through
  generating functions; the forward and backward recurrence time chains, as kernels and pathwise;
  the GI/M/1 queue at arrivals and the M/G/1 queue at departures, with the memoryless property
  and the corrected (2.28); random walk on `ℤ₊`; the Moran dam as random walk on a half line with
  mean increment `α − β`, and as the GI/G/1 waiting time chain when `r = 1`; the content-dependent
  storage model, with the release time `R` and the corrected (CSM2).
* **Stability notions** (§1.3). The path measure `Pₓ`, hitting times, φ-irreducibility (I),
  (1.8)–(1.11), the conditions (1.12)–(1.16) of Theorem 1.3.1, the Feller property of
  Theorem 1.3.2, and the four dynamical-system notions of §1.3.2 with the example `x ↦ x + 1`.
* **Appendix C**. (Q4)–(Q5), (LSS2)–(LSS5), (DS1)–(DS2), (SNSS2)–(SNSS3), (NSS2)–(NSS3),
  (CM2)–(CM3), (SAC2), (SETAR1)–(SETAR3), (SBL2), (DBL2) and (RCA2)–(RCA3) as predicates; the
  remaining items are the model definitions above.

All names are in the namespace `MeynTweedie.MarkovModels`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Recursion](MarkovModels/Recursion.lean) | 18 | The kernel of a random recursion, control maps (2.5), sample paths, `n`-step laws |
| [RandomWalk](MarkovModels/RandomWalk.lean) | 19 | (RW1), (RW2), (RWHL1): random walk, convolution powers, the half line, Lindley's representation |
| [LinearModels](MarkovModels/LinearModels.lean) | 39 | LSS(F, G), LCM(F, G), Figure 1.1, AR(1), AR(k) and (2.1), ARMA(k, ℓ) |
| [NonlinearModels](MarkovModels/NonlinearModels.lean) | 41 | NSS(F), bilinear, SETAR, NARMA, gumleaf, dependent parameter bilinear, SAC, RCA |
| [CountableModels](MarkovModels/CountableModels.lean) | 9 | Random walk on `ℤ₊` and the correction to (2.28); the birth–death chain |
| [Queues](MarkovModels/Queues.lean) | 16 | The GI/G/1 waiting time, GI/M/1 and M/G/1 chains; the memoryless property |
| [Storage](MarkovModels/Storage.lean) | 18 | (SSM1)–(SSM2), (2.31)–(2.33), (CSM1)–(CSM2) and their corrections |
| [Renewal](MarkovModels/Renewal.lean) | 29 | Renewal processes, convolutions, (RT1)–(RT4) |
| [Assumptions](MarkovModels/Assumptions.lean) | 4 | Appendix C: the further model assumptions as predicates |
| [Stability](MarkovModels/Stability.lean) | 10 | §1.3: the path measure, hitting times and the stability notions |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
