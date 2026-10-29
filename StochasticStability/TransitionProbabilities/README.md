# Meyn and Tweedie, Chapter 3: Transition Probabilities, in Lean

This is the `StochasticStability/TransitionProbabilities` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 3 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 48–74. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 3 lays the foundations of the book: a Markov chain is built from an initial law and a
transition kernel, and the transition kernels of the models of Chapter 2 are computed. On a
countable space the chain is given by a transition matrix, through its finite-dimensional
distributions (3.4) (§3.2). The matrices of §3.3 are those of the forward and backward recurrence
time chains, random walk on `ℤ` and on `ℤ₊`, the integer storage model, the GI/M/1 queue at
arrivals, the M/G/1 queue at departures, and the linear model on `ℚ`. On a general space,
Theorem 3.4.1 builds the law `P_μ` of the chain on path space from the kernel `P`. §3.4 then
develops the `n`-step kernels and the Chapman–Kolmogorov equations, skeletons and resolvents,
the Markov property, occupation, hitting and return times, taboo probabilities and the strong
Markov property. §3.5 computes kernels on general spaces: random walk on a half line, storage
models, renewal processes and the `δ`-skeletons of their recurrence time processes, the ladder
chain of the GI/G/1 queue, and the nonlinear state space model.

Every numbered result is formalised: Theorems 3.2.1, 3.4.1 and 3.4.2 and Propositions 3.3.1–3.3.3
and 3.4.3–3.4.6, together with the numbered equations and the claims the text makes about its
models. Where the book says that a chain "can be constructed", is "clearly" Markov or is "easy to
verify" to be Markov, the claim is proved from the primitives of the model: i.i.d. noise for the
recursions, the renewal sequence for the `δ`-skeletons, and the interarrival and service times for
the GI/G/1 ladder chain. Six claims are false as printed. Each is refuted in Lean by a
counterexample, and a corrected statement is proved: the displayed matrix of the backward
recurrence time chain (p. 55); the sign of the increment law of the integer storage model (p. 56)
and of (3.37); the index in (3.18); the sign of `δ − x` in (3.39); and the normalisation in the
backward-chain display of p. 70. Six further points are corrected without a counterexample: the
range `j ≥ 1` in (3.19); the meaning of (3.32) "on the set `{ζ < ∞}`"; `P_x(Φ₀ = x) = 1`, which
is an event only when singletons are measurable; the reflected differential in the p. 70 display;
the label "(3.41)" used for (3.40) on p. 71; and the GI/G/1 "total residual service time", which
the construction does not use. No result needs a countably generated σ-algebra: the chain exists,
and the Markov and strong Markov properties hold, on every measurable space. Both properties hold
for every integrable functional of the future, not only for bounded ones. The δ-skeletons and the
GI/G/1 chain need positivity conditions that the book leaves implicit. The following are not
formalised: the backward recurrence time skeleton started from a general age, the converse of the
countable-space definition (from (3.3) to a Markov chain), the notational conventions of
pp. 50 and 62–63, and the commentary of §3.6. See [corrections](docs/corrections.md). The library
contains **517 theorems**. Of these, 369 are in the Chapter 3 modules and 148 in the modules
carried from Chapters 1–2.

Four pieces of general infrastructure are built here.

* **The strong Markov property** (`StrongMarkov`). Mathlib has none. For a stopping time `ζ` of
  the natural filtration, `𝓕_ζ^Φ` is identified with the book's σ-algebra
  (`measurableSet_stoppedField_iff`), and the post-`ζ` path has, on `{ζ < ∞}` and given `𝓕_ζ^Φ`,
  the law `P_{Φ_ζ}`: as an identity of measures (`strong_markov_measure`), for nonnegative
  functionals (`strong_markov_lintegral`, `strong_markov_lintegral_mul`), for integrable ones
  (`strong_markov_setIntegral`), and as the conditional expectation (3.32)
  (`strong_markov_property`). Proposition 3.4.6 is `proposition_3_4_6`.
* **The Markov property for integrable functionals of the whole future** (`MarkovProperty`).
  `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]` for every measurable `H` on path space with `θⁿH` integrable
  (`markov_property`), from the identity of measures `markov_measure`. The book's bounded case is
  `markov_property_bdd` and `proposition_3_4_3`.
* **Recursions driven by i.i.d. noise are Markov** (`ModelKernels`). If `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` with
  `W₁, W₂, …` i.i.d. and independent of `X₀`, then `X` is a Markov chain with kernel
  `P(x, A) = Γ{w : F(x, w) ∈ A}` (`isMarkovChain_of_iid`), on any probability space. Every model
  of §§3.3 and 3.5 that is a recursion gets its Markov property from this theorem.
* **Regeneration at random indices** (`Regeneration`). An i.i.d. sequence starts afresh after a
  random index determined by its past (`lintegral_regeneration`), and a process that is a function
  of its past and of such a fresh future is a Markov chain (`isMarkovChain_of_regeneration`). The
  `δ`-skeletons of §3.5.3 and the GI/G/1 ladder chain of §3.5.4 are Markov by this lemma.

The library covers the chapter as follows.

* **Path space and Theorem 3.4.1** (§3.1, §3.4.1). The path measures `P_x` and `P_μ` on
  `Ω = ℕ → X`, built by the Ionescu-Tulcea theorem (`pathKernel`, `pathMeasure`), with the mixture
  formula `P_μ = ∫ P_x μ(dx)` and (3.1). A Markov chain is a process whose finite-dimensional
  distributions are (3.20) (`IsMarkovChain`). Theorem 3.4.1: the coordinate process under `P_μ` is
  one, and `P_μ` is the only law on path space with these finite-dimensional distributions. The
  three kinds of state space of §3.1 are defined, and no result uses them.
* **Countable spaces** (§3.2, §3.3). Transition matrices, their powers and their kernels;
  Theorem 3.2.1 with (3.4), (3.5) and (3.8); (3.3) for every chain with a transition matrix. The
  forward and backward recurrence time matrices, random walk on `ℤ` and `ℤ₊`, the integer storage
  increment, and Propositions 3.3.1–3.3.3, each also derived from the recursion that defines the
  model. The Poisson counts (3.14)–(3.19) are proved, not cited: the number of exponential
  services completed by time `t` is Poisson with parameter `μt`.
* **Kernels** (§3.4.2). `Pⁿ`, (3.21)–(3.22) and Theorem 3.4.2; skeletons, sampled kernels and
  resolvents (3.25)–(3.26); the operators `Pf` and `μP`, with `P^{m+n} = PᵐPⁿ`; `I_B` and the
  potential kernel `U` (3.30).
* **Markov property** (§3.4.2). The shift `θⁿ`, (3.8) and (3.24), the Markov property (3.28) and
  Proposition 3.4.3. A process whose one-step conditional laws are given by a kernel is a Markov
  chain (`isMarkovChain_of_step`), so the `m`-skeleton is a Markov chain with kernel `Pᵐ`.
* **Hitting times** (§3.4.3). `η_A`, `τ_A`, `σ_A`, `τ_A(k)` and `L(x, A)`; Proposition 3.4.4
  (stopping times), Proposition 3.4.5, the operator forms with `P I_{Aᶜ}`, the first-step equation
  for `L`, the taboo probabilities (3.33) and the taboo potential `U_A` (3.34) with
  `U_A(x, A) = L(x, A)`.
* **Strong Markov property** (§3.4.3). See above.
* **Kernels of specific models** (§§3.5.1–3.5.2, §3.5.5). (3.35)–(3.36) for random walk on a half
  line; the corrected (3.37) for the storage model; the kernel `Ph(x) = ∫ h(F(x, w)) Γ(dw)` of
  SNSS(F) and its `k`-step form (3.44). Random walk on `ℝ` and on a half line, AR(1), LSS(F, G),
  the GI/G/1 waiting time and the storage model are Markov chains by `isMarkovChain_of_iid`.
* **Renewal processes** (§3.5.3). The delayed renewal process is a random walk with
  `P(Zₙ ∈ ·) = Γ₀ ∗ Γ^{n∗}`; (3.38); the renewal measure `U` and the expected numbers of renewals.
  The forward and backward recurrence time `δ`-skeletons are Markov chains for every increment
  law on `[0, ∞)` not concentrated at `0`, with the corrected (3.39) and the corrected backward
  display of p. 70.
* **Ladder chains and the GI/G/1 queue** (§3.5.4). The ladder kernel (3.40), its translation
  invariance and skip-free structure; (3.41)–(3.43); the GI/G/1 kernel is Markov, by the strong law
  of large numbers. The queue is built from its interarrival and service times, and
  `Φₙ = (Nₙ, Rₙ)` is a Markov chain with the ladder kernel (`gig1_isMarkovChain`).

All names are in the namespace `MeynTweedie.TransitionProbabilities`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [StateSpaces](TransitionProbabilities/StateSpaces.lean) | 2 | §3.1: countable, general and topological state spaces |
| [PathSpace](TransitionProbabilities/PathSpace.lean) | 23 | `P_x`, `P_μ`, (3.1), `𝓕ₙ^Φ`, (3.20), `IsMarkovChain`, Theorem 3.4.1 with uniqueness |
| [CountableChains](TransitionProbabilities/CountableChains.lean) | 13 | §3.2: (3.3)–(3.8), Theorem 3.2.1 |
| [SpecificMatrices](TransitionProbabilities/SpecificMatrices.lean) | 21 | §3.3: (3.9)–(3.15), (3.19), Propositions 3.3.1–3.3.3; the corrections of pp. 55–56 |
| [PoissonCounts](TransitionProbabilities/PoissonCounts.lean) | 12 | (3.14)–(3.19) from exponential services; the correction to (3.18) |
| [Kernels](TransitionProbabilities/Kernels.lean) | 32 | (3.21)–(3.26), Theorem 3.4.2, `Pf`, `μP`, `I_B`, `U` (3.30) |
| [MarkovProperty](TransitionProbabilities/MarkovProperty.lean) | 22 | The shift, (3.8), (3.24), (3.28), Proposition 3.4.3, skeletons |
| [HittingTimes](TransitionProbabilities/HittingTimes.lean) | 36 | (3.29)–(3.31), (3.33)–(3.34), Propositions 3.4.4–3.4.5 |
| [StrongMarkov](TransitionProbabilities/StrongMarkov.lean) | 20 | `𝓕_ζ^Φ`, `Φ_ζ`, `θ^ζ`, (3.32), Proposition 3.4.6 |
| [ModelKernels](TransitionProbabilities/ModelKernels.lean) | 19 | §3.5.5: the SNSS(F) kernel, (3.44), i.i.d. noise makes a recursion Markov |
| [SpecificKernels](TransitionProbabilities/SpecificKernels.lean) | 42 | §§3.3 and 3.5.1–3.5.3 from the recursions: (3.35)–(3.39), the corrections to (3.37) and (3.39) |
| [Regeneration](TransitionProbabilities/Regeneration.lean) | 12 | Regeneration of an i.i.d. sequence at a random index |
| [RenewalSkeletons](TransitionProbabilities/RenewalSkeletons.lean) | 53 | §3.5.3: the `δ`-skeletons `V⁺_δ`, `V⁻_δ`, (3.39), the backward display of p. 70 |
| [LadderChains](TransitionProbabilities/LadderChains.lean) | 25 | §3.5.4: (3.40)–(3.43), the GI/G/1 ladder kernel |
| [GIG1Embedding](TransitionProbabilities/GIG1Embedding.lean) | 37 | §3.5.4: the GI/G/1 queue at arrivals is a Markov chain with the ladder kernel |

Carried from the Chapters 1–2 project `MarkovModels` (148 theorems), identical except for the
namespace, the module names and a note in each module docstring:

* `ModelRecursion` (18): the kernel `recursionKernel` of a random recursion, the control maps
  `Fₖ` of (2.5) and the `n`-step law, used in §3.5.5.
* `ModelRandomWalk` (19): random walk, convolution powers, random walk on a half line, used in
  §§3.3.2, 3.5.1 and 3.5.3.
* `ModelLinearModels` (39): AR(1) and LSS(F, G), used in §3.3.4 and for the linear models of
  `SpecificKernels`.
* `ModelCountableModels` (9): random walk on `ℤ₊`, the kernel of the matrix (3.12)–(3.14).
* `ModelQueues` (16): the GI/G/1 waiting time, GI/M/1 and M/G/1 kernels and the memoryless
  property, used in §§3.3.3 and 3.5.2.
* `ModelStorage` (18): the simple storage model, used in §3.5.2.
* `ModelRenewal` (29): the renewal process and the recurrence time processes (RT3)–(RT4), used in
  §3.5.3.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
