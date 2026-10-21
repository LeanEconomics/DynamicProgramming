# Meyn and Tweedie, Chapter 6: Topology and Continuity, in Lean

This is the `StochasticStability/TopologyContinuity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 6 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 123–145. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 6 puts a topology on the state space and asks how the transition law fits it. A chain is
weak Feller if `P(·, O)` is lower semicontinuous for every open `O`, and strong Feller if `P` maps
bounded measurable functions to continuous ones. A continuous component of a sampled kernel `K_a`
is a substochastic kernel `T ≤ K_a` with every `T(·, A)` lower semicontinuous, and a T-chain is a
chain with a continuous component that is non-trivial at every point. §6.1 gives the equivalent
forms of the Feller properties (Proposition 6.1.1), shows that the nonlinear state space model and
the random walk are weak Feller (Propositions 6.1.2–6.1.3), and relates reachable points to the
support of the maximal irreducibility measure (Lemma 6.1.4). §6.2 shows that an open set
irreducible T-chain is ψ-irreducible (Proposition 6.2.2), that a chain is a T-chain if every
compact set is petite and that every compact set is petite for a ψ-irreducible T-chain (Theorem
6.2.5), and that a ψ-irreducible weak Feller chain whose `supp ψ` has non-empty interior is a
T-chain (Theorem 6.2.9). §6.3 finds continuous components for random walk, for the linear state
space model and for the SETAR model. §6.4 introduces e-chains, the chains whose iterates `Pᵏf` are
equicontinuous on compact sets, and links them, and boundedness in probability, to the stability
of the dynamical systems `(P, M, d_m)` and `(P, C(X), d_c)`.

Every numbered result is formalised: Theorem 6.0.1, Propositions 6.1.1–6.1.3 and 6.1.5–6.1.6,
Lemma 6.1.4, Propositions 6.2.1–6.2.4, 6.2.6 and 6.2.8, Theorems 6.2.5 and 6.2.9, Lemma 6.2.7,
Propositions 6.3.1–6.3.3 and 6.3.5–6.3.6, Lemma 6.3.4 and Propositions 6.4.1–6.4.6, together with
the claims the text makes about its examples. Proposition 6.4.3, whose proof the book omits, is
proved. Three claims are false as printed. Each is refuted in Lean by a counterexample, and a
corrected statement is proved. Proposition 6.4.2 fails: a weak Feller chain with `Pᵏ(x, ·) → δ₀`
for every `x` need not be an e-chain, because pointwise convergence to a continuous limit does not
give equicontinuity. It holds when the convergence is uniform on compact sets. Lemma 6.1.4 needs
`ψ` maximal, and the lower bound in (6.15) needs `ρ₁ ≥ 0`. The claim after Theorem 6.2.9 that a
`δ₀`-irreducible weak Feller chain need not be a T-chain is proved, for the book's example on `ℝ`
instead of `[0, 1]`. Each result assumes only the topology it uses: first countability,
pseudo-metrizability, second countability, local compactness or the Hausdorff property, in place
of the book's locally compact separable metric space; some also need a countably generated
σ-algebra. Proposition 6.4.4 assumes a complete metric, and Proposition 6.4.3 states the condition
on the functions `fⱼ` of (6.16) that the book leaves open. The following are not formalised: the
multiplicative random walk of pp. 143–144, which the book only sketches; the storage-model remark
after Proposition 6.3.1; the remarks on ARMA models and controllable subspaces after Proposition
6.3.3 (AR(k) is formalised); the strong Feller property of the Gaussian linear model (p. 137); the
weakened support conditions after Proposition 6.3.6; the remarks on the instability and the
continuous components of the example (6.1)–(6.2); and the commentary of §6.5. Five devices of the
book's proofs are replaced by other arguments: the compact inner approximation in Lemma 6.2.7, the
minimum of the boundary measures in Proposition 6.3.6, the scalar-noise change of variables in
Proposition 6.3.3, Theorem D.4.1 and Lemma D.4.3. The proof of Proposition 6.4.4, which covers
only orbits of point masses, is completed for every initial law. See
[corrections](docs/corrections.md). The library contains
**837 theorems**. Of these, 130 are in the Chapter 6 modules and 707 in the modules carried from
Chapters 1–5.

Four results carry the chapter.

* **Lower semicontinuity of Feller integrals** (`FellerChains`). For a weak Feller chain on a
  first-countable space, `x ↦ ∫ f(y) P(x, dy)` is lower semicontinuous for every lower
  semicontinuous `f ≥ 0` (`IsWeakFeller.lowerSemicontinuous_lintegral`). The proof is Fatou's
  lemma along a sequence of measures for a lower semicontinuous integrand
  (`lintegral_le_liminf_of_lsc`, the layer-cake argument of Mathlib's portmanteau theorem); it
  replaces the approximation of lower semicontinuous functions by continuous ones (Theorem D.4.1)
  in the book's proof of Proposition 6.1.1. Everything else in §6.1 follows: `Pⁿ` and `K_a` are
  weak Feller (`IsWeakFeller.pow`, `IsWeakFeller.isWeakFeller_sampledKernel`), `K_a(·, F)` is upper
  semicontinuous for closed `F` (`IsWeakFeller.usc_sampledKernel_closed`), `Pₓ(τ_C ≥ k)` and
  `Eₓ[m(τ_C)]` are lower semicontinuous for closed `C` (`proposition_6_1_1_ii_tail`,
  `proposition_6_1_1_ii`), and `Pₓ(τ_O ≤ n)`, `K_a(x, O)` and `L(x, O)` are lower semicontinuous
  for open `O` (`proposition_6_1_1_iii`), a part whose proof the book omits.
* **Compact petite sets and T-chains** (`TChains`, `CompactPetite`). Theorem 6.2.5
  (`theorem_6_2_5_i`, `theorem_6_2_5_ii`): on a locally compact second-countable space a chain
  whose compact sets are petite is a T-chain, and every compact set is petite for a ψ-irreducible
  T-chain. For a ψ-irreducible weak Feller chain, the closure of a petite set is petite
  (`lemma_6_2_7`), and if `supp ψ` has non-empty interior, the Baire category theorem gives an open
  petite set of positive measure, so every compact set is petite (`proposition_6_2_8_ii`) and the
  chain is a T-chain (`theorem_6_2_9`). The hypothesis on `supp ψ` cannot be dropped: the halving
  chain `jumpKernel 2⁻¹` is weak Feller and `δ₀`-irreducible but not a T-chain
  (`feller_not_tChain_counterexample`). Theorem 6.0.1 collects these results (`theorem_6_0_1`).
* **Linear models for every noise dimension** (`TChainModels`, `LinearTChains`). Proposition 6.3.3
  (`proposition_6_3_3`): a controllable LSS(F, G) model whose noise law is not singular with
  respect to Lebesgue measure has an everywhere non-trivial continuous component for its
  `n`-skeleton. The book proves the case `p = 1` with the determinant of `Cₙ`. Here the component is
  the translate by `Fⁿx` of the law of `Cₙ(W₁, …, Wₙ)` for the absolutely continuous part of `Γ`;
  this law is absolutely continuous because `Cₙ` is onto, and its translates are lower
  semicontinuous in measure (`lsc_translate`). With Gelfand's formula for the spectral radius
  (`lemma_6_3_4`) and the uniform reachability estimate `lss_uniform_reach`, LSS(F, G) under (LSS4)
  and (LSS5) is a ψ-irreducible T-chain whose compact sets are small (`proposition_6_3_5`).
* **e-chains and the two dynamical systems** (`EChains`, `EChainsStability`). Proposition 6.4.2 is
  refuted by the doubling chain `jumpKernel 2` (`proposition_6_4_2_counterexample`) and proved
  under uniform convergence on compact sets (`proposition_6_4_2_corrected`). Proposition 6.4.3
  (`proposition_6_4_3`): with `d_m` built from compactly supported `fⱼ` that approximate every
  compactly supported `f` in the sup norm, a chain is an e-chain if and only if `(P, M, d_m)` is
  stable in the sense of Lyapunov. The key step is that weak convergence `ν → μ` gives
  `∫ gᵢ dν → ∫ gᵢ dμ` uniformly over a bounded family equicontinuous at every point
  (`eventually_forall_abs_integral_sub_lt`). Proposition 6.4.5 (`proposition_6_4_5`) uses the
  Arzelà–Ascoli theorem in `C(X, ℝ)`, and Proposition 6.4.4 (`proposition_6_4_4`) uses Prokhorov's
  theorem in both directions.

The library covers the chapter as follows.

* **Feller chains, continuous components and T-chains** (Chapter 6 introduction). The definitions
  of p. 124, Theorem 6.0.1, and the example (6.1)–(6.2): it is not weak Feller, and it is
  `δ₀`-irreducible when every `αₙ > 0`.
* **Weak and strong Feller chains** (§6.1.1). Proposition 6.1.1, with the summation-by-parts
  identity for `Eₓ[m(τ_C)]` and the first-step equations for the return and hitting
  probabilities. Random recursions with continuous maps are weak Feller, which gives Proposition
  6.1.2 for NSS(F). Proposition 6.1.3 for the random walk on `ℝ`, with Lemma D.4.3 replaced by the
  continuity of translation in measure.
* **Strong Feller chains and open set irreducibility** (§6.1.2). Reachable points and open set
  irreducibility, Lemma 6.1.4 for maximal `ψ` and the counterexample for the zero measure, the
  countable discrete case, and Propositions 6.1.5–6.1.6.
* **T-chains** (§§6.2.1–6.2.2). Propositions 6.2.1–6.2.4, Theorem 6.2.5 and Proposition 6.2.6. The
  random walk with rational increments is weak Feller and irreducible for no nonzero measure.
* **Feller chains, petite sets and T-chains** (§6.2.3). Lemma 6.2.7, Proposition 6.2.8, Theorem
  6.2.9 and the weak Feller chain that is not a T-chain.
* **Continuous components for specific models** (§6.3). Random walk on a half line (Proposition
  6.3.1); the unrestricted random walk is a T-chain if and only if it is spread out (Proposition
  6.3.2); LSS(F, G) and AR(k) (Proposition 6.3.3); the spectral radius formula and the bounds
  (6.14)–(6.15), the eigenvalue condition (LSS5) and Proposition 6.3.5; the SETAR model
  (Proposition 6.3.6), with Lebesgue measure maximal and every compact set small.
* **e-chains** (§6.4). The map `μ ↦ μP` on probability measures with the topology of weak
  convergence and Proposition 6.4.1; e-chains, Proposition 6.4.2 refuted and corrected; the metric
  `d_m` (6.16), Lyapunov stability and Proposition 6.4.3; boundedness in probability, Lagrange
  stability and Propositions 6.4.4–6.4.5; the simple linear model with `|α| ≤ 1` and the random walk
  are e-chains (Proposition 6.4.6).

All names are in the namespace `MeynTweedie.TopologyContinuity`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [FellerChains](TopologyContinuity/FellerChains.lean) | 40 | §§6.0–6.1: weak and strong Feller chains, lower semicontinuity of Feller integrals, Proposition 6.1.1, reachability and open set irreducibility, Lemma 6.1.4 and its correction, Propositions 6.1.5–6.1.6 |
| [FellerModels](TopologyContinuity/FellerModels.lean) | 12 | §6.1.1: random recursions, Proposition 6.1.2, translation in measure, Proposition 6.1.3, the example (6.1)–(6.2) |
| [TChains](TopologyContinuity/TChains.lean) | 14 | §§6.2.1–6.2.2: continuous components, T-chains, Propositions 6.2.1–6.2.4, Theorem 6.2.5, Proposition 6.2.6 |
| [CompactPetite](TopologyContinuity/CompactPetite.lean) | 16 | §6.2.3: Lemma 6.2.7, Proposition 6.2.8, Theorems 6.2.9 and 6.0.1, the weak Feller chain that is not a T-chain |
| [TChainModels](TopologyContinuity/TChainModels.lean) | 10 | §§6.3.1–6.3.2, 6.3.4: Propositions 6.3.1–6.3.3, AR(k), the rational random walk, Proposition 6.3.6 |
| [LinearTChains](TopologyContinuity/LinearTChains.lean) | 10 | §6.3.3: Lemma 6.3.4, (6.14)–(6.15) and the correction to (6.15), (LSS5), Proposition 6.3.5 |
| [EChains](TopologyContinuity/EChains.lean) | 16 | §6.4: Proposition 6.4.1, e-chains, Proposition 6.4.2 refuted and corrected, Proposition 6.4.6, boundedness in probability, Lagrange stability, Proposition 6.4.4 |
| [EChainsStability](TopologyContinuity/EChainsStability.lean) | 12 | §§6.4.1–6.4.2: the metric `d_m`, Lyapunov stability, Propositions 6.4.3 and 6.4.5 |

Carried from the Chapter 3 project `TransitionProbabilities` (169 theorems), identical except for
the namespace and, in `SpecificMatrices`, a module-docstring paragraph of cross-references that is
dropped:

* `StateSpaces` (2): the three kinds of state space of §3.1. No result uses them.
* `PathSpace` (23), `Kernels` (32): the path measures `Pₓ` and `P_μ` of Theorem 3.4.1, `n`-step
  kernels, the sampled kernel `K_a`, the resolvent and the potential kernel `U`. Continuous
  components are bounded by `K_a`, and reachability is stated with `U`.
* `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes` (36): the Markov and strong Markov
  properties, the return time `τ_C` (`firstReturn`) and `L(x, A)` (`hitProb`), used in
  Proposition 6.1.1 (ii)–(iii) and throughout §6.2.
* `CountableChains` (13), `SpecificMatrices` (21): transition matrices and the matrices of §3.3. No
  Chapter 6 module imports `SpecificMatrices`.

Carried from the Chapter 4 project `Irreducibility` (177 theorems), identical except for the
namespace and, in `RandomWalkIrreducibility` and `LinearIrreducibility`, module-docstring sentences
that referred to modules not carried:

* `Communication` (33), `CountableIrreducibility` (32): communicating classes. Irreducibility of a
  countable chain (`IsIrreducibleChain`) is compared with open set irreducibility on p. 129. No
  Chapter 6 module imports `CountableIrreducibility`.
* `PsiIrreducibility` (13), `MaximalIrreducibility` (30), `Accessibility` (9): φ-irreducibility,
  maximal irreducibility measures and Proposition 4.2.1, used in Proposition 6.2.8.
* `RandomWalkIrreducibility` (20): Proposition 4.3.1, used in Proposition 6.3.1, and the random walk
  with rational increments (p. 130).
* `LinearControllability` (26), `LinearIrreducibility` (14): controllability, the controllability
  map `ctrbMap` and Proposition 4.4.2, used in §§6.3.2–6.3.3.

Carried from the Chapter 5 project `PseudoAtoms` (244 theorems), identical to the copies there
except for the namespace and the module docstring of `SmallSetsModels` (the Chapter 5 follow-up
modules it points to there are not carried here):

* `Atoms` (8), `Splitting` (51), `SplitMarginal` (13): atoms and the Nummelin splitting, on which
  the small-set modules rest.
* `SmallSets` (13), `SmallSetExistence` (17): small sets, Theorem 5.2.2 and Proposition 5.2.4, used
  in Theorem 6.2.5 (ii), Lemma 6.2.7, Proposition 6.2.8 and Propositions 6.3.5–6.3.6.
* `SampledChains` (21), `PetiteSets` (17): sampling distributions, Lemma 5.5.2, petite sets and
  Propositions 5.5.3–5.5.5, used throughout §6.2.
* `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8): periods and cycles.
  `PetiteSets` imports `Cycles`; no Chapter 6 module imports `CycleAperiodic` or
  `ForwardRecurrence`.
* `SmallSetsModels` (11), `SpreadOut` (6): the small sets of random walk on a half line, used in
  Proposition 6.3.1, and the Lebesgue minorant of a spread-out law, used in Proposition 6.3.2.
* `SplitPetite` (14): the counterexample to Proposition 5.5.6 (ii). No Chapter 6 module imports it.

Carried from the Chapters 1–2 project `MarkovModels` (117 theorems):

* `ModelRecursion` (18), `ModelRandomWalk` (19), `ModelLinearModels` (39), through the Chapter 3 and
  4 projects, identical except for the namespace, the module names and a note in each module
  docstring: random recursions and their control maps, random walk, random walk on a half line,
  convolution powers and spread-out laws (RW2), AR(1), AR(k) and LSS(F, G).
* `ModelNonlinearModels` (41), copied from `NonlinearModels`, identical except for the namespace,
  the import of `ModelLinearModels` and a note in the module docstring: NSS(F), used in Proposition
  6.1.2, and the SETAR model, used in Proposition 6.3.6, with the bilinear, NARMA, gumleaf, SAC and
  RCA models.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
