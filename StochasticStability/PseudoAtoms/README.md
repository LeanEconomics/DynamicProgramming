# Meyn and Tweedie, Chapter 5: Pseudo-atoms, in Lean

This is the `StochasticStability/PseudoAtoms` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 5 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 96–122. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 5 is about atoms and the sets that take their place on a general space. An atom is a set
from every point of which the chain moves with the same law. On a countable space every state is
one, but on a general space accessible atoms are rare (§5.1). The Nummelin splitting builds one.
Under the minorization condition (5.2), `P(x, ·) ≥ δ ν` on a set `C`, the space is doubled into a
top and a bottom copy of `X`. The split chain moves so that its first coordinate is the original
chain, and the bottom copy of `C` is an accessible atom (Theorem 5.1.3). Small sets are the sets on
which some skeleton satisfies the minorization. Every set of positive `ψ`-measure contains one
(Theorem 5.2.2), and `X` is a countable union of them (Proposition 5.2.4). §5.3 finds small sets
for random walk on a half line, spread-out random walk, the GI/G/1 queue, the forward recurrence
time `δ`-skeleton and the linear models. §5.4 defines the period. On a countable space it is the
g.c.d. of the return times of a state. On a general space it is the g.c.d. of the times at which a
small set is small, and Theorem 5.4.4 decomposes the space into a cycle of that length. §5.5
introduces the sampled chains `K_a = Σₙ a(n) Pⁿ` and petite sets, the sets that are small for a
sampled chain, and shows that for an aperiodic chain every petite set is small (Theorem 5.5.7).

Every numbered result is formalised: Propositions 5.1.1–5.1.2, 5.2.4, 5.3.1–5.3.3, 5.4.1–5.4.3,
5.4.5–5.4.7 and 5.5.3–5.5.6, Theorems 5.1.3, 5.2.1–5.2.3, 5.4.4 and 5.5.7, and Lemmas 5.5.1–5.5.2,
together with the claims the text makes about its examples. Lemma D.7.4 of the appendix, which §5.4
uses, is proved, not cited. Three claims are false as printed. Each is refuted in Lean by a
counterexample, and a corrected statement is proved. Lemma 5.5.1 and the bound (5.45) fail when the
sampling distribution charges time `0`. Proposition 5.5.6 (ii) fails, even for a ψ-irreducible,
strongly aperiodic chain on `ℕ`; what holds is that `(C \ A)₀ ∪ X₁` is petite. On p. 108, `G(−∞, x]`
should be `G(−∞, x)` and `G(x, ∞)` should be `G[x, ∞)`. In Proposition 5.3.3 the small set is
`(0, δ)`, not `[0, δ)`, since the forward recurrence time is positive, and the hypothesis
`Γ(0, ∞) > 0` is added. Three smaller points are made precise: (5.2) needs `δ < 1`, Theorem 5.4.4
needs `ν_M(C) > 0`, and the small sets of §5.3.5 use `m = max(n, 1)`. Theorems 5.2.1–5.2.3,
Proposition 5.2.4 (ii), Proposition 5.4.5 (ii)–(iii), Propositions 5.5.5–5.5.6 and Theorem 5.5.7
assume that `B(X)` is countably generated, the book's standing assumption. The splitting, Theorem
5.1.3 and Theorem 5.4.4 for a given small set hold on every measurable space. Theorem 5.2.1 takes
`φ` finite, and the forward recurrence time chain needs `p(0) = 0`. The following are not
formalised: the Athreya–Ney construction of §5.1.3, which is informal; splitting under the
minorization (5.11) by a function `h`; the continuous-state cycle example of p. 110; the remark that
`X` is "not necessarily petite" (p. 119), for which the book gives no example; and the informal
remarks and the commentary of §5.6. Three devices of the book's proofs are replaced by other
arguments: the version of the densities (5.17) with the density points (5.18)–(5.23), Lemma D.4.3,
and the Gaussian density (5.36). See [corrections](docs/corrections.md). The library contains
**970 theorems**. Of these, 276 are in the Chapter 5 modules and 694 in the modules carried from
Chapters 1–4.

Four results carry the chapter.

* **The Nummelin splitting, at the level of paths** (`Splitting`, `SplitMarginal`). A
  minorization `M` bundles `C`, `δ` and `ν`. The split kernel `P̌` (`Minorization.splitKernel`)
  on `X × Bool` is a composition: move by the kernel `Q` (`Minorization.baseK`), which is the
  residual law `R` (`Minorization.resid`) on the top level and `ν` on the bottom level, and then
  toss the `δ`-coin (`Minorization.splitK`). Tossing the coin and then moving by `Q` is moving by
  `P` (`Minorization.baseK_comp_splitK`), and this gives (5.10), `μ*P̌ = (μP)*`
  (`Minorization.split_comp_splitKernel`). Theorem 5.1.3 (i) is proved for whole paths: under
  `P̌_{μ*}`, the first coordinates of the split chain have the law `P_μ`
  (`Minorization.theorem_5_1_3_i_path`). So the first coordinate is a Markov chain with kernel `P`
  (`Minorization.isMarkovChain_split_fst`), and `E_μ[F(Φ)] = Ě_{μ*}[F(Φ̌.1)]` for every measurable
  `F ≥ 0` on path space (`Minorization.lintegral_split_fst`). The book's (5.9) is the one-time
  case (`Minorization.theorem_5_1_3_i`).
* **The existence of small sets without density points** (`SmallSetExistence`). Theorem 5.2.2
  (`theorem_5_2_2`): every `A ∈ B⁺(X)` contains a `νₘ`-small set `C ∈ B⁺(X)` with `νₘ(C) > 0`.
  The book's proof of Theorem 5.2.1 builds a version of the densities with the
  Chapman–Kolmogorov inequality (5.17), and finds density points by the Basic Differentiation
  Theorem (5.18)–(5.23). Here the densities are Mathlib's kernel Radon–Nikodym derivatives, which
  are jointly measurable on a countably generated space (`transDensity`,
  `measurable_transDensity`). The density points are replaced by a countable measure-dense
  family of sets: if `F(x, z) = φ(Uₓ ∩ Vᶻ)` does not vanish almost everywhere on `A × A`, it is
  bounded below on a rectangle `E × D` of positive measure (`exists_rect_of_not_ae_zero`). No
  differentiation of measures is used, and (5.17) is not needed.
* **The cycle decomposition** (`Cycles`, `CycleAperiodic`). Theorem 5.4.4 (`theorem_5_4_4`): for a
  `ν_M`-small `C ∈ B⁺(X)` with `ν_M(C) > 0` and `d = g.c.d. E_C`, there is a `d`-cycle; every
  `d'`-cycle has `d' ∣ d`; and two `d`-cycles agree up to `ψ`-null sets after a relabelling
  `i ↦ k + i`. The key estimate is `ψ(D*_i ∩ D*_k) = 0` for `i ≠ k` (`measure_cycleSet_inter`).
  The period is `g.c.d. E_C` for every such `C` (`isPeriod_gcd`). The book derives the
  aperiodicity in Proposition 5.4.6 "from the definition of `d`". Here a `d'`-cycle of `Pᵈ` inside
  a cycle class is lifted to a `dd'`-cycle of `P` (`isCycle_liftClass`), which forces `d' = 1`
  (`proposition_5_4_6_aperiodic`).
* **Petite sets are small for aperiodic chains** (`PetiteSets`). Theorem 5.5.7 (`theorem_5_5_7`).
  By Proposition 5.5.5 (i), a petite set is petite for a maximal irreducibility measure. For an
  aperiodic chain, `E_C` contains every large time (`exists_forall_mem_smallTimes_of_aperiodic`,
  from Theorem 5.4.4 and Lemma D.7.4). A tail bound on the sampling distribution
  (`exists_tail_le`) then turns `K_a` into a fixed number of steps.

The library covers the chapter as follows.

* **Atoms** (Chapter 5 introduction, §5.1). Atoms and accessible atoms; accessibility does not
  depend on the choice of the maximal irreducibility measure. Propositions 5.1.1 and 5.1.2. Every
  point of an irreducible countable chain is an accessible atom, `{0}` is one for random walk on a
  half line with `Γ(−∞, 0) > 0`, and random walk on `ℝ` with a density has none.
* **Splitting** (§§5.1.1–5.1.2). The minorization (5.2), the split measures (5.3) with the marginal
  identity (5.4), the split kernel (5.5)–(5.7), the atom `α̌ = C₁` (5.8), (5.10) and its iterates,
  and Theorem 5.1.3. `Φ` is `φ`-irreducible if and only if `Φ̌` is `φ*`-irreducible, and a maximal
  irreducibility measure splits into a maximal one.
* **Small sets** (§5.2). The definition (5.14); the Lebesgue decomposition (5.15) with jointly
  measurable densities; Theorems 5.2.1–5.2.3 and Proposition 5.2.4. A small set `C` with
  `ν(C) > 0` gives the minorization (5.2) for a skeleton.
* **Small sets for specific models** (§5.3). Compact sets for random walk on a half line;
  `[−β/2, β/2]` for random walk with a density; Proposition 5.3.1 for spread-out random walk, with
  Lemma D.4.3 replaced by the lower semicontinuity of a self-convolution; Proposition 5.3.2 for
  the GI/G/1 ladder chain, derived from the queue; Proposition 5.3.3 for the forward recurrence
  time `δ`-skeleton; and compact sets for AR(1) and for the controllable LSS(F, G) model. The
  linear case is proved without the Gaussian density, by pulling Lebesgue measure back along the
  surjective controllability map, so it holds for every disturbance law that dominates a multiple
  of Lebesgue measure on balls.
* **Periods on a countable space** (§§5.4.1–5.4.2). Lemma D.7.4, proved through the least
  positive difference of elements of the set, without Bézout's identity. The period (5.37),
  Propositions 5.4.1–5.4.3, aperiodicity and strong aperiodicity, and the deterministic cycle of
  p. 110.
* **Cycles on a general space** (§§5.4.3–5.4.4). The set `E_C` (5.40), Theorem 5.4.4, the period,
  aperiodicity and strong aperiodicity; Propositions 5.4.5–5.4.7. The forward recurrence time chain
  on `ℤ₊` has period `g.c.d.{n : p(n) > 0}`, and the forward recurrence time `δ`-skeleton is
  aperiodic for small `δ`.
* **Sampled chains and petite sets** (§5.5). Sampling distributions and `K_a` (5.43), `⇝ᵃ`
  (5.44), Lemma 5.5.1 corrected, and Lemma 5.5.2; petite sets, Propositions 5.5.3–5.5.5,
  Proposition 5.5.6 (i), the counterexample to (ii) and its corrected statement, and
  Theorem 5.5.7.

All names are in the namespace `MeynTweedie.PseudoAtoms`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Atoms](PseudoAtoms/Atoms.lean) | 8 | Atoms, accessible atoms, Propositions 5.1.1–5.1.2 |
| [Splitting](PseudoAtoms/Splitting.lean) | 51 | (5.2)–(5.8), (5.10): minorization, split measures, the split kernel, Theorem 5.1.3 (i) in the form (5.9) |
| [SplitMarginal](PseudoAtoms/SplitMarginal.lean) | 13 | Theorem 5.1.3: (i) for paths, and (ii) |
| [SmallSets](PseudoAtoms/SmallSets.lean) | 13 | (5.14), (5.26), Proposition 5.2.4 (i) and (iii) |
| [SmallSetExistence](PseudoAtoms/SmallSetExistence.lean) | 17 | (5.15)–(5.16), Theorems 5.2.1–5.2.3, Proposition 5.2.4 (ii) |
| [SmallSetsModels](PseudoAtoms/SmallSetsModels.lean) | 11 | The atoms of pp. 96–98; §5.3.1; random walk with a density (§5.3.2); AR(1) (§5.3.5); Proposition 5.3.2 from the bottom-rung formula |
| [SpreadOut](PseudoAtoms/SpreadOut.lean) | 6 | §5.3.2: (5.28), Proposition 5.3.1 |
| [GIG1SmallSets](PseudoAtoms/GIG1SmallSets.lean) | 7 | §5.3.3: Proposition 5.3.2 for the GI/G/1 queue; the corrections of p. 108 |
| [RenewalSmallSets](PseudoAtoms/RenewalSmallSets.lean) | 7 | §§5.3.4, 5.4.4: (5.32)–(5.35), Propositions 5.3.3 and 5.4.7 |
| [LinearSmallSets](PseudoAtoms/LinearSmallSets.lean) | 9 | §5.3.5: compact sets are small for LSS(F, G) |
| [Period](PseudoAtoms/Period.lean) | 22 | Lemma D.7.4, (5.37)–(5.39), Propositions 5.4.1–5.4.3, the cycle of p. 110 |
| [Cycles](PseudoAtoms/Cycles.lean) | 33 | (5.40)–(5.42), Theorem 5.4.4, the period, Propositions 5.4.5 and 5.4.6 (first part) |
| [CycleAperiodic](PseudoAtoms/CycleAperiodic.lean) | 10 | Proposition 5.4.6: `Φ_d` is aperiodic on each cycle class |
| [ForwardRecurrence](PseudoAtoms/ForwardRecurrence.lean) | 8 | §5.4.4: the period of the forward recurrence time chain |
| [SampledChains](PseudoAtoms/SampledChains.lean) | 21 | (5.43)–(5.48), Lemmas 5.5.1–5.5.2, the correction to Lemma 5.5.1 |
| [PetiteSets](PseudoAtoms/PetiteSets.lean) | 17 | (5.49), Propositions 5.5.3–5.5.5 and 5.5.6 (i), Theorem 5.5.7 |
| [SplitPetite](PseudoAtoms/SplitPetite.lean) | 14 | Proposition 5.5.6 (ii): the counterexample and the corrected statement |
| [SplitPetiteIrreducible](PseudoAtoms/SplitPetiteIrreducible.lean) | 9 | The counterexample to Proposition 5.5.6 (ii) satisfies all its hypotheses |

Carried from the Chapter 3 project `TransitionProbabilities` (369 theorems). `StateSpaces`,
`PathSpace`, `Kernels`, `MarkovProperty`, `StrongMarkov`, `HittingTimes`, `CountableChains` and
`SpecificMatrices` are identical except for the namespace and, in `SpecificMatrices`, a
module-docstring paragraph of cross-references that is dropped. The other seven, `ModelKernels`,
`PoissonCounts`, `SpecificKernels`, `Regeneration`, `LadderChains`, `RenewalSkeletons` and
`GIG1Embedding`, are identical except for the namespace, the imports and a note in each module
docstring. In `LadderChains`, the ladder kernel is renamed `ladderChainKernel` (with
`ladderChainKernel_apply`, `ladderChainKernel_translate` and `isMarkovKernel_ladderChainKernel`),
because `ladderKernel` names the counterexample of Proposition 5.5.6 (ii); `RenewalSkeletons` and
`GIG1Embedding` use the new name.

* `StateSpaces` (2): the three kinds of state space of §3.1. No result uses them.
* `PathSpace` (23), `Kernels` (32): the path measures `Pₓ` and `P_μ` of Theorem 3.4.1, `n`-step
  kernels, the sampled kernel `K_a` of (5.43), the resolvent and the potential kernel `U`. The
  split chain is built with `pathMeasure`.
* `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes` (36): the Markov and strong Markov
  properties, and the hitting times. `L(x, A)` and its first-step identity are used in
  Proposition 5.1.2 and Lemma 5.5.1.
* `CountableChains` (13), `SpecificMatrices` (21): transition matrices and the matrices of §3.3.
* `ModelKernels` (19), `PoissonCounts` (12), `SpecificKernels` (42), `Regeneration` (12),
  `RenewalSkeletons` (53): the kernels of §3.5 and the forward recurrence time `δ`-skeleton
  `fwdSkelKernel`, a Markov chain by `fwdSkeleton_isMarkovChain`. Used in Propositions 5.3.3
  and 5.4.7.
* `LadderChains` (25), `GIG1Embedding` (37): the GI/G/1 ladder kernel `gig1Ladder`, and the queue
  at arrivals as a Markov chain with this kernel (`gig1_isMarkovChain`). Used in
  Proposition 5.3.2.

Carried from the Chapter 4 project `Irreducibility` (177 theorems), identical except for the
namespace and, in `RandomWalkIrreducibility` and `LinearIrreducibility`, module-docstring sentences
that referred to modules not carried:

* `Communication` (33), `CountableIrreducibility` (32): communication and communicating classes,
  used in §5.4.2. No Chapter 5 module imports `CountableIrreducibility`.
* `PsiIrreducibility` (13), `MaximalIrreducibility` (30), `Accessibility` (9): φ-irreducibility,
  maximal irreducibility measures, `B⁺(X)`, Proposition 4.2.3 (used in Theorem 5.4.4) and uniform
  accessibility `⇝`.
* `RandomWalkIrreducibility` (20): Proposition 4.3.1 and the local density bounds, used in §5.1
  and §§5.3.1–5.3.2.
* `LinearControllability` (26), `LinearIrreducibility` (14): controllability and the `k`-step law
  of LSS(F, G), used in §5.3.5.

Carried from the Chapters 1–2 project `MarkovModels` (148 theorems), through the Chapter 3 and 4
projects, identical except for the namespace, the module names and a note in each module
docstring:

* `ModelRecursion` (18), `ModelRandomWalk` (19): random recursions, random walk, convolution
  powers, random walk on a half line and spread-out increments (RW2), used in §§5.1 and 5.3.
* `ModelLinearModels` (39): AR(1) and LSS(F, G), used in §5.3.5.
* `ModelCountableModels` (9), `ModelQueues` (16), `ModelStorage` (18), `ModelRenewal` (29): the
  countable models, queues, storage and renewal processes on which the §3.5 modules rest.
  `ModelRenewal` defines the forward recurrence time `fwdTimeCts`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
