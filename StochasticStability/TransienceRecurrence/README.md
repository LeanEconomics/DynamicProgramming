# Meyn and Tweedie, Chapter 8: Transience and Recurrence, in Lean

This is the `StochasticStability/TransienceRecurrence` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 8 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 171–198. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 8 classifies chains through the occupation times `η_A = Σ_{n ≥ 1} 1{Φₙ ∈ A}` and their
means `U(x, A) = E_x[η_A]`. A set `A` is uniformly transient if `U(·, A)` is bounded on `A`,
recurrent if `U(·, A) = ∞` on `A`, and transient if it is covered by countably many uniformly
transient sets. A ψ-irreducible chain is recurrent if `U(x, A) = ∞` for every `x` and every
`A ∈ B⁺(X)`, and transient if `X` is transient. §8.1 classifies the states of a chain on a
countable space and shows that an irreducible chain is transient or recurrent (Proposition 8.1.1,
Theorem 8.1.2), that a state is recurrent if and only if the chain returns to it surely
(Proposition 8.1.3), and that recurrent countable chains reach every state surely (Proposition
8.1.4); it treats the forward recurrence time chain, renewal sequences and the simple random walk,
and proves that a random walk on `ℤ` with mean-zero increments is recurrent (Theorem 8.1.5). §8.2
introduces the first-entrance and last-exit decompositions (8.18)–(8.19), proves the dichotomy for
a chain with an atom (Theorem 8.2.1), and carries it through the split chain and the resolvent to
every ψ-irreducible chain (Proposition 8.2.2, Lemma 8.2.3, Proposition 8.2.4, Theorem 8.2.5) and to
its skeletons (Theorem 8.2.6). §8.3 gives conditions on return times for uniform transience
(Propositions 8.3.1–8.3.3), proves the dichotomy again without splitting (Theorem 8.3.4), shows
that the petite sets of a transient chain are uniformly transient (Theorem 8.3.5), characterises
recurrence and transience through `L(x, C) = P_x(τ_C < ∞)` (Theorem 8.3.6), and shows that
ψ-null sets are transient (Propositions 8.3.7–8.3.8). §8.4 gives drift criteria in terms of
`ΔV = PV − V`: the minimal solution of (8.39) (Proposition 8.4.1), transience from a bounded `V`
with `ΔV ≥ 0` off a sublevel set (Theorem 8.4.2), recurrence from a `V` unbounded off petite sets
with `ΔV ≤ 0` off a petite set (Theorem 8.4.3), and applies them to random walks with bounded range
on `ℤ` and on `ℤ₊` (Propositions 8.4.4–8.4.6). §8.5 classifies random walk on `ℝ₊`: recurrence for
negative mean (Proposition 8.5.1) and for zero mean with finite variance (Lemmas 8.5.2–8.5.3,
Proposition 8.5.4), and transience of the walk on `ℤ₊` skip-free to the right for positive mean
(Proposition 8.5.5).

Every numbered result is formalised: Theorems 8.0.1–8.0.2, Propositions 8.1.1, 8.1.3 and 8.1.4,
Theorems 8.1.2 and 8.1.5, Theorem 8.2.1, Proposition 8.2.2, Lemma 8.2.3, Proposition 8.2.4,
Theorems 8.2.5–8.2.6, Propositions 8.3.1–8.3.3, Theorems 8.3.4–8.3.6, Propositions 8.3.7–8.3.8,
Proposition 8.4.1, Theorems 8.4.2–8.4.3, Propositions 8.4.4–8.4.6, Proposition 8.5.1, Lemmas
8.5.2–8.5.3 and Propositions 8.5.4–8.5.5, together with the claims the text makes about its
examples. The weak law of large numbers (8.14), which the book quotes without proof, is derived
from Mathlib's strong law. Five claims are false as printed. Each is refuted in Lean by a
counterexample, and a corrected statement is proved. Proposition 8.3.1 (ii) and Theorem 8.3.6 (i)
fail for the empty set, which satisfies their hypotheses vacuously; they hold for non-empty `A` and
`C`. The claim `L(x, C) ≡ 1` of Theorem 8.4.3 fails for `C = ∅`; it holds for `C ∈ B⁺(X)`, and
the recurrence conclusion holds as stated. Proposition 8.4.6 fails for `Γ = δ₀`; it holds when
`Γ(−∞, 0) > 0`. The renewal equation on p. 175 should read `u = δ₀ + u ∗ p`, not `u = 1 + u ∗ p`.
Seven further points are corrected without a counterexample: Theorem 8.4.2 is proved with
`ΔV ≥ 0`, since the book's converse function has `ΔV = 0` and Proposition 8.4.5 uses equality; the
atom proof of Proposition 8.2.2 needs the small set in `B⁺(X)`, and the general form is proved
another way; Proposition 8.3.2 is trivial as printed, and the covering its proof gives is what is
proved; the bound `mM` in (8.29) should be `m(2 + M)`; Theorem 8.3.5 needs no irreducibility; the
cut-off `R` in Proposition 8.5.4 is unnecessary; and Proposition 8.5.5 needs `Γ(−∞, 0) > 0`,
without which the walk is not irreducible. Countable generation of `B(X)` is assumed only for
Theorems 8.2.5 and 8.2.6, Proposition 8.3.8 and (8.43). Lemma 8.5.2 assumes that `log(s + tW)` is
integrable on `A`, moments are stated as integrability, and Propositions 8.4.4–8.4.6 take an
explicit range `r`. The following are not formalised: the generating-function identities in `z`
(8.8)–(8.11) and (8.20)–(8.26), which are proof devices and whose forms at `z = 1` are proved; the
almost-sure statement `η_A = ∞` of p. 173, which is Harris recurrence (Chapter 9); the forward
references, such as the converse of Theorem 8.0.2 (ii) for Feller chains; and the commentary of
§8.6. See [corrections](docs/corrections.md). The library contains **1057 theorems**. Of these,
220 are in the Chapter 8 modules and 837 in the modules carried from Chapters 1–6.

Five results carry the chapter.

* **The dichotomy, proved twice** (`Dichotomy`, `SplitDichotomy`). Directly, without countable
  generation (`theorem_8_3_4`): if `Φ` is not recurrent, some `A ∈ B⁺(X)` has `U(x*, A) < ∞`;
  by (8.36) the set `{U(·, A) = ∞}` is ψ-null (`potKernel_eq_top_of_pow_pos`), so some
  `A_r = {y ∈ A : U(y, A) ≤ r}` lies in `B⁺(X)`, and the sets from which `A_r` is accessible
  cover `X` by uniformly transient sets (`isTransientSet_univ_of_uniformlyTransient`, from
  Proposition 8.3.2). The two cases exclude each other (`isRecurrentChain_or_isTransientChain`).
  By splitting, on a countably generated space (`theorem_8_2_5`): the resolvent `K_{a_{1/2}}`
  satisfies a minorization on a set of `B⁺(X)`, its split chain has an accessible atom `α̌`, which
  is recurrent or uniformly transient (`IsAtom.isRecurrentSet_or_isUniformlyTransient`), so
  Theorem 8.2.1 classifies the split chain and the resolvent (`Minorization.proposition_8_2_2`),
  and Lemma 8.2.3 passes the classification back to `Φ` (`proposition_8_2_4`). This proof does
  not use Theorem 8.3.4. Theorem 8.0.1 follows from the direct proof and Theorem 8.3.5
  (`theorem_8_0_1`).
* **The first-entrance and last-exit decompositions** (`Decompositions`). (8.18) and (8.19) are
  proved as equalities for all measurable `A`, `B` and every `n`, from the Markov property at fixed
  times (`firstEntrance_decomposition`, `lastExit_decomposition`); the last-exit time, which is
  not a stopping time, is never used as one. Summed at `z = 1`, where every term is non-negative,
  they give (8.25) and (8.26) as equalities in `[0, ∞]`, `U = U_A + ∫_A U_A U` and
  `U = U_A + ∫_A U U_A` (`potKernel_firstEntrance`, `potKernel_lastExit`). The first-entrance
  equation `U(x, A) = E_x[1 + U(Φ_{τ_A}, A); τ_A < ∞]` (`potKernel_eq_firstReturn`), from the
  strong Markov property, drives Proposition 8.3.1, and the last-exit form
  `potKernel_eq_zero_of_lastExit` drives Proposition 8.1.4 and Theorem 8.3.6 (ii).
* **Drift criteria** (`DriftCriteria`). `P_x(σ_C < ∞)` is the minimal non-negative solution of
  (8.39) (`proposition_8_4_1`). A bounded `V ≥ 0`, `V ≤ M`, with `ΔV ≥ 0` off `C ∈ B⁺(X)`,
  `V ≤ r` on `C` and `{V > r} ∈ B⁺(X)` gives `L(x, C) ≤ (M − V(x))/(M − r) < 1` on `{V > r}`,
  hence transience (`isTransientChain_of_drift`); with the converse function
  `1 − P_x(σ_C < ∞)`, which has `ΔV = 0` off `C` (`drift_one_sub_hitProbZero`), this is Theorem
  8.4.2 (`theorem_8_4_2`) and Theorem 8.0.2 (i) (`theorem_8_0_2_i`). For recurrence, (V1) bounds the killed chain,
  `∫ (P I_{Cᶜ})ⁿ(x, dy) V(y) ≤ V(x)` (`lintegral_killedKernel_pow_le`), and petite sublevel sets
  reach `C` with probability bounded below (`IsPetite.hitProb_ge`), so `L(x, C) ≡ 1` for
  `C ∈ B⁺(X)` (`lemma_8_4_3_hitProb`) and the chain is recurrent (`theorem_8_4_3`,
  `theorem_8_0_2_ii`). The bounded-range walks of §8.4.3 and the walks of §8.5 are classified by
  these criteria.
* **Random walk on `ℤ` with mean zero** (`RandomWalkMeanZero`). The weak law (8.14),
  `Pⁿ(0, {|y| ≤ an}) ≥ ½` for large `n`, is derived from Mathlib's strong law through convergence
  in measure (`randomWalk_wlln`), with `Pⁿ(0, ·)` identified with the law of `W₁ + ⋯ + Wₙ`
  (`randomWalk_pow_eq_infinitePi`). With (8.15) (`sum_pow_le_sum_pow_zero`) and translation
  invariance it gives `U(0, 0) = ∞` for integrable increments of mean zero, with no bound on the
  range (`theorem_8_1_5`).
* **The skip-free walk** (`SkipFreeWalk`). For the walk on `ℤ₊` skip-free to the right, with
  `aⱼ = Γ(1 − j)` and `Σ n aₙ < 1`, the bounded harmonic function of (8.62) is
  `V(x) = Σ_{m<x} bₘ`, where `b` is the renewal sequence of `cⱼ = Σ_{n>j} aₙ` (`skipFreeV`). The
  equation (8.63) is proved with Mathlib's `PowerSeries` over `[0, ∞]`, by comparing coefficients,
  instead of with Abel's theorem (`skipFree_harmonic`), and `Σ bₘ = (1 − Σ n aₙ)⁻¹` is the renewal
  identity (8.12) at `z = 1` (`tsum_renewalSeq_skipFree`). The walk is then transient
  (`proposition_8_5_5`, `proposition_8_5_5_mean`).

The library covers the chapter as follows.

* **Uniform transience and recurrence** (§8.0, p. 171). Occupation times and their truncations,
  uniformly transient, recurrent and transient sets, and recurrent and transient chains.
* **Classification on countable spaces** (§8.1.1). Transient and recurrent states, (8.5)–(8.7),
  Propositions 8.1.1, 8.1.3, 8.1.4, Theorem 8.1.2, the agreement with the general definitions for
  counting measure, and Harris recurrence of recurrent countable chains.
* **Specific models** (§8.1.2). The forward recurrence time chain; renewal sequences, the renewal
  equation refuted as printed and corrected, (8.12); the simple random walk on `ℤ₊` and (8.13);
  the random walk on `ℤ`, (8.14)–(8.17) and Theorem 8.1.5.
* **Transience and recurrence of sets** (§8.2.1). Taboo probabilities, the decompositions
  (8.18)–(8.19), and (8.22)–(8.26) at `z = 1`.
* **Chains with an atom** (§8.2.2). Theorem 8.2.1 and Proposition 8.1.3 for atoms.
* **The general dichotomy** (§8.2.3). The split chain and (8.28), Proposition 8.2.2 in three
  forms, the powers of the resolvent and Lemma 8.2.3, Proposition 8.2.4, Theorem 8.2.5, skeletons,
  (8.29) corrected and Theorem 8.2.6.
* **Transience of sets** (§8.3.1). Propositions 8.3.1–8.3.3, with the corrections to 8.3.1 (ii)
  and 8.3.2.
* **Transient sets of ψ-irreducible chains** (§8.3.2). Theorems 8.3.4–8.3.6, with Theorem 8.3.6 (i)
  refuted for `C = ∅` and corrected, and Propositions 8.3.7–8.3.8.
* **Drift criteria** (§§8.0, 8.4.1–8.4.2). The drift (8.1), Proposition 8.4.1, Theorems 8.4.2,
  8.4.3 and 8.0.2, the killed chain, (8.43), and the correction to Theorem 8.4.3.
* **Random walks with bounded range** (§8.4.3). Finite sets are petite, the root of (8.53), and
  Propositions 8.4.4–8.4.6, with Proposition 8.4.6 refuted for `Γ = δ₀` and corrected.
* **Random walk on `ℝ₊`** (§§8.5.1–8.5.2). The kernel of the walk, petite intervals,
  Proposition 8.5.1 and (8.54), Lemmas 8.5.2–8.5.3 and Proposition 8.5.4.
* **The skip-free walk** (§8.5.3). (8.62)–(8.63), (8.68), Proposition 8.5.5, and the walks with
  `Γ[0, ∞) = 1`, which are not irreducible.

All names are in the namespace `MeynTweedie.TransienceRecurrence`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [UniformTransience](TransienceRecurrence/UniformTransience.lean) | 46 | §§8.0, 8.2.1, 8.3.1: uniformly transient, recurrent and transient sets and chains, truncated occupation times, the first-entrance equation for `U`, return times along the path, Propositions 8.3.1–8.3.3 and the correction to 8.3.1 (ii) |
| [Decompositions](TransienceRecurrence/Decompositions.lean) | 8 | §8.2.1: the Markov property at a fixed time, the first-entrance and last-exit decompositions (8.18)–(8.19), and (8.25)–(8.26) at `z = 1` |
| [Dichotomy](TransienceRecurrence/Dichotomy.lean) | 17 | §§8.0, 8.3.2: (8.36), Theorems 8.3.4, 8.3.5, 8.0.1 and 8.3.6, Propositions 8.3.7–8.3.8 |
| [SplitDichotomy](TransienceRecurrence/SplitDichotomy.lean) | 32 | §§8.2.2–8.2.3: atoms and Theorem 8.2.1, the split chain, (8.28) and Proposition 8.2.2, the resolvent, Lemma 8.2.3, Proposition 8.2.4, Theorem 8.2.5, skeletons, (8.29) and Theorem 8.2.6 |
| [DriftCriteria](TransienceRecurrence/DriftCriteria.lean) | 23 | §§8.0, 8.4.1–8.4.2: the drift (8.1), Proposition 8.4.1, the drift argument for transience, Theorems 8.4.2 and 8.0.2 (i), the killed chain, Theorems 8.4.3 and 8.0.2 (ii) and the correction to 8.4.3, (8.43) |
| [CountableClassification](TransienceRecurrence/CountableClassification.lean) | 18 | §§8.1.1–8.1.2: transient and recurrent states, Propositions 8.1.1, 8.1.3, 8.1.4, Theorem 8.1.2, (8.6)–(8.7), the forward recurrence time chain, renewal sequences, the renewal equation and its correction, (8.12) |
| [RandomWalkIntegers](TransienceRecurrence/RandomWalkIntegers.lean) | 40 | §§8.1.2, 8.4.3: finite petite sets, the root of (8.53), Propositions 8.4.4–8.4.6 and the correction to 8.4.6, the simple random walk and (8.13), the counterexample to Theorem 8.3.6 (i) |
| [RandomWalkHalfLine](TransienceRecurrence/RandomWalkHalfLine.lean) | 16 | §§8.5.1–8.5.2: the walk on `ℝ₊`, petite intervals, (8.54) and Proposition 8.5.1, Lemmas 8.5.2–8.5.3, Proposition 8.5.4 |
| [SkipFreeWalk](TransienceRecurrence/SkipFreeWalk.lean) | 15 | §8.5.3: the tails `cⱼ`, (8.68), the harmonic function and (8.62)–(8.63), Proposition 8.5.5, walks with `Γ[0, ∞) = 1` |
| [RandomWalkMeanZero](TransienceRecurrence/RandomWalkMeanZero.lean) | 5 | §8.1.2: the `n`-step law as a sum of i.i.d. increments, translation invariance, the weak law (8.14), (8.15), Theorem 8.1.5 |

Carried from the Chapter 6 project `TopologyContinuity` (837 theorems): every module of that
project, identical to the copies there except for the namespace. No Chapter 8 module imports any of
its own Chapter 6 modules (130 theorems): `FellerChains` (40), `TChains` (14), `EChains` (16),
`LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16), `TChainModels` (10),
`EChainsStability` (12).

Carried in turn by `TopologyContinuity` from the earlier projects (707 theorems; see that project's
README for how they differ from the originals):

* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` (`pathKernel`),
  the potential kernel `U` (`potKernel`), the resolvent (`resolvent`), the strong Markov property
  (`strong_markov_lintegral`), hitting and return times and probabilities (`firstReturn`,
  `firstHit`, `returnTimeK`, `hitProb`), taboo probabilities (`tabooProb`, `tabooKernel`,
  `tabooPotKernel`), occupation times (`occTime`) and the random walk matrices on `ℤ` and `ℤ₊`
  (`rwMatrix`, `rwhlMatrix`, with `matKernel`) are used throughout. No Chapter 8 module imports
  `StateSpaces`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Absorbing sets (`IsAbsorbing`), irreducibility on a countable space
  (`IsIrreducibleChain`), ψ-irreducibility and maximal irreducibility measures
  (`IsPhiIrreducible`, `IsMaximalIrreducibility`), full absorbing sets (`proposition_4_2_3_i`,
  `proposition_4_2_3_ii`), the sets `Ā` and `Ā(m)` (`hitSet`, `hitSetLevel`) and the exclusion of
  irreducibility by disjoint absorbing sets (`not_isPhiIrreducible_of_disjoint_absorbing`) are
  used. No Chapter 8 module imports `LinearControllability` or `LinearIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Atoms (`IsAtom`), the split chain
  (`Minorization`), small and petite sets (`IsSmallSet`, `IsPetite`), sampling distributions and
  accessibility (`IsSamplingDist`, `SampledAccessible`, `lemma_5_5_2_iii`), the minorization for
  the resolvent (`theorem_5_2_3_resolvent`), cycles and aperiodicity (`IsCycle`, `IsAperiodic`,
  `proposition_5_4_5_iii`) and the forward recurrence time chain (`fwdRecKernel`) are used. No
  Chapter 8 module imports `SpreadOut` or `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). The random walks
  on `ℤ` and on `ℝ₊` (`randomWalkKernel`, `halfLineWalkKernel`) and the law of a random recursion
  (`law_orbit`) come from these modules. No Chapter 8 module imports `ModelNonlinearModels`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
