# Meyn and Tweedie, Chapter 7: The Nonlinear State Space Model, in Lean

This is the `StochasticStability/NonlinearStateSpace` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 7 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 146–168. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 7 studies the nonlinear state space model NSS(F), `Xₖ = F(Xₖ₋₁, Wₖ)`, through its
deterministic control model CM(F), in which the disturbances are replaced by controls `uₖ` in the
control set `O_w`. CM(F) is forward accessible if the set `A₊(x)` of states reachable from `x` has
non-empty interior for every `x`. §7.1 relates forward accessibility to a rank condition on the
generalized controllability matrix `C_x^k` (Theorem 7.1.1 for scalar models, Proposition 7.1.4 in
general), and shows that when the disturbance has a lower semicontinuous density a forward
accessible model is a T-chain whose state space is a union of open small sets (Propositions 7.1.2
and 7.1.5); the simple bilinear model is the example (Proposition 7.1.3). §7.2 introduces invariant
and minimal sets of CM(F). A minimal set is absorbing, and NSS(F) restricted to it is an open set
irreducible T-chain (Theorem 7.2.4); NSS(F) is ψ-irreducible if and only if CM(F) is M-irreducible,
that is, has a globally attracting state (Proposition 7.2.5, Theorem 7.2.6). §7.3 splits a minimal
set into a periodic orbit of closed sets (Theorem 7.3.3), which are the connected components of the
minimal set when the control set is connected (Proposition 7.3.4), and identifies this orbit with
the cycles of NSS(F) (Theorem 7.3.5). §7.4 applies the theory to the dependent parameter bilinear
model, the gumleaf attractor and the adaptive control model (Propositions 7.4.1–7.4.3). §7.5
drops forward accessibility and shows that NSS(F) is an e-chain when the sensitivity process
`∇Φₖ = dΦₖ/dΦ₀` is bounded in mean on compact sets (Theorem 7.5.1, Propositions 7.5.2–7.5.3).

Every numbered result is formalised: Theorem 7.1.1, Propositions 7.1.2–7.1.5, Propositions
7.2.1–7.2.3, Theorem 7.2.4, Proposition 7.2.5, Theorem 7.2.6, Proposition 7.3.1, Lemma 7.3.2,
Theorem 7.3.3, Proposition 7.3.4, Theorem 7.3.5, Propositions 7.4.1–7.4.3, Theorem 7.5.1 and
Propositions 7.5.2–7.5.3, together with the claims the text makes about its examples and Duflo's
condition from the commentary. Theorem 7.1.1 and Propositions 7.1.5 and 7.3.1, whose proofs the book
omits, are proved; so are Propositions 7.1.4 and 7.5.2, in the forms described below. Five claims
are false as printed. Each is refuted in Lean by a counterexample, and, except for the claim about
indecomposability, a corrected statement is proved. Read literally, the definition of a minimal set
(p. 155) admits only `∅`; "non-empty" is added. The claim that an M-irreducible control model has
`M⁰ = ∅` (p. 156) fails for `x ↦ x/2`; what holds is that `M` lies in every non-empty closed
invariant set. Indecomposability is not necessary for a unique minimal set (p. 156), as `x ↦ 2x`
shows. Proposition 7.1.3 fails for `θ = 1`, `b ≠ 0`, where `−1/b` is a fixed point of every control;
it holds when `b = 0` or `θ ≠ 1`. For the adaptive control model the interior of the state space is
not reached in one step from every initial condition, and it is empty for `α = 0` (p. 162);
Proposition 7.4.3 is proved on the closed state space, for `α`, `σ_z`, `σ_w ≠ 0`, and without
`σ_z² < 1`. Two further slips are corrected without a counterexample: Proposition 7.4.2 cites
Theorem 7.2.6 where Proposition 7.1.5 is meant, and is proved on the absorbing set
`{xᵃ ≠ 0, xᵇ ≠ 0}`;
and in the proof of Theorem 7.2.6 a point of `supp ψ` is shown only to lie in the closure of every
`A₊(y)`, which suffices. `C¹` replaces `C^∞` throughout, and the state and noise spaces are
finite-dimensional real normed spaces. Mathlib's Sard theorem covers only maps whose source
dimension is at most the target dimension, so outside the scalar case the implication from forward
accessibility to the rank condition (CM3) assumes that the critical values of the control maps are
null; Theorems 7.2.4 (ii) and 7.2.6, and Proposition 7.3.1 through Theorem 7.3.5, take the rank
condition, which is equivalent to forward accessibility by Proposition 7.1.4. Theorem 7.5.1 (i)
assumes that `Φₖ` is integrable from one point, Proposition 7.5.2 takes a polynomial bound on the
sensitivity in place of "F rational", and Duflo's condition is used as `E[α(W)ᵐ] ≤ 1`. Three proofs
need less than the book's: Theorem 7.1.1 needs no Sard theorem, Theorem 7.5.1 (ii) does not need
(7.27), and Proposition 7.2.2 does not need forward accessibility. The following are not formalised:
the survey of §7.6 (apart from Duflo's condition), Sard's theorem itself, the rational-function step
of Proposition 7.5.2, the gumleaf model on all of `ℝ²`, the adaptive control model with `α = 0` or
`σ_z = 0`, and the informal remarks. See [corrections](docs/corrections.md). The library contains
**1069 theorems**. Of these, 232 are in the Chapter 7 modules and 837 in the modules carried from
Chapters 1–6.

Four results carry the chapter.

* **Forward accessibility, the rank condition and continuous components** (`ForwardAccessibility`,
  `LocalInverse`, `NSSTChain`). The generalized controllability matrix `C_x^k(u)` of (7.11) is the
  derivative of `u ↦ Fₖ(x, u)` (`hasFDerivAt_controlMap`), and for `F(x, u) = Ax + Bu` it is the
  controllability matrix of (LCM3) (`genCtrb_linear`). Where `C_x^k(u)` is onto, the open mapping
  theorem for `C¹` maps makes `Fₖ(x, Oᵏ)` a neighbourhood of `Fₖ(x, u)`
  (`image_mem_nhds_of_hasFullRankAt`), so the rank condition (CM3) implies forward accessibility
  (`proposition_7_1_4_of_rank`). The converse is proved when the critical values of the control
  maps are null (`proposition_7_1_4_of_forwardAccessible`), and for `X = ℝ` with no such
  hypothesis: if every controllability vector vanishes, each `Fₖ(x, ·)` is locally constant on
  `Oᵏ`, so `A₊(x)` is countable (`countable_image_of_hasFDerivAt_zero`, `theorem_7_1_1`). The
  continuous component of (7.6)–(7.8) comes from straightening the map `(x, u) ↦ Fₖ(x, u)` near a
  point of full rank (`exists_straightening`, `exists_lsc_minorant`). The book's change of
  variables is replaced by an inequality in which the Jacobian is bounded by `2`, and its
  approximation by continuous functions by Fatou's lemma (`lowerSemicontinuous_lintegral_of_lsc`).
  Under (NSS3) every point then has an open small neighbourhood, and NSS(F) is a T-chain
  (`proposition_7_1_5`, `proposition_7_1_2`).
* **Minimal sets and ψ-irreducibility** (`MinimalSets`, `NSSIrreducibility`). Under (NSS3), for
  continuous `F` and open `U`, `A₊ᵏ(x)` meets `U` if and only if `Pᵏ(x, U) > 0`, and a closed set is
  absorbing if and only if it is invariant (`proposition_7_2_2_ii`, `proposition_7_2_2_i`); forward
  accessibility is not needed. A minimal set is absorbing, and under the rank condition the chain
  restricted to it is an open set irreducible, ψ-irreducible T-chain (`theorem_7_2_4_i`,
  `theorem_7_2_4_ii`). NSS(F) is ψ-irreducible if and only if CM(F) is M-irreducible
  (`theorem_7_2_6`). A point of `supp ψ` lies in the closure of every `A₊(y)`, which makes CM(F)
  M-irreducible (`isMIrreducible_of_forall_mem_closure`); conversely a globally attracting state is
  reachable, and Proposition 6.2.1 applies to the T-chain of Proposition 7.1.5. Three statements
  of pp. 155–156 are refuted (`minimal_literal_eq_empty`, `halving_noReach_nonempty`,
  `indecomposable_not_necessary`).
* **Periodic orbits and cycles** (`PeriodicOrbits`, `NSSPeriodicity`). Under the rank condition
  every point has an open neighbourhood `B` with `B →ᵏ C` for a non-empty open `C`
  (`proposition_7_3_1`, from `exists_uniform_reach`), and a minimal set contains a non-empty open
  `E` with `E →ⁿ E` (`lemma_7_3_2`). The classes `Gᵢ` of (7.18), indexed by Mathlib's `ZMod d` with
  `d` the g.c.d. of the return times (7.17), are disjoint closed sets forming a periodic orbit with
  union `M`, unique in the sense of Theorem 7.3.3 (`theorem_7_3_3`). For a connected control set
  they are the connected components of `M`, so `M` is aperiodic if and only if it is connected
  (`proposition_7_3_4`). The orbit is a `d`-cycle of NSS(F), `d` is the period of the chain, and
  every `d`-cycle agrees with the orbit up to `ψ`-null sets (`theorem_7_3_5_i`); M-irreducibility
  with an aperiodic minimal set gives a ψ-irreducible aperiodic T-chain (`theorem_7_3_5_ii`).
* **Sensitivity and e-chains** (`NSSEquicontinuity`). The sensitivity process (7.26) is the
  derivative of `Fₖ(·, u)` (`hasFDerivAt_controlMap_left`), and under the domination (7.27)
  `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]` (`theorem_7_5_1_i`). The mean value theorem in integral form
  (`enorm_controlMap_sub_le`) and Tonelli bound `E‖Φₖ(x) − Φₖ(y)‖` by
  `sup_{z ∈ [x, y]} E_z‖∇Φₖ‖ · ‖x − y‖`, and paths that are Lipschitz in mean give an e-chain
  (`isEChain_of_meanLipschitz`). So a bound on `sup_{y ∈ C} sup_k E_y‖∇Φₖ‖` for every compact `C`
  makes NSS(F) an e-chain without (7.27) (`theorem_7_5_1_ii`). The linear model under (LSS5)
  (`proposition_7_5_3`) and models satisfying Duflo's condition (`duflo_isEChain`) follow.

The library covers the chapter as follows.

* **Scalar models and forward accessibility** (§7.1.1). The reachable sets `A₊ᵏ(x)` and `A₊(x)`
  of (7.2)–(7.3), forward accessibility, the rank condition (CM2) and Theorem 7.1.1.
* **Continuous components for the scalar model** (§7.1.2). The density condition (SNSS3), the
  uniform and Gaussian laws, the kernel formula (7.6), the continuous component (7.7)–(7.8) and
  Proposition 7.1.2.
* **The simple bilinear model** (§7.1.3). The controllability vectors of p. 152, the one-step
  kernel without an everywhere non-trivial continuous component, Proposition 7.1.3 refuted for
  `θ = 1`, `b ≠ 0` and proved otherwise.
* **Multidimensional models** (§7.1.4). The matrices `Ξₖ`, `Λₖ`, the generalized controllability
  matrix (7.11) and its linear case (7.12), the rank condition (CM3), Proposition 7.1.4 (the "only
  if" half under the Sard hypothesis) and Proposition 7.1.5.
* **Minimality for the deterministic control model** (§7.2.1). The sets `A₊(E)`, `E⁰` and `Ω₊(C)`,
  the semigroup property, invariant sets, Propositions 7.2.1–7.2.3, the definition of a minimal set
  and its correction, and the minimal set `X₀` of the linear control model, unique under (LSS5).
* **M-irreducibility and ψ-irreducibility** (§7.2.2). Theorem 7.2.4, the case of a minimal state
  space, indecomposability and M-irreducibility with the two corrections of p. 156, the translation
  example, globally attracting states, Proposition 7.2.5 and Theorem 7.2.6.
* **Periodicity for control models** (§7.3.1). `k`-accessibility, Proposition 7.3.1, Lemma 7.3.2,
  periodic orbits, the return times (7.17) and classes (7.18), the period of a minimal set, Theorem
  7.3.3 and Proposition 7.3.4.
* **Periodicity of NSS(F)** (§7.3.2). Periodic orbits are cycles, the period of a cycle divides the
  period of the orbit, the orbit is the cycle up to null sets, and Theorem 7.3.5.
* **Forward accessible examples** (§7.4). The dependent parameter bilinear model and Proposition
  7.4.1; the gumleaf attractor and Proposition 7.4.2 on `{xᵃ ≠ 0, xᵇ ≠ 0}`; the adaptive control
  model, the corrections to its interior, its zero-noise limit and Proposition 7.4.3.
* **Equicontinuity** (§§7.5–7.6). The sensitivity process (7.26), Theorem 7.5.1 and the case of
  bounded disturbances, Proposition 7.5.2 under a polynomial sensitivity bound, Proposition 7.5.3,
  and Duflo's condition from the commentary.

All names are in the namespace `MeynTweedie.NonlinearStateSpace`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ControlModel](NonlinearStateSpace/ControlModel.lean) | 33 | §§7.1.1, 7.2.1: the reachable sets `A₊ᵏ(x)`, `A₊(x)`, `A₊(E)`, `E⁰` and `Ω₊(C)`, the semigroup property, forward accessibility, invariant sets, Proposition 7.2.1, `k`-accessibility, periodic orbits |
| [ForwardAccessibility](NonlinearStateSpace/ForwardAccessibility.lean) | 18 | §§7.1.1, 7.1.4: the derivatives `Ξ`, `Λ`, the generalized controllability matrix (7.11) as the derivative of the control map, its linear case (7.12), the sensitivity process (7.26), the rank conditions (CM2)–(CM3), Proposition 7.1.4, Theorem 7.1.1 |
| [LocalInverse](NonlinearStateSpace/LocalInverse.lean) | 8 | §7.1.2: lower semicontinuity of products and of integrals (Fatou), product densities, straightening a submersion, the minorant behind (7.6)–(7.8), uniform reachability for Proposition 7.3.1 |
| [NSSTChain](NonlinearStateSpace/NSSTChain.lean) | 12 | §§7.1.2, 7.1.4: the density condition (SNSS3)/(NSS3) and the control set, the kernel formula (7.6), the continuous component, Propositions 7.1.5 and 7.1.2 |
| [MinimalSets](NonlinearStateSpace/MinimalSets.lean) | 29 | §§7.2.1–7.2.2: minimal sets and the correction to their definition, Proposition 7.2.3, indecomposability, M-irreducibility, globally attracting states, the three examples of p. 156, Proposition 7.2.5, Proposition 7.2.2 |
| [NSSIrreducibility](NonlinearStateSpace/NSSIrreducibility.lean) | 8 | §7.2.2: restriction of a T-chain to an absorbing set, Theorem 7.2.4, the minimal state space, Theorem 7.2.6 |
| [PeriodicOrbits](NonlinearStateSpace/PeriodicOrbits.lean) | 37 | §7.3.1: Proposition 7.3.1, Lemma 7.3.2, the return times (7.17) and classes (7.18), the period of a minimal set, Theorem 7.3.3, Proposition 7.3.4 |
| [NSSPeriodicity](NonlinearStateSpace/NSSPeriodicity.lean) | 10 | §7.3.2: periodic orbits as cycles, divisibility of periods, uniqueness up to null sets, globally attracting states are reachable, Theorem 7.3.5 |
| [NSSEquicontinuity](NonlinearStateSpace/NSSEquicontinuity.lean) | 15 | §§7.5–7.6: continuity of the sensitivity process, Theorem 7.5.1 and the bounded case, paths Lipschitz in mean, Propositions 7.5.3 and 7.5.2, Duflo's condition |
| [NSSExamples](NonlinearStateSpace/NSSExamples.lean) | 44 | §§7.1.3, 7.2.1, 7.4.1–7.4.3: the uniform law, the bilinear model and Proposition 7.1.3 refuted and corrected, the linear control model, the dependent parameter bilinear model and Proposition 7.4.1, the gumleaf model and Proposition 7.4.2, the zero-noise limit and the interior corrections for the adaptive control model |
| [NSSAdaptiveControl](NonlinearStateSpace/NSSAdaptiveControl.lean) | 18 | §7.4.3: derivatives and the rank of the second order controllability matrix, Gaussian densities, the absorbing state space, continuous components at every point of it, Proposition 7.4.3 |

Carried from the Chapter 6 project `TopologyContinuity` (837 theorems): every module of that
project, identical to the copies there except for the namespace. Its own Chapter 6 modules (130
theorems):

* `FellerChains` (40): reachable points (`IsReachable`) and open set irreducibility
  (`IsOpenSetIrreducible`), used in Theorems 7.2.4, 7.2.6 and 7.3.5.
* `TChains` (14): continuous components and T-chains (`IsContinuousComponent`, `IsTChain`), with
  Propositions 6.2.1, 6.2.2 and 6.2.4, used throughout §§7.1–7.4.
* `EChains` (16): e-chains (`IsEChain`), used in §7.5.
* `LinearTChains` (10): the eigenvalue condition (LSS5) (`IsStableMatrix`,
  `isStableMatrix_geometric`), used for the linear control model and Proposition 7.5.3.
* `FellerModels` (12), `CompactPetite` (16), `TChainModels` (10), `EChainsStability` (12): the rest
  of Chapter 6. No Chapter 7 module imports `EChainsStability`.

Carried in turn by `TopologyContinuity` from the earlier projects (707 theorems; see that project's
README for how they differ from the originals):

* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The potential kernel `U` (`potKernel`) is
  used for reachability. No Chapter 7 module imports `StateSpaces` or `SpecificMatrices`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Absorbing sets and restricted kernels (`IsAbsorbing`,
  `restrictKernel`), ψ-irreducibility and the resolvent `K_{a_{1/2}}` (`IsPhiIrreducible`,
  `resolventHalf`), maximal irreducibility measures (`IsMaximalIrreducibility`) and the
  controllability map `ctrbMap` are used throughout. No Chapter 7 module imports
  `CountableIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Small sets (`IsSmallSet`,
  `IsSmall`), the sampling distributions `diracDist`, the g.c.d. `setGcd` and the cycles and
  periods of Theorem 5.4.4 (`IsCycle`, `IsPeriod`, `IsAperiodic`) are used in §§7.1–7.4. No
  Chapter 7 module imports `CycleAperiodic`, `ForwardRecurrence` or `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). The control maps
  `Fₖ` (`controlMap`) and random recursions (`recursionKernel`), LSS(F, G) (`lssMatrixKernel`), and
  the models NSS(F) (`nssKernel`), simple bilinear (`bilinearKernel`), dependent parameter bilinear
  (`dblKernel`), gumleaf (`gumleafKernel`) and adaptive control (`sacKernel`,
  `sacGaussianKernel`) come from these modules.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
