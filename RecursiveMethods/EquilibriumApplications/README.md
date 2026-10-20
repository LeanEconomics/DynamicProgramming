# SLP Chapter 16: Applications of Equilibrium Theory, in Lean

This is the `RecursiveMethods/EquilibriumApplications` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 16 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 16 applies the welfare theorems of Chapter 15 to models of earlier chapters. The solution
of a planning problem is a competitive equilibrium of an economy of identical consumers and
identical constant-returns firms: the one-sector growth model, both with one market at date 0 and
with sequential spot markets (§16.1); the many-sector stochastic growth model, with the security
prices it implies (§16.2); a model of sustained growth, on a commodity space `S_θ` of sequences
growing at most like `θᵗ` (§16.3); and industry investment under uncertainty, in which industry
equilibrium and surplus maximisation coincide (§16.4). §16.5 generalises Theorem 15.6 by
truncating to an arbitrary allocation instead of zero. §16.6 is an exchange economy on `ℓ∞` in
which every supporting price puts all its weight at infinity. §16.7 finds the Pareto optima of a
growth model whose consumers have recursive preferences, through the support function of the
utility possibility set and a contraction.

Chapter 16 has no numbered theorems. Its one numbered assumption (Assumption 16.1) and all 41
parts of Exercises 16.1–16.7 are formalised, with the displayed equations and the claims of the
text. Several claims are false as stated. Each is refuted in Lean, by a counterexample or a proof
of inconsistency, and a corrected statement is proved: the restrictions on `f` in §16.1 (a bounded
`f(k) = F(k, 1) + (1 − δ)k` forces `δ = 1`, and boundedness does not give the fixed point `k̄`);
the price (4) on p. 480, which has a spurious factor `f′(k)`; Exercise 16.2a (the technology
assumptions of §10.3 give neither truncation nor an interior point); Exercise 16.2c (the
consumer's choices can leave the domain of `w`); Exercise 16.2d (the envelope identity holds only
at the equilibrium price); Exercise 16.2h (additivity fails for bubble solutions of (3)); the
production set of §16.3 (as printed it lies in no `S_θ`); Exercise 16.3d (utility is unbounded on
`X` when `σ ≤ 1`); the use of Theorems 15.4–15.6 in Exercise 16.4e (Assumption 15.8′ fails); and,
in §16.7, the closedness of `Y(k̂)` (Exercise 16.7a), the nonsatiation the welfare theorems need,
Exercise 16.7b for weights on the boundary of the simplex, Exercise 16.7c without closedness of
`U(κ)`, the convexity claim of Exercise 16.7d, `T : F → F` (Exercise 16.7e), and both the hint and
the contraction claim of Exercise 16.7f. Several steps of the solutions manual are also wrong
(Exercises 16.1b, 16.6a and 16.6c, with counterexamples, and incomplete arguments in 16.1c,
16.1e, 16.1f, 16.3a, 16.3b and 16.3d); the results they support are true and are proved. The example of
§16.6 is carried to a conclusion the book does not state: the economy has no competitive
equilibrium in `ℓ∞`. Some results are proved only under added hypotheses: finitely many shocks for
parts of §16.2, an interior allocation in Exercise 16.1d, and a bound on capital for parts of
§16.7. The chapter introduction and the bibliographic notes (§16.8) are not formalised. See
[corrections](docs/corrections.md). The library contains **1043 theorems**. Of these, 681 are in
the Chapter 16 modules, 209 in the modules carried from Chapter 15 and 153 in the modules carried
from Chapter 6.

* **Growth under certainty: the welfare theorems** (§16.1, pp. 476–478). The restrictions on `β`,
  `U` and `f`, with "`f` bounded" replaced by `f(k) < k` for `k > k̄`, so that feasible capital is
  bounded by `max {k̂, k̄}`. Symmetric Pareto optima are the planner's solutions. Exercise 16.1a
  (a unique optimum, by Tychonoff compactness), 16.1b (Assumptions 15.1–15.5, with a corrected
  interior point and cheaper point) and 16.1c (Assumptions 15.6–15.7 and prices `p ∈ ℓ₁` with
  every `p_t > 0`). Interest rates and Exercise 16.1d, for an interior allocation, with the
  first-order conditions proved from (E2) and (E3) by perturbation.
* **Growth under certainty: sequential markets** (§16.1, pp. 478–481). The firm's equation (1)
  and the household's equation (2) with the corrected price (4); (1) is not a contraction, and has
  a unique bounded continuous solution because the discount factors along the equilibrium path
  are bounded by `M βⁿ` uniformly in the state. Exercise 16.1e–g: the policies `h` and `ω` are
  single-valued and continuous, (R3)–(R4) hold, and the sequential allocation is the optimum of
  Exercise 16.1a. Proved first for a planner's policy with stated properties, then with `g` the
  policy of the Bellman equation (3), whose properties are derived from Chapters 5–6.
* **Many-sector stochastic growth** (§16.2, pp. 481–482). The commodity space `L∞` over time and
  states; Exercise 16.2a under two added hypotheses (free disposal of consumption, a uniformly
  positive feasible plan), each shown necessary by a counterexample; Exercise 16.2b by Theorems
  15.4 and 15.9, with the cheaper point that Theorem 15.9 alone does not give. One consumption
  good.
* **Pricing securities** (§16.2, pp. 482–485). The consumer's equation (1) with a domain condition
  on the credit limit: Exercise 16.2c for finitely many shocks, and for a Feller transition on a
  compact shock space. Exercise 16.2d corrected (`w₁(0) = U′(c + δ*(0))`) and its converse at the
  equilibrium price, by a verification argument; the pricing equations (2) and (3) (Exercise
  16.2g). Exercises 16.2e, 16.2f (lottery tickets are priced risk-neutrally) and 16.2h
  (Modigliani–Miller, for bounded prices) for a general shock space; the one-step martingale
  property of p. 485.
* **Sustained growth** (§16.3). `S_θ` as a normed space isometric to `ℓ∞`; Exercise 16.3a
  (`Y ⊆ S_θ` iff `θ ≥ θ̂ = γ^{1/(1−α)}`) and 16.3b (an interior point iff `θ ≤ θ̂`); continuity of
  `u` (Exercise 16.3c); CRRA utility, and Exercise 16.3d corrected (finite, bounded on bounded
  sets and continuous; bounded only for `σ > 1`). Exercise 16.3e: (i) equilibria are optima; (ii)
  an optimum whose lower bound does not bind is an equilibrium, both through Theorem 15.4 and
  directly with the price `p_t = βᵗ U′(x_t)`.
* **Industry investment** (§16.4). The adjustment cost, demand and surplus of §10.4; the
  production set (1), convex despite the equality constraint on investment and with constant
  returns; industry equilibrium (I1)–(I3) and surplus maximisation (I4). Exercise 16.4a
  (`J` firms aggregate to one), 16.4b and 16.4c directly; the synthetic consumer, Exercise 16.4d,
  and Exercise 16.4e, where Theorem 15.3 gives (b) and Theorem 15.4 gives some supporting price,
  but Assumption 15.8′ fails, so Theorem 15.9 cannot give `L¹` prices.
* **Truncation** (§16.5). Exercise 16.5a; Assumption 16.1, which is Assumptions 15.6–15.7 when
  `a = b = 0` and is strictly weaker; Exercise 16.5b–e, using only Assumptions 15.1, 15.2 and
  16.1; the competitive equilibrium at the regular price `ψ`, and Theorem 15.6 as a special case.
* **A peculiar example** (§16.6). Exercise 16.6a; the constant prices are not a continuous
  functional on `ℓ∞` (16.6b); every supporting price has regular part `ψ = 0` (16.6c); in `ℓ₁`
  the production set has empty interior and constant prices give an equilibrium (16.6d). Every
  supporting `φ` on `ℓ∞` has `φ(x*) = 0`, and there is no competitive equilibrium in `ℓ∞`.
* **Many consumers: preferences, technology, Pareto optima** (§16.7, pp. 495–498). Aggregators
  (W1)–(W5) and technology (T1)–(T7); Exercise 16.7a, with closedness for capital paths that need
  not be bounded, or under a capital bound (T8); the welfare theorems, given nonsatiation and a
  cheaper point; the utility possibility set, its support function (2) and the recursion (3);
  Exercises 16.7b and 16.7c, corrected.
* **Many consumers: the operator `T`** (§16.7, pp. 498–499). Exercise 16.7d (compact, convex
  when `f` is concave in `κ′`); on functions of support-function type, the hint `𝒰ᵃ = B`, the
  contraction of Exercise 16.7f, and Berge's theorem for Exercise 16.7e; the Principle of
  Optimality question of p. 499 (the support function is the unique admissible solution of (4));
  Exercise 16.7g. Counterexamples on one technology refute 16.7a–f as stated.

All names are in the namespace `StokeyLucasPrescott.EquilibriumApplications`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [GrowthCertainty](EquilibriumApplications/GrowthCertainty.lean) | 47 | §16.1 set-up, Exercise 16.1b–c (assumptions), interest rates |
| [GrowthCertaintyOptimum](EquilibriumApplications/GrowthCertaintyOptimum.lean) | 7 | Symmetric optima; Exercise 16.1a–c |
| [GrowthCertaintyPrices](EquilibriumApplications/GrowthCertaintyPrices.lean) | 5 | Exercise 16.1d |
| [GrowthCertaintyPlanner](EquilibriumApplications/GrowthCertaintyPlanner.lean) | 14 | The planner's policy (3) and the price (4) |
| [GrowthCertaintyRecursive](EquilibriumApplications/GrowthCertaintyRecursive.lean) | 30 | The firm's equation (1); Exercise 16.1e for the firm |
| [GrowthCertaintyHousehold](EquilibriumApplications/GrowthCertaintyHousehold.lean) | 20 | The household's equation (2); Exercise 16.1e for the household |
| [GrowthCertaintySequential](EquilibriumApplications/GrowthCertaintySequential.lean) | 33 | (R1)–(R4); Exercise 16.1f–g |
| [GrowthCertaintyBellman](EquilibriumApplications/GrowthCertaintyBellman.lean) | 5 | Exercise 16.1e–g with `g` the policy of (3) |
| [ManySector](EquilibriumApplications/ManySector.lean) | 33 | §16.2 consumption side; Exercise 16.2a for `(C, u)` |
| [ManySectorTech](EquilibriumApplications/ManySectorTech.lean) | 21 | The technology of §10.3; Exercise 16.2a; two counterexamples |
| [ManySectorPrices](EquilibriumApplications/ManySectorPrices.lean) | 4 | Exercise 16.2b |
| [ManySectorSecurities](EquilibriumApplications/ManySectorSecurities.lean) | 15 | (1) of §16.2; Exercise 16.2c, finite shocks |
| [ManySectorFeller](EquilibriumApplications/ManySectorFeller.lean) | 15 | Exercise 16.2c, Feller transition on a compact shock space |
| [ManySectorEnvelope](EquilibriumApplications/ManySectorEnvelope.lean) | 10 | Exercise 16.2d; (2); Exercise 16.2g |
| [ManySectorVerification](EquilibriumApplications/ManySectorVerification.lean) | 4 | Exercise 16.2d at the equilibrium price |
| [ManySectorPricing](EquilibriumApplications/ManySectorPricing.lean) | 8 | Exercises 16.2e, 16.2f, 16.2h; (3′) and the martingale property |
| [SustainedGrowth](EquilibriumApplications/SustainedGrowth.lean) | 24 | (1) of §16.3, `S_θ`, `Y`; Exercise 16.3a–b |
| [SustainedGrowthUtility](EquilibriumApplications/SustainedGrowthUtility.lean) | 28 | CRRA utility; Exercise 16.3c–d |
| [SustainedGrowthWelfare](EquilibriumApplications/SustainedGrowthWelfare.lean) | 17 | Exercise 16.3e |
| [SustainedGrowthPrices](EquilibriumApplications/SustainedGrowthPrices.lean) | 8 | Exercise 16.3e(ii) with inner-product prices |
| [IndustryModel](EquilibriumApplications/IndustryModel.lean) | 38 | §10.4 primitives; the production set (1) of §16.4 |
| [IndustryEquilibrium](EquilibriumApplications/IndustryEquilibrium.lean) | 21 | (I1)–(I4); Exercise 16.4b–c |
| [IndustryFirms](EquilibriumApplications/IndustryFirms.lean) | 8 | Exercise 16.4a |
| [IndustryWelfare](EquilibriumApplications/IndustryWelfare.lean) | 27 | The synthetic consumer; Exercise 16.4d–e |
| [IndustryLinfty](EquilibriumApplications/IndustryLinfty.lean) | 5 | Assumption 15.8′ fails for the industry |
| [Truncation](EquilibriumApplications/Truncation.lean) | 17 | §16.5: (1)–(4), Assumption 16.1, Exercise 16.5 |
| [PeculiarModel](EquilibriumApplications/PeculiarModel.lean) | 43 | §16.6 economy; Exercise 16.6a |
| [PeculiarPrices](EquilibriumApplications/PeculiarPrices.lean) | 22 | (1)–(3) of §16.6; Exercise 16.6b–c; no equilibrium in `ℓ∞` |
| [PeculiarEllOne](EquilibriumApplications/PeculiarEllOne.lean) | 11 | Exercise 16.6d |
| [ManyConsumers](EquilibriumApplications/ManyConsumers.lean) | 23 | (W1)–(W5), (T1)–(T7), `Y(k̂)`; Exercise 16.7a; welfare theorems |
| [ManyConsumersClosed](EquilibriumApplications/ManyConsumersClosed.lean) | 5 | Exercise 16.7a: closedness with unbounded capital paths |
| [ManyConsumersPareto](EquilibriumApplications/ManyConsumersPareto.lean) | 25 | (1)–(3) of §16.7; Exercise 16.7b–c |
| [ManyConsumersOperator](EquilibriumApplications/ManyConsumersOperator.lean) | 34 | (4), `F`, `T`; Exercises 16.7d, 16.7f, 16.7g; p. 499 |
| [ManyConsumersBerge](EquilibriumApplications/ManyConsumersBerge.lean) | 18 | Exercise 16.7e corrected; continuity of `v`; Exercise 16.7g |
| [ManyConsumersCapital](EquilibriumApplications/ManyConsumersCapital.lean) | 10 | The capital bound (T8); `U(κ)` closed; Exercise 16.7c and (4) under (T8) |
| [ManyConsumersExample](EquilibriumApplications/ManyConsumersExample.lean) | 26 | Counterexamples to Exercise 16.7a–f |

Carried from the Chapter 15 project `ParetoOptimaEquilibria` (209 theorems), identical except for
the namespace and imports:

* `Economy`, `Welfare`, `WelfareSecond` (22): economies, Pareto optima and competitive equilibria,
  Assumptions 15.1–15.5, Theorem 15.3, Theorem 15.4 and the Remark after it, used in §§16.1–16.4,
  16.6 and 16.7.
* `SequencePrices`, `SequenceInfinity`, `SequenceAssumptions`, `SequenceTailUtility`,
  `SequenceSupport` (99): Lemma 15.5, Assumptions 15.6–15.7, the aggregators of Exercise 15.10 and
  Theorem 15.6, used in §§16.1, 16.5, 16.6 and 16.7.
* `LinftyPrices`, `LinftyAssumptions`, `LinftyTimeState` (88): Lemma 15.7, Theorem 15.8, the space
  (8) of §15.4, Assumptions 15.8′–15.9′ and Theorem 15.9, used in §§16.2 and 16.4.

Carried from the Chapter 6 project `DeterministicDynamics` (153 theorems), as the modules
`GrowthCertaintyDD*` in the nested namespace `GrowthCertaintyDD`, identical except for the
namespace and imports; they are used to derive the planner's policy in Exercise 16.1e–g:

* `GrowthCertaintyDDContraction`, `GrowthCertaintyDDCorrespondences`, `GrowthCertaintyDDMaximum`
  (24): Theorem 3.2, hemi-continuity, Theorems 3.6 and 3.8.
* `GrowthCertaintyDDExtendedReals`, `GrowthCertaintyDDPrinciple`, `GrowthCertaintyDDAssumption42`,
  `GrowthCertaintyDDBoundedReturns`, `GrowthCertaintyDDConcavity`, `GrowthCertaintyDDEnvelope`,
  `GrowthCertaintyDDEulerEquations` (73): Theorems 4.2–4.10 and 4.15.
* `GrowthCertaintyDDOneSectorGrowth`, `GrowthCertaintyDDWeakConcavity`,
  `GrowthCertaintyDDGrowthDifferentiability` (25): Exercise 5.1a–d.
* `GrowthCertaintyDDGrowthStability` (31): §6.1, Exercise 6.1 and Proposition 6.1.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
