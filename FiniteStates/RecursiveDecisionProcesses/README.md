# Recursive decision processes in Lean

This is the `FiniteStates/RecursiveDecisionProcesses/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/RecursiveDecisionProcesses`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 8, "Recursive Decision Processes"
(pp. 247–291), including every provable exercise (Exercises 8.1.1–8.1.19,
8.2.1–8.2.11, 8.3.1 and 8.3.3–8.3.10). The library contains **431 theorems** and
audits every declaration, including structure constructors and projections.

* **RDPs** (§8.1.1–§8.1.3.2): `R = (Γ, V, B)` with monotone, consistent aggregator;
  policy operators, well-posedness, global stability, continuity, greedy policies,
  the Bellman operator `T = ⋁_σ T_σ` (Exercises 8.1.6–8.1.9), HPI, OPI and the
  Howard operator (Algorithms 8.1–8.2, Exercise 8.1.10).
* **Optimality** (§8.1.3.3–§8.1.4): **Theorem 8.1.1** and **Theorem 8.1.2**, whose
  proofs the book defers to Chapter 9, are proved here from one comparison lemma
  (`T_τ v_σ ≤ v_σ ⇒ v_τ ≤ v_σ`, and the reverse), which global stability gives by
  iterating `T_τ` and boundedness gives by Knaster–Tarski. HPI improves and
  terminates because the finitely many policies cannot carry a strictly increasing
  value sequence; its terminal value is a fixed point of `T`, and every fixed point
  of `T` in `V` dominates every `v_σ`, so it is `v*`. OPI and VFI converge, squeezed
  between `T_{σ*}ᵏv_σ` and `v*`, and the greedy policies are eventually optimal.
  Nonstationary policies (§8.1.3.5, Exercise 8.1.11), bounded RDPs
  (Exercises 8.1.12–8.1.13), and topologically conjugate RDPs
  (Proposition 8.1.3, Exercise 8.1.18).
* **Examples** (§8.1.1): MDPs, cake eating, optimal stopping, the Stokey–Lucas form
  as an MDP, state-dependent discounting, risk-sensitive, quantile and Epstein–Zin
  preferences (Exercises 8.1.1–8.1.5); shortest paths and the ill-posed two-cycle
  of Example 8.1.14.
* **Contracting RDPs** (§8.2.1): Proposition 8.2.1, Corollary 8.2.2, the error
  bound of Proposition 8.2.3, Blackwell's condition (Exercise 8.2.3), and its
  applications: MDPs with `v_σ = (I − βP_σ)⁻¹r_σ` (Exercises 8.1.14, 8.2.1), optimal
  stopping (Example 8.2.1, Exercise 8.1.15), bounded state-dependent discounting
  (Exercise 8.2.4), optimal savings (Exercise 8.2.5), quantile job search
  (Exercise 8.2.6), optimal default (Exercise 8.2.7), risk-sensitive RDPs
  (Proposition 8.3.1) and quantile RDPs (Exercise 8.3.1).
* **Eventually contracting RDPs** (§8.2.2): Proposition 8.2.4, the completion of the
  proof of Proposition 6.2.2, firm exit with state-dependent interest rates
  (Exercise 8.2.8), and boundedness under Proposition 6.2.2 (Exercise 8.1.16).
* **Convex and concave RDPs** (§8.2.3): Exercise 8.2.9, Proposition 8.2.5 (by Du's
  theorem), and MDPs on `[(r₁ − ε)/(1 − β), (r₂ + ε)/(1 − β)]` (Exercises
  8.2.10–8.2.11).
* **Adversarial agents and robustness** (§8.3.2–§8.3.3): Proposition 8.3.2,
  Exercise 8.3.3, the perturbed MDP (Exercise 8.3.4, Lemma 8.3.3), robust control
  (Proposition 8.3.4), robust job search (Example 8.3.1), penalties (8.50), the
  variational formula (8.51) for KL divergence on a finite set, and the reduction of
  KL-penalised robust control to risk-sensitive preferences.
* **Epstein–Zin RDPs** (§8.1.4.1): the transformed RDP (8.24), Exercise 8.1.19,
  Lemma 8.1.5 and Proposition 8.1.4.
* **Smooth ambiguity** (§8.3.4): Exercises 8.3.5–8.3.9, Lemma 8.3.6 and
  Proposition 8.3.5, for a finite parameter set.
* **Minimization** (§8.3.5): Theorem 8.3.7 (deferred by the book to §9.2.3), by
  reflecting `B` to `−B(x, a, −v)`; shortest paths (Exercise 8.1.17,
  Proposition 8.3.8) and negative discount rates (Exercise 8.3.10,
  Proposition 8.3.9).

The main entry points are `RDP.optimality_of_globallyStable`,
`RDP.optimality_of_bounded`, `RDP.opi_converges`, `RDP.isGloballyStable_iff_of_conj`,
`RDP.IsContracting.isGloballyStable`, `RDP.IsContracting.norm_vstar_sub_vσ_le`,
`RDP.SatisfiesBlackwell.isContracting`, `RDP.IsEventuallyContracting.isGloballyStable`,
`RDP.IsConcaveRDP.isGloballyStable`, `adversarialRDP_isConcaveRDP`, `klDuality`,
`MDP.riskSensitive_B_eq_robust`, `MDP.epsteinZin_isGloballyStable`,
`SmoothAmbiguity.toRDP_isGloballyStable`, `RDP.minOptimality` and
`pathRDP_minOptimal`, all in the namespace `SargentStachurski.RecursiveDecisionProcesses`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (the smooth ambiguity exponent and value space;
bounded RDPs need `[v₁, v₂] ⊆ V`, not convexity; the reward in the penalised robust
aggregator is `r + βd`; the quantile operator at `τ = 0`), the hypotheses the book
leaves implicit, and what is not formalised: the figures, listings and the
replication Exercise 8.3.2.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](RecursiveDecisionProcesses/Basics.lean) | 18 | Markov matrices, contractions and Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 (restated) |
| [SpectralRadius](RecursiveDecisionProcesses/SpectralRadius.lean) | 29 | `ρ(A)`, Gelfand's formula, the Neumann series, Ex 2.2.28 (restated) |
| [Resolvent](RecursiveDecisionProcesses/Resolvent.lean) | 11 | The resolvent series (restated) |
| [PerronFrobenius](RecursiveDecisionProcesses/PerronFrobenius.lean) | 20 | Thm 2.3.1, nonnegative case; Lemmas 2.3.2–2.3.3 (restated) |
| [Irreducible](RecursiveDecisionProcesses/Irreducible.lean) | 10 | Thm 2.3.1, irreducible case (restated) |
| [LinearValuation](RecursiveDecisionProcesses/LinearValuation.lean) | 25 | Thm 6.1.1, `ρ(βP) = β`, Lemma 6.1.4, Thm 6.1.5, Example 6.1.2, Prop 6.1.6 (restated) |
| [OrderFixedPoints](RecursiveDecisionProcesses/OrderFixedPoints.lean) | 15 | Global stability on a set, conjugacy, Thm 7.1.1, Thm 7.1.3 (restated) |
| [PowerAffine](RecursiveDecisionProcesses/PowerAffine.lean) | 27 | Ex 7.1.7–7.1.8, Thm 7.1.4 (restated) |
| [CertaintyEquivalents](RecursiveDecisionProcesses/CertaintyEquivalents.lean) | 33 | Entropic, Kreps–Porteus and quantile operators (restated) |
| [Koopmans](RecursiveDecisionProcesses/Koopmans.lean) | 29 | Aggregators and Koopmans operators (restated) |
| [EpsteinZin](RecursiveDecisionProcesses/EpsteinZin.lean) | 13 | Epstein–Zin Koopmans operators, Prop 7.2.3, Prop 7.3.5 (restated) |
| [RDP](RecursiveDecisionProcesses/RDP.lean) | 29 | §8.1.1–8.1.3.2, (8.1)–(8.18), Ex 8.1.6–8.1.11, Algorithms 8.1–8.2 |
| [Optimality](RecursiveDecisionProcesses/Optimality.lean) | 26 | Thm 8.1.1, Thm 8.1.2, §8.1.3.5, Ex 8.1.12–8.1.13, Prop 8.1.3, Ex 8.1.18 |
| [Examples](RecursiveDecisionProcesses/Examples.lean) | 12 | Examples 8.1.1–8.1.8, 8.1.14, Ex 8.1.1–8.1.5 |
| [Contracting](RecursiveDecisionProcesses/Contracting.lean) | 26 | §8.2.1, Props 8.2.1, 8.2.3, 8.3.1, Cor 8.2.2, Examples 8.1.12–8.1.13, 8.1.15–8.1.16, 8.2.1, Ex 8.1.14–8.1.15, 8.2.1–8.2.7, 8.3.1 |
| [EventuallyContracting](RecursiveDecisionProcesses/EventuallyContracting.lean) | 6 | §8.2.2, Prop 8.2.4, Prop 6.2.2, Ex 8.1.16, 8.2.8 |
| [ConcaveRDP](RecursiveDecisionProcesses/ConcaveRDP.lean) | 9 | §8.2.3, Prop 8.2.5, Ex 8.2.9–8.2.11 |
| [Adversarial](RecursiveDecisionProcesses/Adversarial.lean) | 26 | §8.3.2–8.3.3, Props 8.3.2, 8.3.4, Lemma 8.3.3, Example 8.3.1, Ex 8.3.3–8.3.4, (8.50)–(8.51) |
| [EpsteinZinRDP](RecursiveDecisionProcesses/EpsteinZinRDP.lean) | 8 | §8.1.4.1, (8.23)–(8.25), Ex 8.1.19, Lemma 8.1.5, Prop 8.1.4 |
| [SmoothAmbiguity](RecursiveDecisionProcesses/SmoothAmbiguity.lean) | 37 | §8.3.4, (8.52)–(8.54), Ex 8.3.5–8.3.9, Lemma 8.3.6, Prop 8.3.5 |
| [Minimization](RecursiveDecisionProcesses/Minimization.lean) | 22 | §8.3.5, Thm 8.3.7, Ex 8.1.17, 8.3.10, Props 8.3.8–8.3.9 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
