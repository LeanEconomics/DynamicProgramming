# Nonlinear valuation in Lean

This is the `FiniteStates/NonlinearValuation/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/NonlinearValuation`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 7, "Nonlinear Valuation" (pp. 213–245),
including every provable exercise (Exercises 7.1.1–7.1.9, 7.2.1–7.2.4,
7.2.6–7.2.9, 7.3.1–7.3.22). The library contains **251 theorems** and audits
every declaration, including structure constructors and projections.

* **Order fixed points** (§7.1.1–§7.1.2): Theorem 7.1.1 (Knaster–Tarski) on order
  intervals of `ℝ^X`, which are complete lattices; Exercise 7.1.1; Theorem 7.1.3
  (Du) under each of its four conditions, proved here (the book cites Du, 1990):
  for concave `T` with `Tv₁ ≥ v₁ + δ(v₂ − v₁)`, `Tᵏv₁ ≥ (1 − λₖ)v₁ + λₖTᵏv₂` with
  `1 − λₖ = (1 − δ)ᵏ`, so every orbit is squeezed onto the fixed point; the convex
  cases by reflection. Exercise 7.1.6.
* **One dimension** (§7.1.2.1): Proposition 7.1.2, with the Solow–Swan model
  (Exercise 7.1.2), the counterexample of Exercise 7.1.3, general production under
  the Inada conditions (Exercise 7.1.4) and the aggregate-uncertainty law of
  Fajgelbaum et al. (Exercise 7.1.5).
* **The power-transformed affine equation** (§7.1.3): the shape of
  `t ↦ (h + t^{1/θ})^θ`, convex for `θ ∈ (0, 1]` and concave otherwise, from its
  derivative `(1 + ht^{−1/θ})^{θ−1}` (Exercises 7.1.7–7.1.8); **Theorem 7.1.4**, for
  irreducible `A ≥ 0` and `h ≫ 0`, `v ↦ [h + (Av)^{1/θ}]^θ` is globally stable on
  `(0, ∞)^X` iff `ρ(A)^{1/θ} < 1`, with no positive fixed point otherwise. The book
  cites Stachurski et al. (2022); the proof here applies Du's theorem on intervals
  `[ce, Ce]` around the Perron–Frobenius eigenvector. Exercise 7.1.9 (Kleinman et
  al.): a unique positive Markov consumption rate iff `ρ(A)^ψ < 1`.
* **Recursive preferences** (§7.2): the time additive recursion (7.6); the
  entropic risk-adjusted expectation, its translation property, the Gaussian
  formula `E_θ[ξ] = Eξ + θ Var ξ/2` and Lemma 7.2.1 (strict iff `Var ξ > 0`);
  Proposition 7.2.2; the Gaussian AR(1) solution `v(x) = ax + b` (Exercise 7.2.4);
  the IID closed form (Exercise 7.2.6); Epstein–Zin preferences, the conjugacy
  `v ↦ v^γ` (Lemma 7.2.4, Exercise 7.2.8), Proposition 7.2.3, and the infinite slope
  at zero that defeats contraction arguments (Exercise 7.2.9).
* **Certainty equivalents** (§7.3.1.1–§7.3.1.3): linear (exactly the Markov
  matrices, Exercise 7.3.1), entropic, Kreps–Porteus and quantile operators;
  constant-subadditivity and nonexpansiveness; Kreps–Porteus is subadditive for
  `γ ≥ 1` and superadditive for `γ ≤ 1` (Example 7.3.5), hence convex or concave
  (Lemma 7.3.1); the entropic operator is concave for `θ < 0` ((7.17), proved by
  the weighted AM–GM inequality); monotonicity under monotone kernels.
* **Koopmans operators** (§7.3.1.4–§7.3.3): aggregators, `K = A ∘ R`, the
  elasticity of intertemporal substitution `1/(1 − α)` (Exercise 7.3.14),
  finite-horizon values (Exercise 7.3.15), monotone lifetime values (Lemma 7.3.2,
  Exercise 7.3.16), Blackwell aggregators and Proposition 7.3.3, quantile
  preferences, Uzawa aggregation with Proposition 7.3.4 and Exercise 7.3.20, and
  Epstein–Zin preferences with state-dependent discounting (Proposition 7.3.5,
  Exercises 7.3.21–7.3.22).

The main entry points are `knaster_tarski`, `du_concave`, `du_convex`,
`globallyStableOn_of_concave`, `globallyStableOn_powG_iff`, `not_isFixedPt_powG`,
`existsUnique_kleinmanSol_iff`, `entExp_le_mean`, `entExp_ne_mean`,
`globallyStable_riskSensitive`, `globallyStableOn_ez`, `globallyStableOn_ezK_iff`,
`superadditive_kpR`, `concaveOn_entR`, `isContractionOn_koopmans`,
`globallyStableOn_uzawa_concave` and `monotone_ez_lifetimeValue`, all in the
namespace `SargentStachurski.NonlinearValuation`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (the quantile operator at `τ = 0`; Proposition
7.3.4 needs `L ≥ 0`; Exercise 7.1.9 needs irreducibility), the hypotheses the book
leaves implicit, and what is not formalised: the coin-flip illustration of
§7.2.1.2 and the computational exercises.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](NonlinearValuation/Basics.lean) | 18 | Markov matrices, contractions and Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 (restated) |
| [SpectralRadius](NonlinearValuation/SpectralRadius.lean) | 29 | `ρ(A)`, Gelfand's formula, the Neumann series, Ex 2.2.28 (restated) |
| [Resolvent](NonlinearValuation/Resolvent.lean) | 11 | The resolvent series (restated) |
| [PerronFrobenius](NonlinearValuation/PerronFrobenius.lean) | 20 | Thm 2.3.1, nonnegative case; Lemmas 2.3.2–2.3.3 (restated) |
| [Irreducible](NonlinearValuation/Irreducible.lean) | 10 | Thm 2.3.1, irreducible case (restated from Chapter 6) |
| [LinearValuation](NonlinearValuation/LinearValuation.lean) | 25 | Thm 6.1.1, `ρ(βP) = β`, Lemma 6.1.4, Thm 6.1.5, Example 6.1.2, Prop 6.1.6 (restated) |
| [OrderFixedPoints](NonlinearValuation/OrderFixedPoints.lean) | 15 | Global stability on a set, conjugacy, Thm 7.1.1, Ex 7.1.1, Thm 7.1.3 (i)–(iv), Ex 7.1.6 |
| [OneDimensional](NonlinearValuation/OneDimensional.lean) | 7 | Prop 7.1.2, Ex 7.1.2–7.1.5 |
| [PowerAffine](NonlinearValuation/PowerAffine.lean) | 27 | (7.1)–(7.2), Ex 7.1.7–7.1.8, Thm 7.1.4, Ex 7.1.9 |
| [CertaintyEquivalents](NonlinearValuation/CertaintyEquivalents.lean) | 33 | §7.3.1.1–7.3.1.3, Examples 7.3.1–7.3.6, Ex 7.3.1–7.3.13, (7.16)–(7.17), Lemma 7.3.1 |
| [Koopmans](NonlinearValuation/Koopmans.lean) | 29 | §7.3.1.4–7.3.3.2, (7.18)–(7.22), Examples 7.3.7–7.3.10, Remark 7.3.1, Ex 7.3.14–7.3.15, 7.3.17–7.3.20, Lemma 7.3.2, Props 7.2.2, 7.3.3, 7.3.4 |
| [RiskSensitive](NonlinearValuation/RiskSensitive.lean) | 14 | (7.5)–(7.11), Ex 7.2.1–7.2.4, 7.2.6, Lemma 7.2.1 |
| [EpsteinZin](NonlinearValuation/EpsteinZin.lean) | 13 | (7.12)–(7.15), (7.23)–(7.24), Ex 7.2.7–7.2.9, Lemma 7.2.4, Prop 7.2.3, Ex 7.3.16, Prop 7.3.5, Ex 7.3.21–7.3.22 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
