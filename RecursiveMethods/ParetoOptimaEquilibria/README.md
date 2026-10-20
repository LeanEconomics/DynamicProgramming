# SLP Chapter 15: Pareto Optima and Competitive Equilibria, in Lean

This is the `RecursiveMethods/ParetoOptimaEquilibria` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 15 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 15 proves the two welfare theorems on an arbitrary normed commodity space and then asks
when the supporting price is an inner product. It develops dual spaces and the geometric
Hahn–Banach theorem, proves the First and Second Welfare Theorems (Theorems 15.3 and 15.4), shows
that on `ℓ∞` a supporting price can put all its weight at infinity, and gives conditions under
which the regular part of a price, `ψ(x) = lim_T φ(xᵀ)` on sequences or `ψ(x) = ∫ p x dμ` on
`L∞`, is again a supporting price (Theorems 15.6, 15.8 and 15.9).

Every numbered result, assumption and exercise is formalised. That includes the results the book
states without proof: Theorem 15.2 (Hahn–Banach), the duals `ℓ_p* = ℓ_q` and `L_p* = L_q` of
Examples 2 and 4, and Lemma 15.7, which is proved directly instead of from the Yosida–Hewitt
decomposition. One of these is covered only in part: `L_p* = L_q` for `1 < p < ∞` is proved for
finite measures, not for σ-finite measures of infinite mass. The case `p = 1` is proved for every
σ-finite measure, and it is false without σ-finiteness. Several claims are false as stated: Theorem
15.2 (it needs `A ≠ ∅`), `L₁* = L∞` for an arbitrary measure, the p. 458 claim that competitive
equilibria and Pareto optima coincide under Assumptions 15.1–15.5, and four exercise parts
(15.10b, 15.10c, 15.11b and 15.12). Each has a Lean counterexample and a corrected statement that
is proved. The one-person economy of Figures 15.1–15.2 is a heuristic and is not formalised,
except for the p. 444 remark on concavity. The bibliographic notes (§15.5) are not formalised. See
[corrections](docs/corrections.md). The library contains **347 theorems**.

* **Dual spaces** (§15.1). Theorem 15.1, with the book's sequential continuity; the dual norm
  (1); Exercise 15.1 (`S*` is complete). The duals of `ℝⁿ` (Example 1), `ℓ_p` for `1 < p < ∞`
  (Example 2), `ℓ₂` and `ℓ₁` (Exercise 15.2), `c₀` (Exercise 15.4), and `ℓ₁ ⊆ ℓ∞*` (Exercise
  15.3), each as an isometric isomorphism `y ↦ (x ↦ Σ yᵢ xᵢ)`.
* **`L_p` duals** (§15.1, Example 4). `L₁* = L∞` for σ-finite `μ`, by Riesz representation in
  `L₂`; `L_p* = L_q` for `1 < p < ∞` and finite `μ`, by Radon–Nikodym and Fatou. Exercise 15.5,
  and the example `L∞(ℕ, μ) = ℓ∞` on p. 450.
* **Hahn–Banach** (§15.1). Theorem 15.2 with the nonemptiness hypotheses it needs, and
  counterexamples to the printed statement. Exercise 15.6: in the space with norm `Σ βᵗ |xₜ|` the
  box `{|xₜ| ≤ 1}` has empty interior, and separation fails for `A = {θ}`.
* **The welfare theorems** (§15.2). Economies, Pareto optima and competitive equilibria;
  Theorem 15.3 under local nonsatiation; Assumptions 15.1–15.5; Theorem 15.4, with the
  separation proved directly in both cases of Assumption 15.5; the Remark (a cheaper point for
  every consumer gives an equilibrium). Two steps of the book's proof of Theorem 15.4 give a
  wrong reason, and each has a Lean counterexample.
* **Figure 15.3 and p. 458** (§§15.2–15.3). A concrete exchange economy with the features of
  Figure 15.3: a Pareto optimum supported by a nonzero price that is not a competitive equilibrium
  at any price. With a second example, it shows that neither inclusion of the p. 458 claim holds;
  the corrected combination of Theorems 15.3, 15.4 and the Remark is proved.
* **The choice of commodity space** (§15.3). Exercise 15.7 (orthants of `ℓ_p` and `ℓ∞`); the
  economy `u(x) = inf_t x_t` on `ℓ∞` (Exercise 15.8), whose supporting price vanishes on every
  finitely supported sequence and has no inner product form (4); Exercise 15.9 and the weighted
  norm (5).
* **Prices on sequence spaces** (§15.4). Lemma 15.5: the regular part `ψ` of `φ`, with
  `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖` and the inner product forms (3). Assumptions 15.6–15.7;
  Exercises 15.10 and 15.11; a functional on `ℓ∞` with all its weight at infinity. Theorem 15.6,
  its combination with Theorem 15.4, and an economy in which the regular part `ψ` is zero.
* **Prices on `L∞`** (§15.4). Lemma 15.7; Assumptions 15.8–15.9; Exercise 15.12 (expected
  utility); Theorem 15.8.
* **Time and uncertainty combined** (§15.4). The space `X₀ × X₁ × …`, `X_t = L∞(μ^t)`, with norm
  (8); Assumptions 15.8′–15.9′; Theorem 15.9, with prices `ν(x) = Σ_t ∫ p_t x_t dμ^t`.

All names are in the namespace `StokeyLucasPrescott.ParetoOptimaEquilibria`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DualSpaces](ParetoOptimaEquilibria/DualSpaces.lean) | 84 | Theorems 15.1–15.2, Examples 1–3, Exercises 15.1–15.6, `L₁* = L∞`, p. 444 |
| [DualLp](ParetoOptimaEquilibria/DualLp.lean) | 22 | Example 4: `L_p* = L_q`, `1 < p < ∞` |
| [Economy](ParetoOptimaEquilibria/Economy.lean) | 0 | Feasibility, Pareto optima, competitive equilibria, Assumptions 15.1–15.5 |
| [Welfare](ParetoOptimaEquilibria/Welfare.lean) | 10 | Theorem 15.3; convexity lemmas for Theorem 15.4 |
| [WelfareSecond](ParetoOptimaEquilibria/WelfareSecond.lean) | 12 | Theorem 15.4, the Remark, the corrected p. 458 claim |
| [WelfareExamples](ParetoOptimaEquilibria/WelfareExamples.lean) | 7 | Figure 15.3; counterexamples to p. 458 |
| [CommodityChoice](ParetoOptimaEquilibria/CommodityChoice.lean) | 25 | §15.3, Exercises 15.7–15.9 |
| [SequencePrices](ParetoOptimaEquilibria/SequencePrices.lean) | 28 | Truncations, Lemma 15.5, (3) |
| [SequenceInfinity](ParetoOptimaEquilibria/SequenceInfinity.lean) | 17 | Discounted sums, the tail distance, a functional at infinity |
| [SequenceAssumptions](ParetoOptimaEquilibria/SequenceAssumptions.lean) | 29 | Assumptions 15.6–15.7, Exercise 15.10 |
| [SequenceTailUtility](ParetoOptimaEquilibria/SequenceTailUtility.lean) | 14 | Exercise 15.11 |
| [SequenceSupport](ParetoOptimaEquilibria/SequenceSupport.lean) | 11 | Theorem 15.6 |
| [LinftyPrices](ParetoOptimaEquilibria/LinftyPrices.lean) | 48 | Truncation over events, Lemma 15.7 |
| [LinftyAssumptions](ParetoOptimaEquilibria/LinftyAssumptions.lean) | 19 | Assumptions 15.8–15.9, Exercise 15.12, Theorem 15.8 |
| [LinftyTimeState](ParetoOptimaEquilibria/LinftyTimeState.lean) | 21 | (8), Assumptions 15.8′–15.9′, Theorem 15.9 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
