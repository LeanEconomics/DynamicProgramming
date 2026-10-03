# Optimal stopping in Lean

This is the `FiniteStates/OptimalStopping/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/OptimalStopping` from
the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 4, "Optimal Stopping" (pp. 105–127),
including every provable exercise (Exercises 4.1.1–4.1.5, 4.1.7–4.1.13,
4.2.1–4.2.3). The library contains **143 theorems** and audits every
declaration, including structure constructors and projections.

* **The theory of §4.1.1.** A stopping problem is `S = (β, P, c, e)`. Each policy
  `σ` has a policy operator `T_σ v = r_σ + L_σ v`, order preserving
  (Exercise 4.1.2) and a `β`-contraction (Proposition 4.1.1), whose unique fixed
  point is the lifetime value `v_σ`, (4.2)–(4.4); `ρ(L_σ) < 1` (Exercise 4.1.1).
  The value function `v* = ⋁_σ v_σ` is the unique fixed point of the Bellman
  operator `Tv = e ∨ (c + βPv)` (Proposition 4.1.2), proved as in the book:
  `v̄ ≤ v*` because `v̄` is the value of its own greedy policy, and `v* ≤ v̄`
  by Proposition 2.2.7. A policy is optimal iff it is `v*`-greedy
  (Proposition 4.1.3, which the book defers to Chapter 5; the proof here is
  direct). Value function iteration converges at rate `βᵏ`.
* **Continuation values** (§4.1.4): `h* = c + βPv*` is the unique fixed point of
  the `β`-contraction `Ch = c + βP(e ∨ h)` (Proposition 4.1.5), and
  `σ* = 1{e ≥ h*}` is optimal. When the state is `(w, z)` with `w` IID and the
  continuation reward depending on `z` only, `h*` depends on `z` only and is the
  fixed point of the reduced operator (4.15) on `ℝ^Z`; IID job search is the case
  `Z` a point (Example 4.1.6). Exercise 4.1.13 (a stochastically larger scrap
  value makes the firm exit less) is proved for scrap values on a finite set.
* **Monotonicity** (§4.1.3): `v*` and `h*` are increasing when `e`, `c` are
  increasing and `P` is monotone increasing (Lemma 4.1.4); `σ*` is decreasing
  when `e` is decreasing and `h*` increasing, increasing when the reverse holds
  (Exercises 4.1.9–4.1.11), and a monotone binary policy on a totally ordered
  state space is a threshold policy.
* **Firm valuation with exit** (§4.1.2): the no-exit value `w = (I − βQ)⁻¹π` is
  the value of never exiting, so `w ≤ v*`; if `Q ≫ 0` and `s > w(z)` somewhere
  then `w ≪ v*` (Exercise 4.1.7); Examples 4.1.3–4.1.4 and the price-state
  Bellman equation of Exercise 4.1.8, with `max_ℓ (p√ℓ − wℓ) = p²/(4w)`.
* **American options** (§4.2.1): a finite-horizon call is embedded in
  infinite-horizon stopping with the date in the state; the continuation value
  operator (4.16) acts on `ℝ^{T × Z}`; and the claim of p. 122 that the exercise
  region expands with `t` is proved, since `v*` is nonnegative and nonincreasing
  in the date.
* **Research and development** (§4.2.2): constant costs (Bellman equation (4.17),
  Exercises 4.2.1–4.2.2) and IID costs, where the expected value function `g`
  solves (4.20) and the operator `R` is a `β`-contraction (Exercise 4.2.3).

The main entry points are `StoppingProblem.isContractionOn_Tσ`,
`StoppingProblem.specRad_L_lt_one`, `StoppingProblem.isFixedPt_T_vstar`,
`StoppingProblem.bellman_equation`, `StoppingProblem.isOptimal_iff_isGreedy`,
`StoppingProblem.isContractionOn_C`, `StoppingProblem.monotone_vstar`,
`productProblem.hstar_eq_reducedH`, `scrapFirm_sigmaStar_ge`,
`firmExit.noExitValue_lt_vstar`, `AmericanOption.exercise_region_expands` and
`rdIID.isContractionOn_R`, all in the namespace `SargentStachurski.OptimalStopping`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (Exercise 4.1.13 is proved with a finite scrap
distribution; the exercise-region claim of p. 122 is proved as a theorem), the
hypotheses the book leaves implicit, and what is not formalised: the exactness of value function
iteration after finitely many steps (Theorem 8.1.1) and the computational
exercises.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](OptimalStopping/Basics.lean) | 15 | Markov matrices, `|Ph| ≤ ‖h‖`, contractions with Banach's theorem, Prop 2.2.7 on ordered operators, closed increasing functions, monotone Markov operators (restated Chapter 1–3 facts) |
| [Problem](OptimalStopping/Problem.lean) | 22 | `S = (β, P, c, e)`, policies, `r_σ`, `L_σ`, `T_σ` (4.5), Ex 4.1.2, Prop 4.1.1 (Ex 4.1.3), `v_σ` and (4.2)–(4.4) with the Neumann series, Examples 4.1.1–4.1.2 |
| [SpectralRadius](OptimalStopping/SpectralRadius.lean) | 7 | `ρ(A) ≤ ‖A‖` for the ℓ∞ operator norm; Ex 4.1.1: `ρ(L_σ) < 1` |
| [Bellman](OptimalStopping/Bellman.lean) | 18 | `T` (4.8), Ex 4.1.4, Prop 4.1.2 (Ex 4.1.5), `v*` (4.6), the Bellman equation (4.7), VFI, greedy policies (4.9), optimality (4.1), Prop 4.1.3 |
| [ContinuationValue](OptimalStopping/ContinuationValue.lean) | 13 | `h*` (4.10), (4.11)–(4.13), Prop 4.1.5, `σ* = 1{e ≥ h*}` optimal |
| [Monotonicity](OptimalStopping/Monotonicity.lean) | 10 | Lemma 4.1.4, Ex 4.1.9–4.1.11, Example 4.1.5, threshold policies (p. 116) |
| [Reduction](OptimalStopping/Reduction.lean) | 16 | Product kernels, (4.14), the reduced operator (4.15), `h*(w, z) = h̃(z)`, Example 4.1.6, Ex 4.1.12–4.1.13 |
| [FirmExit](OptimalStopping/FirmExit.lean) | 13 | §4.1.2: the firm's `T_σ`, `T`, Bellman equation, `w = (I − βQ)⁻¹π ≤ v*`, Ex 4.1.7, Examples 4.1.3–4.1.4, Ex 4.1.8 |
| [AmericanOption](OptimalStopping/AmericanOption.lean) | 18 | §4.2.1: the date-augmented state, `P`, Bellman equation, (4.16), `σ*`, the exercise region expands with `t` |
| [ResearchDevelopment](OptimalStopping/ResearchDevelopment.lean) | 11 | §4.2.2: (4.17), Ex 4.2.1–4.2.2; IID costs, (4.18)–(4.20), `R`, Ex 4.2.3, `σ*` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
