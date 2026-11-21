# AKMM Chapter 10: Computational Tools, in Lean

This is the `AKMM/ComputationalTools` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 10 of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama,
*Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands below from
this directory. [Return to the library index](../../README.md).

Chapter 10 surveys the numerical methods of computational macroeconomics: function approximation,
root finding, optimisation, the discretisation of AR(1) processes, value-function iteration and
the solution of linear rational-expectations models by Blanchard and Kahn's method. The chapter
has no numbered theorems; the theorems behind the methods are formalised: interpolation error and
uniqueness, convergence and iteration counts of bisection, local quadratic convergence of Newton's
method (not in Mathlib), the self-similarity of golden-section search, Tauchen rows as probability
vectors, the Rouwenhorst chain's binomial invariant law and its moments, value-function iteration as
a contraction with the closed-form cake-eating problem, the log-linearised growth model with labour
and the Blanchard–Kahn solution. Algorithms as code, MATLAB examples, numerical output and figures
are listed as not formalised in the [source map](docs/source-map.md). Seven printed errors are
corrected, with Lean counterexamples to the golden-section bracket length, the Rouwenhorst recursion
(its weights are swapped), Tauchen's interior probabilities (their sign), the `z_t` coefficient of
(10.17) and the matrix `E` (a missing `α`), and the non-differentiability claim for linear
interpolation, as recorded in [corrections](docs/corrections.md). The project depends on Miao's
`NumericalMethods`, `RationalExpectations` and `DifferenceEquations` and on Sargent–Stachurski's
`JobSearch`. The library contains **120 theorems**.

* **Approximating a function** (§10.1): the linear interpolant and its uniqueness
  (`linInterp_unique`), the error bound `M(x − xᵢ)(x_{i+1} − x)/2 ≤ Mh²/8` (`linInterp_error`,
  `linInterp_error_h`), kinks (`linInterp_kink_not_differentiable`), natural cubic splines
  (`cubic_spline_existsUnique`) and (10.1) (`eq_10_1_unique_iff`, `eq_10_1_poly`).
* **Bisection** (§10.2.1): bracketing (`bisect_bracket_root`), halving (`bisect_length`),
  convergence to a root of a continuous function (`bisect_converges`), the iteration count
  (`bisect_iteration_count`, `bisect_ten_steps`) and termination without a root
  (`bisect_discontinuous_no_root`).
* **Newton's methods** (§10.2.2, §10.3.2–10.3.3): (10.2) and (10.3) (`eq_10_2`, `eq_10_3`,
  `eq_10_3_max`), one-step exactness (`newton_affine_exact`, `newtonOpt_quadratic_exact`), local
  quadratic convergence (`newton_local_quadratic`, `newton_converges`), central differences
  (`central_difference_tendsto`) and Newton for `max F` = Newton–Raphson on `F′`
  (`newtonOpt_eq_newtonStep_deriv`).
* **Golden-section search** (§10.3.1): `ω* = (3 − √5)/2` and the golden ratio (`golden_ratio_eq`),
  the bracket lemma (`golden_bracket_max`), self-similarity and the length `(1 − ω*)ⁿ(c − a)`
  (`goldenStep_spec`, `golden_length`, `golden_printed_length_counterexample`), footnote 3
  (`golden_fn3_unique`).
* **Example 1** (§10.3.3): (10.5) is the derivative of (10.4) (`eq_10_5`), a unique root that is the
  maximiser (`ex1_root_isMax`, `ex1_unique_root`).
* **Discretising AR(1) processes** (§10.4): `σ_z² = σ_ε²/(1 − ρ²)` (`ar1_uncond_var`); Tauchen,
  corrected (`tauchen_stochastic`, `tauchen_printed_neg`, `tauchen_printed_row_sum`); Rouwenhorst,
  corrected: generating polynomials (`rouwenhorst_eq_coeff`), stochasticity (`rouwenhorst_row_sum`),
  the binomial invariant law (`rouwenhorst_invariant`), moment matching
  (`rouwenhorst_matches_ar1`) and the printed recursion refuted
  (`rouwenhorst_printed_counterexample`).
* **Value-function iteration** (§10.5): the grid Bellman operator is a `β`-contraction
  (`GridDP.contraction`), VFI converges (`GridDP.vfi`), the stopping rule (`GridDP.stopping_rule`),
  grid cake eating (`cakeGrid_vfi`, `stochCakeGrid`); the continuous cake: closed form
  `V(a) = √(a/(1 − β²))` (`cake_bellman`, `cake_policy_unique`, `cake_path_value`), uniqueness of
  bounded solutions (`cake_bellman_unique`), concavity (`cake_concave`).
* **Linearisation** (§10.6): the labour choice (10.12) (`labour_foc_unique`), log-linearisation of
  (10.9), (10.13), (10.14) (`loglin_resource`, `loglin_euler`, `loglin_labour`), (10.15)–(10.17)
  (`eq_10_15`, `eq_10_16`, `eq_10_17`, `eq_10_17_printed_counterexample`) and (10.27) (`eq_10_27`).
* **Blanchard–Kahn** (§10.6.1): (10.18)–(10.20) (`eq_10_19`, `eq_10_20`), forecasts and (10.23)
  (`bk_forecast`, `eq_10_23`, `eq_10_23_unique`), indeterminacy (`bk_fn8`, `bk_indeterminate`),
  guess and verify (`eq_10_25`), (10.30) (`eq_10_30`), the solution (`bk_tilde_solution`,
  `bk_y_solution`, `bk_x_solution`) and the condition `h = m` (`bk_condition`).

All names are in the namespace `AKMM.ComputationalTools`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Interpolation](AKMMComputationalTools/Interpolation.lean) | 10 | Linear and cubic-spline interpolation, (10.1) (AKMM §10.1, pp. 261–263) |
| [Bisection](AKMMComputationalTools/Bisection.lean) | 12 | Bracketing, convergence and iteration count of bisection (AKMM §10.2.1, pp. 263–265) |
| [Newton](AKMMComputationalTools/Newton.lean) | 10 | (10.2)–(10.3), local quadratic convergence, central differences (AKMM §10.2.2, §10.3.2–10.3.3, pp. 265–269) |
| [GoldenSection](AKMMComputationalTools/GoldenSection.lean) | 15 | Golden-section search, the bracket length, footnote 3 (AKMM §10.3.1, pp. 266–267, 269) |
| [LabourLeisure](AKMMComputationalTools/LabourLeisure.lean) | 5 | Example 1, (10.4)–(10.5) (AKMM pp. 269–270) |
| [Discretization](AKMMComputationalTools/Discretization.lean) | 7 | The AR(1) variance and the Tauchen method (AKMM §10.4–10.4.1, pp. 270–271) |
| [Rouwenhorst](AKMMComputationalTools/Rouwenhorst.lean) | 20 | The Rouwenhorst matrix, its invariant law and moments (AKMM §10.4.2, p. 271) |
| [ValueIteration](AKMMComputationalTools/ValueIteration.lean) | 6 | (10.6)–(10.7) on a grid, contraction and VFI, cake grids (AKMM §10.5, pp. 272–275) |
| [CakeEating](AKMMComputationalTools/CakeEating.lean) | 7 | The cake-eating problem in closed form (AKMM §10.5.1, pp. 273–274) |
| [Linearization](AKMMComputationalTools/Linearization.lean) | 11 | (10.12)–(10.17), (10.27): the log-linearised growth model (AKMM §10.6, pp. 275–281) |
| [BlanchardKahn](AKMMComputationalTools/BlanchardKahn.lean) | 17 | (10.18)–(10.31), the Blanchard–Kahn condition (AKMM §10.6.1, pp. 278–283) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
