# Miao Chapter 11: Numerical Methods, in Lean

This is the `EconomicDynamics/NumericalMethods` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 11 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 11 surveys numerical methods for dynamic models: quadrature, discretising AR(1)
processes, interpolation with orthogonal polynomials and splines, perturbation, projection
methods and numerical dynamic programming. Only the theorems are formalised: every mathematical
claim the text makes or derives (Definition 11.3.1, Theorem 11.3.1, the exactness of Gaussian
rules, the properties of the discretised chains, the derivations of the perturbation and
projection examples, the convergence of value, policy and fitted value iteration), and the
mathematical content of Exercises 1–3. Algorithmic descriptions, toolbox calls and numerical
output are recorded as not formalised in the [source map](docs/source-map.md); the
corrections are in [corrections](docs/corrections.md). This draft of §11.2 has no Rouwenhorst
method. The library contains **430 theorems**; 72 of them are Sargent–Stachurski's finite Markov
decision processes, copied.

* **Quadrature** (§11.1): an `n`-point Gaussian rule is exact for degree `2n − 1` and no rule is
  exact for degree `2n` (`nq_gauss_exact`, `nq_gauss_not_exact_two_mul`); Gauss–Legendre,
  Gauss–Chebyshev for every `n`, Gauss–Hermite and normal expectations, product rules
  (`nq_chebyshev_isGaussRule`, `nq_normal_expectation_gauss_hermite`, `nq_prod_gauss_exact`).
* **Discretising AR(1) processes** (§11.2): Tauchen's and Tauchen–Hussey's matrices are
  stochastic, with the printed intervals and weights corrected (`nq_tauchen_stochastic`,
  `nq_tauchen_printed_I2_upper`, `nq_th_normalized_stochastic`, `nq_th_rowsum_lt_one`).
* **Interpolation** (§11.3): orthogonal polynomials and Definition 11.3.1, whose norm lacks a
  square root (`definition_11_3_1`, `ni_inner_self_not_homogeneous`); Chebyshev polynomials,
  nodes and discrete orthogonality (`ni_cheb_discrete_orthogonality`); **Theorem 11.3.1** for
  `n ≥ k` by the Lebesgue inequality and Jackson's theorem, false as printed for all `n`
  (`theorem_11_3_1`, `theorem_11_3_1_counterexample`); non-convergence at uniform nodes
  (`ni_uniform_interp_not_convergent`); cubic splines under natural, clamped and not-a-knot end
  conditions (`ni_natural_spline_existsUnique`, `ni_notAKnot_not_unique_two`), B-splines and
  tensor products (`ni_bspline_recursion`, `ni_tensor_coeff`).
* **Perturbation** (§11.4): (11.4)–(11.7) for the recursive-utility example (`eq_11_6`,
  `eq_11_7`) and Exercise 2 in closed form (`ex_11_2`).
* **Projection methods** (§11.5): collocation needs a discrete inner product
  (`np_collocation_integral_degenerate`), least squares, Galerkin and the method of moments, and
  Chebyshev regression = orthogonal collocation (`np_cheb_regression_iff_collocation`,
  `np_cheb_galerkin_iff_collocation`); the growth-model Euler equation (`eq_11_8`).
* **Numerical dynamic programming** (§11.6): the discretised growth model as a finite MDP
  (`GrowthGrid.eq_11_10`), contraction and geometric convergence of value iteration
  (`np_bellman_contraction`, `np_vfi_geometric`), policy iteration and its termination
  (`eq_11_12`, `np_pfi_terminates`), fitted value iteration with averaging interpolants
  (`np_fitted_converges`), and the PEA conditions (`np_pea_kkt_unique`); Exercise 3's
  first-order conditions and steady state (`ex_11_3_euler`, `ex_11_3_steady_state`).

All names are in the namespace `Miao.NumericalMethods` (the §11.5–11.6 names in
`Miao.NumericalMethods.NP`). `NPBasics`, `NPMDP` and `NPBellman` are copied from
[FiniteStates/MarkovDecisionProcesses](../../FiniteStates/MarkovDecisionProcesses/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [NQQuadrature](NumericalMethods/NQQuadrature.lean) | 14 | Gaussian quadrature (Miao, §11.1, pp. 347–350) |
| [NQChebyshev](NumericalMethods/NQChebyshev.lean) | 8 | Gauss–Chebyshev quadrature (Miao, §11.1.1, p. 349) |
| [NQHermite](NumericalMethods/NQHermite.lean) | 8 | Gauss–Hermite quadrature and normal expectations (Miao, §11.1.1, p. 349) |
| [NQAR1](NumericalMethods/NQAR1.lean) | 27 | Discretizing AR(1) processes (Miao, §11.2, pp. 350–354) |
| [NQPerturbation](NumericalMethods/NQPerturbation.lean) | 8 | Perturbation methods: recursive utility with unit EIS (Miao, §11.4, pp. 366–369) |
| [NQPerturbationExercise](NumericalMethods/NQPerturbationExercise.lean) | 12 | The Hansen–Heaton–Li example in closed form (Miao, §11.4, pp. 367–369; Exercise 11.2) |
| [NIWeighted](NumericalMethods/NIWeighted.lean) | 9 | Weighting functions and weighted inner products (Definition 11.3.1) |
| [NIInterpolation](NumericalMethods/NIInterpolation.lean) | 9 | The interpolation problem (Miao, §11.3, pp. 354–356) |
| [NILegendre](NumericalMethods/NILegendre.lean) | 11 | Legendre polynomials (Miao, §11.3.1, p. 357) |
| [NILaguerre](NumericalMethods/NILaguerre.lean) | 15 | Laguerre polynomials (Miao, §11.3.1, p. 357) |
| [NIHermite](NumericalMethods/NIHermite.lean) | 15 | Hermite polynomials (Miao, §11.3.1, p. 357) |
| [NIChebyshev](NumericalMethods/NIChebyshev.lean) | 20 | Chebyshev polynomials (Miao, §11.3.1, pp. 357–358) |
| [NIChebInterp](NumericalMethods/NIChebInterp.lean) | 12 | Chebyshev interpolation (Miao, §11.3.1, pp. 359–360) |
| [NILebesgue](NumericalMethods/NILebesgue.lean) | 9 | The Lebesgue constant of the Chebyshev nodes (for Theorem 11.3.1) |
| [NIJackson](NumericalMethods/NIJackson.lean) | 17 | Jackson's theorem for Lipschitz functions (for Theorem 11.3.1) |
| [NIJacksonApprox](NumericalMethods/NIJacksonApprox.lean) | 3 | Jackson's theorem (for Theorem 11.3.1) |
| [NIChebThm](NumericalMethods/NIChebThm.lean) | 7 | Theorem 11.3.1, the Chebyshev Interpolation Theorem (Miao, p. 359) |
| [NISplines](NumericalMethods/NISplines.lean) | 6 | Splines and linear splines (Miao, §11.3.2, pp. 360–361) |
| [NICubicSpline](NumericalMethods/NICubicSpline.lean) | 19 | Cubic splines (Miao, §11.3.2, p. 361) |
| [NIBSplines](NumericalMethods/NIBSplines.lean) | 15 | pp-form and B-splines (Miao, §11.3.2, pp. 361–362) |
| [NITensor](NumericalMethods/NITensor.lean) | 12 | Multidimensional approximation: tensor products (Miao, §11.3.3, pp. 364–366) |
| [NIExercise1](NumericalMethods/NIExercise1.lean) | 6 | Exercise 11.1 (Miao, p. 383) |
| [NIRunge](NumericalMethods/NIRunge.lean) | 10 | Interpolation at uniformly spaced nodes need not converge (Miao, p. 360) |
| [NPBasics](NumericalMethods/NPBasics.lean) | 18 | Markov matrices, contractions and Blackwell's condition: the shared vocabulary (copied) |
| [NPMDP](NumericalMethods/NPMDP.lean) | 22 | Markov decision processes, policies and lifetime values (copied) |
| [NPBellman](NumericalMethods/NPBellman.lean) | 32 | Optimality: the Bellman operator, greedy policies and the algorithms (copied) |
| [NPDiscreteDP](NumericalMethods/NPDiscreteDP.lean) | 33 | Discrete approximation methods for dynamic programming |
| [NPFitted](NumericalMethods/NPFitted.lean) | 8 | Smooth approximation: value function interpolation |
| [NPProjection](NumericalMethods/NPProjection.lean) | 15 | Projection methods: residuals and weighted-residual conditions |
| [NPChebyshev](NumericalMethods/NPChebyshev.lean) | 9 | Orthogonal collocation with Chebyshev polynomials |
| [NPGrowthProjection](NumericalMethods/NPGrowthProjection.lean) | 7 | The projection method for the stochastic growth model |
| [NPEuler](NumericalMethods/NPEuler.lean) | 9 | Euler equations from the Bellman equation: the growth model and Exercise 11.3 |
| [NPPEA](NumericalMethods/NPPEA.lean) | 5 | The parameterized expectations approach: irreversible investment |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
