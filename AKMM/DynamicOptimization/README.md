# AKMM Chapter 4: Dynamic Optimization, in Lean

This is the `AKMM/DynamicOptimization` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 4 and Appendix 4.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 4 introduces dynamic optimization for the consumption–saving model and the neoclassical
growth model (NGM): finite-horizon sequence problems and Kuhn–Tucker conditions, a closed-form
example, CRRA utility and the elasticity of intertemporal substitution, the infinite horizon
(bounded utility, Ponzi schemes, the lifetime budget, Proposition 4.4 on the Euler equation and
the transversality condition), balanced growth, dynamic programming (the Bellman equation,
recursive formulations, the properties of the value function, guess-and-verify, the functional
Euler equation) and the global and local dynamics of the NGM; Appendix 4.A proves the equivalence
of three borrowing constraints (Theorem .3), that balanced growth forces CRRA utility
(Theorem .4) and Proposition 4.4, and analyses the phase diagram: the shapes of the loci in
Figures .1–.3, the saddle path (convergence iff on it) and the paths above and below it. Every
numbered result and derivation of the text is proved. Not formalised: narrative and empirical EIS
estimates. The existence of the saddle path, which the book asserts, is proved for every `δ ≤ 1`
by a shooting argument in the difference system.
The project depends on SLP's `DeterministicDP` (the Principle of Optimality, Theorems 4.2–4.10,
the tangent-plane inequality) and `DeterministicDynamics` (concavity tools, the monotone policy
and Proposition 6.1 of the growth model), and on `EulerTransversality` (supergradient sufficiency
of the Euler and transversality conditions); the book's statements are proved from them in the
book's notation. Thirteen printed errors are corrected, with Lean counterexamples to Proposition 4.4
without nonnegative states, to "the policy function is strictly increasing", to the printed
Weierstrass conditions and to the literal statement of Theorem .4, as recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **180 theorems**, all new.

* **Sequence problems** (§4.1): the Weierstrass argument (`seq_weierstrass`) and a counterexample
  to the printed conditions (`seq_weierstrass_counterexample`); (P2), (4.1)–(4.3)
  (`cs_gamma_iff`, `eq_4_2`, `ngm_gamma_iff`, `ngm_resource_binds`).
* **The two-period model** (§4.2.1): the lifetime budget, (4.4)–(4.6) as sufficient conditions,
  interiority and the closed form (`eq_4_4_to_4_6`, `twoPeriod_interior`,
  `twoPeriod_closed_form`, `twoPeriod_closed_form_optimal`).
* **Finite horizon** (§4.2.2–4.2.3): Result 1 (`result_1`); joint concavity of the NGM return
  (`ngm_return_concave`); (4.8)–(4.10), interiority under Inada and uniqueness
  (`ngm_terminal_zero`, `eq_4_10`, `ngm_finite_interior`, `ngm_finite_sufficient`,
  `ngm_finite_unique`).
* **Example 4.1, CRRA, EIS** (§4.2.4): (4.11) and optimality of the closed form (`eq_4_11`,
  `example_4_1`); the `σ → 1` and `σ → ∞` limits, corrected, and the Leontief limit
  (`crra_tendsto_log`, `crra_tendsto_atBot_of_lt_one`, `crra_leontief_limit`); Example 4.2
  (`example42_ratio`, `example42_eis`, `example42_income_effect`).
* **Infinite horizon** (§4.3.1): bounded utility (`infinite_growth_summable_iff`); the Ponzi
  scheme (`ponzi_improvement`, `ponzi_no_maximum`); (4.13)–(4.15) (`eq_4_13`, `eq_4_14`);
  Example 4.3 (`example_4_3`); **Proposition 4.4** (`proposition_4_4`, with
  `proposition_4_4_counterexample` and `proposition_4_4_ngm`); the TVC on stationary and balanced
  paths (`tvc_stationary`, `tvc_balanced_growth`).
* **The infinite-horizon NGM** (§4.3.2): (4.16) (`eq_4_16`); Examples 4.5–4.6
  (`example_4_5_limit`, `example_4_5_tvc`, `example_4_5`, `example_4_6`,
  `example_4_5_convergence`).
* **Balanced growth** (§4.3.3): (4.18)–(4.20) and the detrended Euler equation (`eq_4_18`,
  `eq_4_19`, `bgp_euler_original`, `bgp_condition`, `bgp_cobbDouglas`).
* **Recursive methods** (§4.4.1–4.4.3): (4.22) (`eq_4_22`); the periodic and delayed-depreciation
  NGMs, corrected (`periodic_bellman`, `delayed_bellman`, `delayed_no_discount_not_contraction`);
  properties 1–4 of `V` (`property_1` to `property_4`) and property 5 refuted and corrected
  (`property_5_counterexample`, `property_5_corrected`, `property_5_ngm`).
* **Solving for `V`** (§4.4.4–4.4.5): Example 4.7 (`eq_4_23`, `example_4_7_V2`,
  `example_4_7_coefficients`, `example_4_7`); (4.25) and Example 4.8 (`eq_4_25`, `example_4_8`).
* **NGM dynamics** (§4.4.6): `k^u` (`ngm_max_capital`); (4.26)–(4.28), corrected
  (`eq_4_26`, `eq_4_27`, `eq_4_28`); global convergence (`ngm_policy_direction`,
  `ngm_global_convergence`, `ngm_global_convergence_full`); (4.29)–(4.30) and the slope `a₁`
  (`eq_4_29`, `slopeRoot_mem`, `slopeRoot_strictAnti`, `slopeRoot_tendsto_zero`); `Θ` under CRRA
  and Cobb–Douglas (`theta_crra`, `crra_slope_limits`, `theta_cobbDouglas`,
  `cobbDouglas_slope_mono`).
* **Appendix 4.A**: Theorem .3 (`theorem_4A_3`, `appendix_4A_too_restrictive`); Theorem .4,
  corrected (`theorem_4A_4`, `theorem_4A_4_sigma_pos`, `theorem_4A_4_affine_counterexample`); the
  phase diagram (`eq_4A_12`, `eq_4A_13`, `golden_rule`, `steady_below_golden`,
  `phase_tvc_identity`, `phase_below_saddle_violates_tvc`, `phase_saddle_tvc`).
* **Figures .1–.3 and the saddle path** (App. 4.A.4): the hump of `c = f(k) − δk` and the
  increasing `c_{t+1} = c_t` locus (`saddle_kloc_shape`, `saddle_cloc_shape`), the arrows
  (`saddle_arrows`); paths ordered by `c₀` (`saddle_order`, `saddle_not_both`); convergence iff
  on the saddle path (`saddle_path_iff`), which is the optimal policy (`saddle_path_slp`,
  `saddle_logCobbDouglas`); above it capital becomes nonpositive in finite time
  (`saddle_above_infeasible`, `saddle_regionA_absorbing`); below it `c_t → 0`, `k_t > k^G` and the
  TVC fails (`saddle_below`).
* **Existence of the saddle path by shooting** (App. 4.A.4): for every `k₀ > 0` and `δ ≤ 1`, a
  saddle path `g` with "convergence iff `c₀ = g(k₀)`" (`saddle_path_general`, via
  `saddle_fwd_exists` and `saddle_trapped_converges`), equal to `(1 − αβ)Ak^α` for log utility and
  Cobb–Douglas (`saddle_path_general_logCobbDouglas`).

All names are in the namespace `AKMM.DynamicOptimization`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SequenceProblems](AKMMDynamicOptimization/SequenceProblems.lean) | 7 | (P1), Weierstrass and a counterexample, (P2), (4.1)–(4.3) (AKMM §4.1, pp. 94–99) |
| [TwoPeriod](AKMMDynamicOptimization/TwoPeriod.lean) | 6 | The two-period model, (4.4)–(4.6) (AKMM §4.2.1, pp. 99–100) |
| [FiniteHorizon](AKMMDynamicOptimization/FiniteHorizon.lean) | 13 | Result 1, concavity of the NGM return, (4.7)–(4.10), uniqueness (AKMM §4.2.2–4.2.3, pp. 100–102) |
| [FiniteInterior](AKMMDynamicOptimization/FiniteInterior.lean) | 2 | Interior capital under the Inada conditions (AKMM p. 102) |
| [FiniteExample](AKMMDynamicOptimization/FiniteExample.lean) | 13 | Example 4.1, (4.11) (AKMM §4.2.4, pp. 103–104) |
| [CRRA](AKMMDynamicOptimization/CRRA.lean) | 11 | The CRRA box, the EIS, Example 4.2 (AKMM pp. 104–105, fn. 31) |
| [InfiniteHorizon](AKMMDynamicOptimization/InfiniteHorizon.lean) | 14 | Bounded utility, Ponzi schemes, (4.12)–(4.15), Example 4.3 (AKMM §4.3.1, pp. 106–109) |
| [Proposition44](AKMMDynamicOptimization/Proposition44.lean) | 7 | Proposition 4.4, its counterexample, the TVC in the NGM (AKMM pp. 110–111, App. 4.A.3) |
| [InfiniteNGM](AKMMDynamicOptimization/InfiniteNGM.lean) | 8 | (4.16), Examples 4.5–4.6 (AKMM §4.3.2, pp. 111–113) |
| [BalancedGrowth](AKMMDynamicOptimization/BalancedGrowth.lean) | 8 | (4.18)–(4.20), the detrended Euler equation (AKMM §4.3.3, pp. 113–114) |
| [Recursive](AKMMDynamicOptimization/Recursive.lean) | 13 | (4.21)–(4.22), recursive formulations, properties 1–5 of `V` (AKMM §4.4.1–4.4.3, pp. 114–120) |
| [ValueFunctionExamples](AKMMDynamicOptimization/ValueFunctionExamples.lean) | 8 | Example 4.7, (4.23)–(4.25), Example 4.8 (AKMM §4.4.4–4.4.5, pp. 120–123) |
| [NGMDynamics](AKMMDynamicOptimization/NGMDynamics.lean) | 7 | `k^u`, (4.26)–(4.28), global convergence (AKMM §4.4.6, pp. 123–124) |
| [PolicySlope](AKMMDynamicOptimization/PolicySlope.lean) | 19 | (4.29)–(4.30), `Θ` and calibration (AKMM pp. 125–127) |
| [BorrowingConstraints](AKMMDynamicOptimization/BorrowingConstraints.lean) | 4 | (4.A.1)–(4.A.7), Theorem .3 (AKMM App. 4.A.1, pp. 827–829) |
| [BalancedGrowthCRRA](AKMMDynamicOptimization/BalancedGrowthCRRA.lean) | 6 | Theorem .4 (AKMM App. 4.A.2, pp. 829–830) |
| [PhaseDiagram](AKMMDynamicOptimization/PhaseDiagram.lean) | 10 | (4.A.8)–(4.A.13), golden rule, the TVC off and on the saddle path (AKMM App. 4.A.4, pp. 831–835) |
| [SaddlePath](AKMMDynamicOptimization/SaddlePath.lean) | 11 | Figures .1–.3: the loci and arrows; convergence iff on the saddle path; paths above and below it (AKMM App. 4.A.4, pp. 831–835) |
| [SaddlePathExistence](AKMMDynamicOptimization/SaddlePathExistence.lean) | 2 | The saddle path is the optimal policy: `δ = 1` (SLP §6.1), log and Cobb–Douglas (AKMM pp. 112, 834) |
| [SaddlePathShooting](AKMMDynamicOptimization/SaddlePathShooting.lean) | 11 | Existence of the saddle path for every `δ ≤ 1` by shooting; trapped paths converge (AKMM App. 4.A.4, p. 834) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
