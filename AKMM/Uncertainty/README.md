# AKMM Chapter 7: Uncertainty, in Lean

This is the `AKMM/Uncertainty` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 7 and Appendix 7.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 7 introduces the tools for stochastic economies — expectations on event trees, Markov
chains, AR(1) and vector linear stochastic difference equations, expected utility, risk aversion and
portfolio choice — and applies them to the stochastic growth model (planner, recursive formulation,
linearisation), to trade under complete markets (Arrow–Debreu and sequential equilibrium, insurance,
risk sharing, spanning), to the competitive equilibrium of the growth model and to an
incomplete-markets saving problem, whose decision rules, ergodic set and stationary distribution
(Figure 7.4) are proved for Markov income; Appendix 7.A defines the recursive competitive
equilibrium and proves the law of iterated expectations on a finite tree. Every numbered equation
and derivation of the text is proved and every numbered definition is formalised; the first-order
conditions (7.13), (7.20) and (7.28) and the two-period Euler equation are proved from optimality by
finite perturbations, the transversality condition is shown sufficient, and the log closed form is
proved optimal. Not formalised: narrative, the ergodicity and law-of-large-numbers remarks, the
numerical illustrations, and the claims read off Figure 7.3 (deferred). The project depends on
Miao's `CompleteMarkets` (the event tree), `MarkovProcesses` (stationary distributions and
convergence) and `RationalExpectations` (VAR moments and the Lyapunov equation), on Obstfeld and
Rogoff's `InternationalFinancialMarkets` (spanning), and on AKMM Chapters 4 (CRRA, the EIS, the
policy slope `a₁`) and 5 (finite perturbations, the log tangent). Ten printed errors are corrected,
with Lean counterexamples to footnote 3's solution, the "necessary condition" for convergence, the
definition of aperiodicity, the EIS derivative and the Euler equation of p. 201, as recorded in
[corrections](docs/corrections.md); every book item is located in the [source
map](docs/source-map.md). The claims of Figure 7.4 are proved with added hypotheses, and the
high-income rule of the figure is shown to depend on the parameters (corrections 19–21). The library
contains **170 theorems**.

* **Event trees and iterated expectations** (§7.1.1, §7.2.1, 7.A.2): conditional probabilities
  (`tree_condProb_sum`); the law of iterated expectations on the tree and for filtrations
  (`tree_lie`, `lie_filtration`); Appendix 7.A.2, corrected (`appendix_7A_2`, `appendix_7A_2_sum`,
  `appendix_7A_2_root`); the Markov property (`tree_markov`); expected utility
  (`tree_expectedUtility_term`).
* **Markov chains** (§7.1.2): `π_{t+k} = π_tPᵏ` (`markov_marginal_column`, `markov_marginal_pow`);
  unit eigenvectors (`markov_stationary_iff_eigen`, `markov_unit_eigenvalue`); the employment chain
  (`employment_unique`, `employment_closed_form`, `employment_fn3`,
  `employment_fn3_printed_counterexample`, `employment_converges`); the identity and flip matrices
  (`identity_not_unique`, `flip_stationary_iff`, `flip_not_converge`); convergence conditions,
  corrected (`positive_matrix_converges`, `positive_matrix_not_necessary`,
  `offdiag_positive_not_sufficient`); irreducibility and aperiodicity, corrected
  (`ak_irreducible_iff`, `markov_irreducible_unique`, `markov_irreducible_aperiodic_converges`,
  `aperiodic_printed_counterexample`).
* **AR(1) and linear systems** (§7.1.3–7.1.4): the moving average (`ar1_ma`); the moments and
  correlation (`ar1_moments`, `ar1_correlation`); `µ = (I − A)⁻¹C` (`sde_mean_fixed`); (7.6)
  (`eq_7_6`); impulse responses (`sde_no_further_shocks`, `sde_impulse_response`).
* **Risk aversion and portfolios** (§7.2.2–7.2.3): Jensen (`risk_averse_jensen`,
  `risk_averse_strict`, `risk_neutral`); ARA and RRA (`ara_affine`, `rra_affine`, `ara_cara`,
  `rra_crra`, `rra_log`); the EIS, corrected (`eis_crra`, `eis_printed_counterexample`); the
  portfolio first-order condition (`portfolio_foc`) and homogeneity (`portfolio_crra_share`,
  `portfolio_cara_invariant`, `portfolio_cara_share_falls`).
* **The stochastic growth planner** (§7.3.1–7.3.2): the two-period Euler equation
  (`two_period_lagrangian`, `two_period_euler`); (7.12)–(7.14) (`eq_7_12_7_13`, `eq_7_13`,
  `eq_7_14`); sufficiency with the transversality condition (`pt_euler_tvc_optimal`); the log
  closed form (`pt_log_euler`, `pt_log_tvc`, `pt_log_optimal`).
* **The recursive formulation** (§7.3.3): (7.15), the envelope condition and (7.16) (`rb_foc`,
  `rb_envelope`, `rb_euler`, `eq_7_15`, `rec_envelope`, `eq_7_16`); the printed Euler equation
  refuted (`rec_euler_printed_counterexample`).
* **Linearisation** (§7.3.4): certainty equivalence (`lin_certainty_equivalence`); matching
  coefficients (`lin_match`, `lin_K_eq_of_policy`); (7.17) and its roots, agreeing with Chapter 4's
  `a₁` (`eq_7_17`, `eq_7_17_values`, `eq_7_17_roots`); `g_A` (`lin_gA`); (7.18)–(7.19)
  (`eq_7_18_7_19`, `lin_system_stable`).
* **Complete markets** (§7.4): Definition 13 (`definition_13`); (7.20) (`eq_7_20_pair`,
  `eq_7_20`); insurance (`cm_insurance`, `cm_insurance_no_aggregate_risk`, `cm_fair_value`); risk
  sharing and (7.21) (`cm_risk_sharing`, `eq_7_21`, `cm_aggregate_risk_only`); sequential trading
  and Definition 14 (`seq_consolidated`, `seq_ad_budget_le`, `seq_ad_budget_eq`, `seq_price_map`,
  `seq_price_of_ad`, `definition_14`, `definition_14_goods_of_assets`); spanning
  (`spanning_iff_rank`, `spanning_arrow`).
* **Competitive equilibrium of the growth model** (§7.5): Definition 15 (`definition_15`); (7.28)
  (`eq_7_28_lagrangian`, `eq_7_28`); condition 3 is redundant
  (`definition_15_resource_redundant`); the equilibrium is the planner's (`ce_euler_is_planner`,
  `ce_planner_optimal`).
* **Incomplete markets** (§7.6): the first-order condition, envelope condition and Euler
  inequality, corrected (`im_foc`, `im_envelope`, `im_envelope_boundary`, `im_euler`).
* **Figure 7.4 for Markov income** (§7.6, pp. 214–215): under the standing assumptions
  (`imf_Standing`), savings and consumption are nondecreasing and continuous in assets
  (`imf_g_mono`, `imf_c_mono`, `imf_g_lipschitz`, `imf_c_lipschitz`); the lowest-consumption state
  dissaves and the constraint binds near `a̲` (`imf_min_dissave`, `imf_binds_near_limit`); the
  bound `ā` (`imf_abar_exists`, `imf_abar_exists_neg`, `imf_crra_spread`); the ergodic set is
  invariant and reached along every income history (`imf_ergodic_invariant`,
  `imf_enters_ergodic`); an accessible atom gives Condition M, a unique stationary distribution of
  `(a, y)` and convergence in total variation (`imf_kernel_hit`, `imf_kernel_stationary`,
  `imf_stationary`); a solved two-state Markov instance (`imf_example_stationary`), in which the
  high-income consumer does not accumulate (`imf_example_no_accumulation`).
* **Recursive competitive equilibrium** (7.A.1): Definition 16, corrected (`definition_16`), an
  equilibrium (`definition_16_example`) and its functional Euler equation, which is (7.16)
  (`definition_16_euler`).

All names are in the namespace `AKMM.Uncertainty`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [EventTrees](AKMMUncertainty/EventTrees.lean) | 8 | Event trees, the law of iterated expectations, Appendix 7.A.2, expected utility (AKMM §7.1.1, §7.2.1–7.2.2, pp. 188, 193–194, 840–841) |
| [MarkovChains](AKMMUncertainty/MarkovChains.lean) | 30 | Marginals, stationary distributions, the employment chain, convergence conditions (AKMM §7.1.2, pp. 189–190) |
| [AR1](AKMMUncertainty/AR1.lean) | 5 | (7.1), the moving average, moments and autocorrelations (AKMM §7.1.3, pp. 191–192) |
| [LinearSDE](AKMMUncertainty/LinearSDE.lean) | 6 | (7.2)–(7.6), the mean, the Lyapunov equation, impulse responses (AKMM §7.1.4, pp. 191–192) |
| [RiskAversion](AKMMUncertainty/RiskAversion.lean) | 11 | Jensen, ARA and RRA, CARA and CRRA, the EIS (AKMM §7.2.2, pp. 194–195) |
| [Portfolio](AKMMUncertainty/Portfolio.lean) | 9 | The portfolio problem, CRRA and CARA homogeneity (AKMM §7.2.3, pp. 195–196) |
| [TwoPeriod](AKMMUncertainty/TwoPeriod.lean) | 2 | (7.7)–(7.9), the stochastic Euler equation (AKMM §7.3.1, pp. 196–198) |
| [PlannerTree](AKMMUncertainty/PlannerTree.lean) | 8 | (7.10)–(7.14), the Euler equation from optimality (AKMM §7.3.2, pp. 198–199) |
| [PlannerSufficiency](AKMMUncertainty/PlannerSufficiency.lean) | 9 | Euler and transversality sufficient, the log closed form (AKMM §7.3.2, pp. 199–200) |
| [Recursive](AKMMUncertainty/Recursive.lean) | 8 | (7.15)–(7.16), the envelope condition, the printed Euler equation refuted (AKMM §7.3.3, pp. 200–201) |
| [Linearization](AKMMUncertainty/Linearization.lean) | 10 | Certainty equivalence, (7.17)–(7.19), `g_K` and `g_A` (AKMM §7.3.4, pp. 201–203) |
| [CompleteMarkets](AKMMUncertainty/CompleteMarkets.lean) | 17 | Definitions 13–14, (7.20)–(7.25), insurance, risk sharing, spanning (AKMM §7.4, pp. 204–210) |
| [GrowthEquilibrium](AKMMUncertainty/GrowthEquilibrium.lean) | 5 | Definition 15, (7.26)–(7.29), equivalence with the planner (AKMM §7.5, pp. 210–212) |
| [RecursiveEquilibrium](AKMMUncertainty/RecursiveEquilibrium.lean) | 2 | Definition 16 and its functional Euler equation (AKMM Appendix 7.A.1, p. 840) |
| [IncompleteMarkets](AKMMUncertainty/IncompleteMarkets.lean) | 5 | The income-fluctuation problem: first-order, envelope and Euler conditions (AKMM §7.6, pp. 213–215) |
| [IncomeFluctuation](AKMMUncertainty/IncomeFluctuation.lean) | 21 | Figure 7.4(A) for Markov income: monotone decision rules, `ā`, the ergodic set (AKMM §7.6, p. 214) |
| [IncomeFluctuationStationary](AKMMUncertainty/IncomeFluctuationStationary.lean) | 7 | Figure 7.4(B): the transition of `(a, y)`, an accessible atom, the unique stationary distribution and convergence (AKMM §7.6, p. 215) |
| [IncomeFluctuationExample](AKMMUncertainty/IncomeFluctuationExample.lean) | 7 | A solved two-state Markov instance; the high-income rule need not cross the 45-degree line (AKMM §7.6, pp. 213–215) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
