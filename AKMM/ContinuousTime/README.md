# AKMM Chapter 9: Continuous-time analytical techniques, in Lean

This is the `AKMM/ContinuousTime` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 9 and Appendix 9.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 9 introduces continuous-time tools: growth rates and logs, the maximum principle derived
from a discrete-time Hamiltonian, continuous discounting and the no-Ponzi condition, the
continuous Solow and Ramsey models with the decentralized equilibrium, and Poisson uncertainty
with unemployment flows; Appendix 9.A adds the nPg with time-varying interest and the failure of
the TVC below the saddle path. Everything is formalised in continuous time, as the book does.
Mathlib has no Pontryagin maximum principle: the first-order conditions are proved as calculus
identities, their *sufficiency* is proved as a Mangasarian–Arrow theorem for every problem of the
chapter, and their general *necessity* is not formalised; in discrete time necessity is proved
directly by perturbation. Mathlib has no Poisson process: the binomial limit, the exponential
distribution, memorylessness and survival with time-varying rates are proved. The project
depends on Sargent–Stachurski's `ContinuousTime` (scalar exponential IVPs, memorylessness),
`EulerTransversality` (the finite-horizon supergradient bound), and EconomicGrowth's `Solow1956`
(general Solow dynamics) and `RamseyCassKoopmans` (the Cass optimum, its certificate,
stationary and golden-rule facts). Six printed errors are corrected and five departures
recorded in [corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **123 theorems**, all new.

* **Growth rates** (§9.1, App. 9.A.1–9.A.2): (9.1)–(9.5) (`eq_9_2`, `eq_9_4`, `eq_9_4_unique`,
  `eq_9_3_unique`, `eq_9_5`); growth accounting (`growthRates_growth_accounting`); footnote 1
  (`growthRates_log_one_add_approx`); the appendix identities (`appendix_9A1`,
  `appendix_9A2_exp`, `appendix_9A2_log`).
* **The discrete Hamiltonian** (§9.2): the Lagrangian rewriting and (9.8)–(9.14)
  (`discreteHamiltonian_lagrangian`, `eq_9_9`, `eq_9_10`, `eq_9_13`, `eq_9_14`,
  `discreteHamiltonian_tvc_iff`); sufficiency (`discreteHamiltonian_finite_sufficient`,
  `discreteHamiltonian_infinite_sufficient`) and necessity
  (`discreteHamiltonian_euler_necessary`, `discreteHamiltonian_tvc_necessary`,
  `discreteHamiltonian_euler_necessary_infinite`); the nPg example corrected
  (`discreteBudget_npg_counterexample`).
* **Budgets and discounting** (§9.2, App. 9.A.3): the telescoped budget and nPg ⇔ lifetime
  budget (`appendix_9A3_discrete_budget`, `appendix_9A3_discrete_npg_iff_lbc`); (9.18) and the
  discount limit (`eq_9_18`, `continuousBudget_discount_limit`); the integrating factor and the
  corrected continuous budget (`appendix_9A3_continuous_budget`,
  `appendix_9A3_printed_budget_false`, `appendix_9A3_continuous_npg_iff_lbc`); the product limit
  (`productLimits_product`, `appendix_9A3_product_limit`).
* **The maximum principle** (§9.2): (9.19)–(9.26) and the boxes (`eq_9_20`, `eq_9_21`,
  `eq_9_22`, `eq_9_23`, `eq_9_26`, `continuousHamiltonian_crra_relative_risk_aversion`,
  `continuousHamiltonian_discrete_euler_remainder`); Mangasarian–Arrow sufficiency
  (`mangasarian`, `mangasarian_catching_up`, `mangasarian_consumption_saving`,
  `mangasarian_planner`, `mangasarian_planner_steady_state`).
* **Solow** (§9.3.1): (9.31)–(9.32), the phase line, convergence and balanced growth (`eq_9_31`,
  `eq_9_32`, `solowContinuous_phase_line`, `solowContinuous_convergence`,
  `solowContinuous_income_per_capita_growth`).
* **Ramsey** (§9.3.2, App. 9.A.4): (9.35), the phase signs, the modified golden rule
  (`eq_9_35`, `ramseyPlanner_phase_signs`, `ramseyPlanner_modified_golden_rule`); the saddle path
  for the Cobb–Douglas–CRRA model (`ramseySaddle_primitives`, `ramseySaddle_of_interior`,
  `ramseySaddle_path`, `ramseySaddle_crra_cobbDouglas`); (9.A.1)–(9.A.6) and the TVC on and below
  the saddle path (`appendix_9A4_marginal_utility`, `appendix_9A4_tvc_iff`,
  `appendix_9A4_saddle_tvc`, `appendix_9A4_below_saddle_violates_tvc`).
* **The market equilibrium** (§9.3.2): (9.36)–(9.39) (`eq_9_37`, `market_household_optimal`,
  `market_firm_marginal_products`, `market_firm_optimal`, `market_equilibrium_planner_system`,
  `market_planner_is_equilibrium`).
* **Poisson uncertainty** (§9.4): (9.40)–(9.43) and the Poisson limit (`eq_9_41`, `eq_9_42`,
  `eq_9_43`, `poisson_limit`, `poisson_sum_mean`); survival and memorylessness
  (`poisson_survival_memoryless`, `poisson_memoryless_iff_exponential`,
  `poisson_survival_time_varying`, `productLimits_survival`); `E[duration] = 1/σ`
  (`poisson_expected_duration`); unemployment flows (9.44) (`unemployment_steady_state`,
  `unemployment_unique`, `unemployment_converges`, `unemployment_rate_comparative_statics`).

All names are in the namespace `AKMM.ContinuousTime`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [GrowthRates](AKMMContinuousTime/GrowthRates.lean) | 14 | (9.1)–(9.5), growth accounting, `log(1 + x) ≈ x`, logs and the chain rule (AKMM §9.1, pp. 242–243; App. 9.A.1–9.A.2, pp. 843–844) |
| [DiscreteBudget](AKMMContinuousTime/DiscreteBudget.lean) | 10 | Telescoped budget with `r_t`, nPg ⇔ lifetime budget, the nPg example (AKMM §9.2, p. 246; App. 9.A.3, p. 844) |
| [DiscreteHamiltonian](AKMMContinuousTime/DiscreteHamiltonian.lean) | 9 | Discrete Hamiltonian, (9.8)–(9.14), TVC, finite-horizon sufficiency (AKMM §9.2, pp. 244–245) |
| [DiscreteOptimality](AKMMContinuousTime/DiscreteOptimality.lean) | 10 | Necessity by perturbation; infinite-horizon TVC, sufficiency and necessity (AKMM §9.2, pp. 244–246) |
| [ContinuousBudget](AKMMContinuousTime/ContinuousBudget.lean) | 10 | (9.16)–(9.18), the discount limit, the integrating factor and continuous lifetime budget (AKMM §9.2, pp. 246–248; App. 9.A.3, pp. 845–846) |
| [ProductLimits](AKMMContinuousTime/ProductLimits.lean) | 4 | Riemann sums, `∏(1 + r(tΔ)Δ) → e^{∫r}`, time-varying survival (AKMM App. 9.A.3, pp. 844–845; §9.4, p. 259) |
| [ContinuousHamiltonian](AKMMContinuousTime/ContinuousHamiltonian.lean) | 12 | (9.19)–(9.26), current value, CRRA, discrete vs continuous Euler (AKMM §9.2, pp. 248–250) |
| [Mangasarian](AKMMContinuousTime/Mangasarian.lean) | 7 | Mangasarian–Arrow sufficiency; consumption–saving and planner (AKMM §9.2–9.3, pp. 246–255) |
| [SolowContinuous](AKMMContinuousTime/SolowContinuous.lean) | 6 | (9.27)–(9.32), phase line, convergence, balanced growth (AKMM §9.3.1, pp. 251–253) |
| [RamseyPlanner](AKMMContinuousTime/RamseyPlanner.lean) | 10 | (9.33)–(9.35), Figure 9.2 signs, modified golden rule, (9.A.1)–(9.A.6) (AKMM §9.3.2, pp. 253–255; App. 9.A.4, pp. 846–848) |
| [RamseySaddle](AKMMContinuousTime/RamseySaddle.lean) | 7 | The saddle path via EconomicGrowth's Cass optimum, Cobb–Douglas–CRRA instance (AKMM §9.3.2, pp. 254–255) |
| [MarketEquilibrium](AKMMContinuousTime/MarketEquilibrium.lean) | 6 | (9.36)–(9.39), households, firms, the planner allocation as an equilibrium (AKMM §9.3.2, pp. 256–257) |
| [Poisson](AKMMContinuousTime/Poisson.lean) | 13 | (9.40)–(9.43), the Poisson limit, survival, memorylessness, expected duration (AKMM §9.4, pp. 257–259) |
| [Unemployment](AKMMContinuousTime/Unemployment.lean) | 5 | (9.44), steady state, convergence, comparative statics (AKMM §9.4, pp. 259–260) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
