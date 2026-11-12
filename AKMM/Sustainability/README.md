# AKMM Chapter 25: Sustainability, in Lean

This is the `AKMM/Sustainability` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 25 (Sustainability, by J. Hassler, P. Krusell and C. Olovsson) of Marina Azzimonti, Per
Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025),
pp. 749–784, with Appendix 25.A (p. 909), cited by the draft's pages. Run the commands below from
this directory. [Return to the library index](../../README.md).

Chapter 25 builds integrated assessment models from a climate module, a carbon cycle and a
growth model, and then studies natural resources in finite supply. Formalised: the
energy-balance ODE and the two-box climate model with their steady states and stability; the
three-reservoir carbon cycle (sign-corrected) and the GHKT carbon kernel; Nordhaus damages and
the adaptation example; the static IAM with Pigou taxes, caps and two firms; the CES energy
aggregate with its price index and duality; the market saving rate; **the GHKT optimal carbon
tax (25.32) as a theorem about the planner's optimum**, proved by an exact finite-horizon
decomposition of log utility under Cobb–Douglas production and full depreciation; cake eating
with its market equilibrium and Hotelling rents; Dasgupta–Heal growth; Hotelling with
extraction costs; the Leontief resource economy; the inversion of factor-augmenting technologies
(25.33)–(25.34); and the technology-menu result. Not formalised: data, facts and figures,
calibrated numbers and simulations, the climate-science narrative and the empirical
discussion. Eleven printed errors are corrected and six departures recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **164 theorems**, all new; it reuses
Sargent–Stachurski (`ContinuousTime`, `OperatorsFixedPoints`), Miao (`DifferenceEquations`),
Stokey–Lucas (`DeterministicApplications`) and Obstfeld–Rogoff (`RealExchangeRate`).

* **Climate** (§25.3.1): the solution of (25.1), its uniqueness and convergence (`eq_25_1`,
  `eq_25_1_unique`, `eq_25_1_tendsto`), (25.3) and the ECS (`eq_25_3`, `climate_ecs`,
  `climate_ecs_doubling`), the steady state of (25.4)–(25.5) (`eq_25_4_steady_iff`) and its
  stability (`climate_twoBox_tendsto`, `climate_twoBox_isStable`).
* **Carbon cycle** (§25.3.2): (25.6)–(25.8) corrected and printed (`eq_25_6_total`,
  `eq_25_6_printed_false`), the Markov structure and invariant split (`carbon_isMarkov`,
  `carbon_exists_invariant`, `carbon_invariant_unique`), linearity (`carbon_superposition`),
  (25.9)–(25.10) (`eq_25_9`, `excessCarbon_pulse`, `eq_25_10_tendsto`,
  `eq_25_10_within_period`, `ghktKernel_hasSum`).
* **Damages** (§25.3.5): Nordhaus (`nordhausD_approx`, `nordhausD_convexOn`,
  `nordhausD_not_convexOn`, `nordhausD_tendsto`) and adaptation (`adaptation_optimal`,
  `adaptation_unique`, `adaptation_low_T`).
* **Static IAM** (§25.4.1): (25.16)–(25.19) (`eq_25_16`, `eq_25_17`, `eq_25_18_exists`,
  `static_pigou`, `static_private_deriv_zero`, `eq_25_19`, `static_cap_nonbinding`,
  `static_cap_binding`), two firms with the coal cost restored (`static_two_optimal`,
  `static_two_cap`).
* **Dynamic IAM** (§25.4.2, App. 25.A): (25.26)–(25.28) (`eq_25_27_index`, `eq_25_27_cost`,
  `eq_25_27_foc`, `eq_25_26_least_cost`, `eq_25_28`), the saving rate (`eq_25_29_saving`,
  `saving_below`, `saving_above_tendsto`, `saving_above_tvc`), the oil owner
  (`oil_owner_optimal`), the appendix weights (`eq_25_A_ratio`, `eq_25_A_normalize`).
* **The optimal tax** (pp. 770–771): `lg_identity`, `lg_compare`, `ghkt_optimal`,
  `eq_25_31`, `ghkt_tax_of_proportional`, `eq_25_32`, `eq_25_32_ghkt`, with the coal economy as
  an instance (`ghkt_coal_optimal`).
* **Natural resources** (§25.5.2): cake eating (`cake_overtake`, `cake_optimal`, `cake_unique`,
  `cake_slp`), markets and Hotelling (`hotelling_price_const`, `cake_market_equilibrium`,
  `hotelling_rent_pos`, `hotelling_rule`, `hotelling_cost_rule`), Dasgupta–Heal (`dh_optimal`,
  `dh_bgp`, `dh_growth_tendsto`, `dh_interest_tendsto`, `dh_hotelling`).
* **Complementarity and technology** (§25.5.3): the Leontief economy
  (`leontief_optimal_tight`, `leontief_e0_infeasible`, `leontief_eventually_declines`,
  `leontief_abundant`), (25.33)–(25.34) corrected (`ces_share_e`, `eq_25_33`, `eq_25_34`,
  `eq_25_34_printed_false`), the technology menu (`menu_reduced_le`, `menu_reduced_attained`,
  `menu_elasticity`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](AKMMSustainability/Basics.lean) | 5 | Tangent-line bounds for `log` and powers |
| [Climate](AKMMSustainability/Climate.lean) | 11 | (25.1)–(25.5): energy balance, ECS, two-box stability (AKMM §25.3.1, pp. 753–755) |
| [CarbonCycle](AKMMSustainability/CarbonCycle.lean) | 17 | (25.6)–(25.10): carbon cycle, GHKT kernel (AKMM §25.3.2, pp. 755–756, p. 770) |
| [Damages](AKMMSustainability/Damages.lean) | 9 | Nordhaus damages, adaptation (AKMM §25.3.5, p. 763) |
| [StaticIAM](AKMMSustainability/StaticIAM.lean) | 24 | (25.11)–(25.19), two firms (AKMM §25.4.1, pp. 764–767) |
| [DynamicIAM](AKMMSustainability/DynamicIAM.lean) | 18 | (25.22)–(25.29), the saving rate, App. 25.A (AKMM §25.4.2, pp. 768–770; p. 909) |
| [CakeEating](AKMMSustainability/CakeEating.lean) | 20 | Cake eating, markets, Hotelling, the oil owner (AKMM §25.5.2, pp. 775–778; p. 769) |
| [LogGrowth](AKMMSustainability/LogGrowth.lean) | 6 | The log/Cobb–Douglas/full-depreciation decomposition (AKMM pp. 770, 777) |
| [OptimalTax](AKMMSustainability/OptimalTax.lean) | 17 | (25.30)–(25.32): the GHKT planner and optimal tax (AKMM §25.4.2, pp. 770–771) |
| [DasguptaHeal](AKMMSustainability/DasguptaHeal.lean) | 14 | Growth with an exhaustible resource (AKMM §25.5.2, pp. 777–778) |
| [Leontief](AKMMSustainability/Leontief.lean) | 9 | Strong complementarity (AKMM §25.5.3, p. 779) |
| [FactorTechnology](AKMMSustainability/FactorTechnology.lean) | 14 | (25.33)–(25.35): technology inversion and menus (AKMM §25.5.3, pp. 779–782) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
