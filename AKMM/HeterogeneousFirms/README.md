# AKMM Chapter 22: Heterogeneous firms, in Lean

This is the `AKMM/HeterogeneousFirms` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 22 (Heterogeneous firms, by T. Mukoyama) of Marina Azzimonti, Per Krusell, Alisdair
McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 663–692, with
Appendix 22.A (pp. 888–896), cited by the draft's pages. Run the commands below from this
directory. [Return to the library index](../../README.md).

Chapter 22 builds an aggregate production function from heterogeneous decreasing-returns firms,
measures misallocation, presents Hopenhayn–Rogerson firm dynamics, monopolistic competition and
Atkeson–Burstein oligopoly, the granular origins of aggregate fluctuations with Hulten's theorem,
and a discrete-time Klette–Kortum model of innovation and firm size. The unit mass of firms is a
probability space and the book's law of large numbers is the identification of cross-section
integrals with expectations. Imported results: the Dixit–Stiglitz demand and price index of Miao
Chapter 19 (`NewKeynesian`), the First Welfare Theorem of Stokey–Lucas–Prescott Chapter 15
(`ParetoOptimaEquilibria`) for Hulten's theorem, and the quality-ladder limit-pricing condition of
AKMM Chapter 13 (`AKMMGrowth`). Not formalised: the data, figures and tables, the calibrations,
the narrative and cited results, and Gabaix's granular limit theorem under Zipf's law (beyond the
text). Eleven printed errors are corrected and seven departures recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **128 theorems**, all new.

* **The simple model** (§22.2): two-stage cost minimisation under constant returns
  (`twostage_cost`, `twostage_profit_le`), the scale problem (22.1)–(22.2) (`eq_22_1`,
  `eq_22_2`), aggregation (22.3)–(22.7) (`eq_22_3`, `simple_A_eq`, `eq_22_7`), efficiency of the
  competitive allocation (`simple_planner`, `simple_planner_A`), footnote 2
  (`cobbDouglas_unit_cost`, `simple_footnote_2`).
* **Lognormal productivity** (22.8), App. 22.A.1: `eq_22_8`, `lognormal_mean`,
  `lognormal_A_strictMono`; `A ≥ ∫ a` for every distribution (`aggTFP_ge_mean`).
* **Misallocation** (§22.4): the FHK decomposition (`fhk_decomposition`), job flows (22.9) and
  `JC = JD` in a steady state (`jobflows_net`, `jobflows_steady`), wedges (22.10) (`eq_22_10`,
  `wedgeTFP_one`), the bivariate-normal formula (22.11) (`bivariate_mgf`, `eq_22_11`,
  `wedge_A_indep`, `wedge_A_strictAnti`), and wedges lower TFP for every distribution
  (`wedge_A_le`).
* **Hopenhayn–Rogerson** (§22.5): the Bellman equation (22.13) has a unique solution
  (`hr_bellman_existsUnique`); block recursivity and free entry (22.14): the entry value is
  strictly decreasing and continuous in the wage, the free-entry wage is unique and exists when
  bracketed, and entry barriers lower it (`hr_entry_strictAnti`, `hr_free_entry_unique`,
  `hr_free_entry_exists`, `hr_entry_barrier_wage`); the stationary distribution for a given entry
  mass exists, is unique, nonnegative and linear in the mass (`hr_stationary_existsUnique`,
  `hr_stationary_nonneg`, `hr_stationary_linear`); the labour market (22.15) pins the entry mass
  (`eq_22_15`, `hr_entry_mass`).
* **Monopolistic competition** (§22.6.1): (22.17)–(22.22) (`eq_22_17`, `eq_22_19`, `eq_22_20`,
  `eq_22_22`), `Y = (c/γ)(σ/(σ−1))M` and the modified `A` (`mc_output_eq`, `mc_aggregate_eq`).
* **Oligopoly** (§22.6.2, App. 22.A.4): the nested CES (`eq_22_24`, `eq_22_25`, `eq_22_29`), the
  Cournot elasticity from the marginal-revenue derivative (`eq_22_28`, `eq_22_27`) and its
  properties (`cournot_strictAntiOn`, `cournot_mem_Icc`, `cournot_symmetric_tendsto`), the
  Bertrand elasticity (`bertrand_demand_deriv`, `bertrand_markup`, sign corrections
  `bertrand_ratio`), Cournot markups exceed Bertrand markups (`markup_cournot_ge`).
* **Granularity** (§22.7): (22.30) (`eq_22_30`), equal sizes (`granular_equal_sizes`,
  `granular_herfindahl_ge`).
* **Hulten's theorem** (22.31), App. 22.A.5: `hulten` (via the imported First Welfare Theorem),
  Euler's identity (22.A.6) (`eq_22_A_6`), a concrete economy satisfying every hypothesis
  (`hulten_one_sector`), the two-sector example (22.32) (`eq_22_32`, `hulten_example_prices`).
* **Klette–Kortum** (§22.8): equal shares (22.36) (`eq_22_36`), (22.37)–(22.40) (`eq_22_37`,
  `eq_22_38`, `kk_limit_price_iff`, `eq_22_39`, `eq_22_40`), the Bellman equation (22.41)–(22.43)
  (`eq_22_41`, `eq_22_42`, `eq_22_43`), the equilibrium with corrected entry labour
  (`kk_equilibrium`), growth `λ^μ` (`kk_growth`), Gibrat's law (`kk_gibrat`).
* **Firm sizes** (p. 692, App. 22.A.6): the Pareto stationary density (`pareto_stationary`,
  `pareto_zeta_pos`, `pareto_zeta_mono`), transition probabilities of product lines (`fsdT`,
  `fsd_T_sum`) and the book's three groups with the corrected inner bound (`fsd_stay`,
  `fsd_from_above`, `fsd_from_below`, `fsd_below_zero`, `fsd_printed_bound_false`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SimpleModel](AKMMHeterogeneousFirms/SimpleModel.lean) | 17 | Two-stage cost minimisation, (22.1)–(22.7), fn. 2 (AKMM §22.2, pp. 664–665) |
| [Lognormal](AKMMHeterogeneousFirms/Lognormal.lean) | 10 | (22.8), (22.10)–(22.11) with lognormal laws (AKMM pp. 665, 672–673; App. 22.A.1, 22.A.3) |
| [Misallocation](AKMMHeterogeneousFirms/Misallocation.lean) | 8 | (22.9), FHK, the planner bound, wedges (AKMM §22.3–22.4, pp. 669–673) |
| [HopenhaynRogerson](AKMMHeterogeneousFirms/HopenhaynRogerson.lean) | 21 | (22.12)–(22.15), block recursivity, free entry, stationary distribution (AKMM §22.5, pp. 673–677) |
| [MonopolisticCompetition](AKMMHeterogeneousFirms/MonopolisticCompetition.lean) | 10 | (22.16)–(22.22), aggregation (AKMM §22.6.1, pp. 677–679) |
| [Oligopoly](AKMMHeterogeneousFirms/Oligopoly.lean) | 22 | (22.23)–(22.29), Cournot and Bertrand (AKMM §22.6.2, pp. 679–681; App. 22.A.4, pp. 892–893) |
| [Granularity](AKMMHeterogeneousFirms/Granularity.lean) | 5 | (22.30) (AKMM §22.7, p. 682) |
| [Hulten](AKMMHeterogeneousFirms/Hulten.lean) | 5 | (22.31)–(22.32), (22.A.5)–(22.A.8) (AKMM pp. 683–684; App. 22.A.5, pp. 894–896) |
| [HultenExample](AKMMHeterogeneousFirms/HultenExample.lean) | 2 | A one-sector economy satisfying every hypothesis of Hulten's theorem |
| [KletteKortum](AKMMHeterogeneousFirms/KletteKortum.lean) | 16 | (22.34)–(22.46), growth, Gibrat's law (AKMM §22.8, pp. 686–691) |
| [FirmSize](AKMMHeterogeneousFirms/FirmSize.lean) | 12 | Pareto tail, transitions of product lines (AKMM p. 692; App. 22.A.6, p. 896) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
