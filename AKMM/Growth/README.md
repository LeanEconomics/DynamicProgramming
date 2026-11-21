# AKMM Chapter 13: Growth, in Lean

This is the `AKMM/Growth` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 13 (Growth, by T. Boppart and P. J. Klenow) of Marina Azzimonti, Per Krusell, Alisdair
McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 369–404, with
Appendix 13.A (pp. 850–862), cited by the draft's pages. Run the commands below from this
directory. [Return to the library index](../../README.md).

Chapter 13 combines growth and development accounting with a continuous-time neoclassical model
with investment-specific technical change (ISTC) and three endogenous growth models: AK, Romer's
expanding varieties (with Jones's semi-endogenous variant) and Aghion–Howitt quality ladders.
Everything is formalised in continuous time, as the book does. Mathlib has no Pontryagin
maximum principle: the first-order conditions are derived as calculus identities and their
*sufficiency* is proved with the Mangasarian–Arrow theorem of AKMM Chapter 9
(`AKMMContinuousTime`), for the ISTC planner, the AK planner and household, the Romer planner and
the quality-ladder planner. The aggregate quality index is defined by its mean-field law, with
the single-ladder Poisson expectation proved. Not formalised: the facts, tables and figures, the
calibrations and the narrative. Ten printed errors are corrected and five departures recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **175 theorems**, all new.

* **Accounting** (§13.2, §13.4): (13.1)–(13.3) (`eq_13_2`, `eq_13_3_log`, `eq_13_3`), nominal
  development accounting (13.17) (`eq_13_17`), footnote 23 (`accounting_footnote_23`,
  `accounting_footnote_23_value`), the U.S. decomposition (`accounting_us_decomposition`).
* **The ISTC model** (§13.3, App. 13.A.1–13.A.2): the return condition (13.5) (`eq_13_5`), firm
  optimality and (13.A.1)–(13.A.3) (`istc_firm_optimal`, `eq_13_A_1`, `eq_13_A_2`, `eq_13_A_3`),
  the Euler equation (`eq_13_A_7`), (13.A.8)/(13.10) (`eq_13_A_8`, `eq_13_10`), Walras's law
  (`istc_walras`), (13.A.11) (`eq_13_A_11`), the planner (`istc_planner_euler`), the
  labour-augmenting form (`istc_labour_augmenting`, `istc_budget_reduced`).
* **The balanced growth path**: the standard candidate fails (`istc_standard_candidate_fails`),
  detrending (`eq_13_12`, `eq_13_13`), the unique steady state (`eq_13_14`, `eq_13_15`,
  `istc_steady_unique`), the TVC iff (13.8) (`istc_bgp_tvc_iff`), boundedness corrected
  (`istc_bgp_utility_integrable`, `istc_bgp_utility_unbounded`), optimality
  (`istc_optimal`, `istc_bgp_optimal`, `istc_closed_form_optimal`).
* **Predictions**: `s*` (`istc_footnote_14`, `istc_saving_rate_bgp`), the golden rule (13.16)
  (`eq_13_16`, `istc_golden_saving`, `istc_below_golden_iff`), prices (`istc_r_star`,
  `istc_rental_bgp`, `istc_wage_bgp`), nominal and real `K/Y` with the corrected deflator
  (`istc_nominal_KY`, `istc_real_KY_growth`, `istc_deflator_printed_false`), the `σ = α` closed
  form and its global transition (`istc_closed_form`, `istc_closed_form_path`,
  `istc_closed_form_converges`).
* **Linearisation** (App. 13.A.3): the Jacobian (13.A.14) and characteristic equation (13.A.15)
  (`eq_13_A_14`, `eq_13_A_15`), saddle stability (`istc_saddle`), the stable root and half-life
  (`istc_stable_root`, `istc_half_life`).
* **The AK model** (§13.5): (13.19)–(13.20) (`eq_13_19`, `eq_13_20`), the policy and boundedness
  (`ak_policy`, `ak_bounded_iff`), optimality and decentralisation (`ak_optimal`,
  `ak_decentralized`), footnote 24 (`ak_footnote_24_general`, `ak_footnote_24_unique`), footnote
  25 (`ak_footnote_25`).
* **Expanding varieties** (§13.5.1): (13.23)–(13.46) (`eq_13_33`, `eq_13_37`, `eq_13_41`,
  `eq_13_43`, `eq_13_44`, `eq_13_46`), footnote 33 — the balanced path is the only equilibrium
  (`romer_footnote_33`), footnote 34 corrected (`romer_footnote_34`), comparative statics
  (`romer_comparative_statics`), taxes and markups (`romer_theta_growth_mono`); the planner
  (`eq_13_A_16`, `eq_13_A_17`, `eq_13_A_21`, `eq_13_50`, `romer_planner_optimal`), machine use and
  the subsidy corrected (`romer_machine_ratio`, `romer_subsidy`), `g^{DE} < g^{SP}`
  (`romer_planner_growth_gt`).
* **Semi-endogenous growth**: (13.54)–(13.60) (`eq_13_54`, `jones_value_unique`, `eq_13_55`,
  `eq_13_56`, `eq_13_59`, `jones_N_unique`, `eq_13_60`, `jones_level_effect`), the planner
  (`eq_13_A_24`, `jones_planner_bgp`).
* **Quality ladders** (§13.5.2, App. 13.A.9–13.A.10): (13.62)–(13.65) (`eq_13_63`, `eq_13_65`),
  drastic and incremental innovation (`eq_13_64`, `eq_13_A_26`, `eq_13_A_27`), research and the
  Arrow replacement effect (`quality_research_foc`, `quality_arrow_replacement`), the single
  ladder (`quality_single_ladder`), (13.66) and comparative statics (`eq_13_66`,
  `quality_comparative_statics`, `quality_growth_mono_lambda`), the planner (13.A.28)
  (`eq_13_A_28`, `quality_planner_aggregates`), and `g^{SP}` versus `g^{DE}`
  (`quality_sp_vs_de_ambiguous`).

All names are in the namespace `AKMM.Growth`. Dependencies: AKMM Chapter 9's
[`AKMMContinuousTime`](../ContinuousTime/README.md) (Mangasarian–Arrow sufficiency, the
consumption–saving sufficiency theorem, CRRA utility and its concavity).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Accounting](AKMMGrowth/Accounting.lean) | 8 | (13.1)–(13.3), (13.17), fn. 23, the U.S. decomposition (AKMM §13.2, pp. 372–374; §13.4, pp. 383–384) |
| [ISTCModel](AKMMGrowth/ISTCModel.lean) | 23 | (13.4)–(13.11), (13.A.1)–(13.A.12): prices, firms, households, Walras, planner (AKMM §13.3, pp. 376–378; App. 13.A.1–13.A.2, pp. 850–851) |
| [ISTCBGP](AKMMGrowth/ISTCBGP.lean) | 18 | (13.8), (13.12)–(13.15), TVC, boundedness (AKMM §13.3, pp. 378–379) |
| [ISTCPredictions](AKMMGrowth/ISTCPredictions.lean) | 20 | `s*`, (13.16), prices, nominal and real `K/Y`, the `σ = α` closed form (AKMM §13.3, pp. 380–381) |
| [ISTCLinear](AKMMGrowth/ISTCLinear.lean) | 7 | (13.A.13)–(13.A.15), saddle stability, half-life (AKMM App. 13.A.3, pp. 851–852) |
| [ISTCOptimality](AKMMGrowth/ISTCOptimality.lean) | 7 | Sufficiency of the FOCs, optimality of the BGP and of the `σ = α` transition (AKMM §13.3, App. 13.A.1–13.A.2) |
| [AKGrowth](AKMMGrowth/AKGrowth.lean) | 12 | (13.18)–(13.20), fn. 24–25 (AKMM §13.5, pp. 384–386) |
| [Romer](AKMMGrowth/Romer.lean) | 24 | (13.21)–(13.46), (13.52), comparative statics (AKMM §13.5.1, pp. 386–392) |
| [RomerDynamics](AKMMGrowth/RomerDynamics.lean) | 7 | fn. 33–34: uniqueness, the corner (AKMM §13.5.1, p. 391) |
| [RomerPlanner](AKMMGrowth/RomerPlanner.lean) | 12 | (13.47)–(13.51), (13.A.16)–(13.A.21), subsidy (AKMM §13.5.1, p. 392; App. 13.A.6, pp. 853–854) |
| [Jones](AKMMGrowth/Jones.lean) | 15 | (13.53)–(13.60), (13.A.22)–(13.A.25) (AKMM §13.5.1, pp. 393–394; App. 13.A.7, pp. 854–855) |
| [QualityLadders](AKMMGrowth/QualityLadders.lean) | 16 | (13.61)–(13.66), (13.A.26)–(13.A.27) (AKMM §13.5.2, pp. 398–403; App. 13.A.9, p. 861) |
| [QualityPlanner](AKMMGrowth/QualityPlanner.lean) | 6 | (13.A.28), `g^{SP}` vs `g^{DE}` (AKMM §13.5.2, p. 404; App. 13.A.10, pp. 861–862) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
