# AKMM Chapter 3: The Solow Model, in Lean

This is the `AKMM/Solow` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 3 and Appendix 3.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 3 presents the discrete-time Solow model: the aggregate production function and its
intensive form, the steady state and its global stability, other kinds of dynamics (endogenous
growth, poverty traps, non-monotone dynamics), the growing economy and balanced growth, factor
prices and shares, the speed of convergence, and the use of the model for business cycles with
impulse responses; Appendix 3.A proves a discrete-time Uzawa theorem in two parts. Every
derivation and precise claim of the text is proved, including both Uzawa theorems; strict
concavity of `f` is derived from the book's Assumptions 1–6 rather than assumed. The qualitative
claims of Figures 3.3 (poverty traps and raising saving) and 3.5 (faster convergence with a higher
`λ`) are proved too. Not formalised: the data, the other figures, calibrated numbers and numerical
impulse responses, and the narrative chaos claim. The project depends on EconomicGrowth's
`DiscreteTime` and `Solow1956` libraries (the Solow map, steady state, global convergence,
comparative statics and slope at the steady state) and on `UzawaModern` (the weighted-moment
identity); the book's statements are proved from them in the book's notation. Five printed errors
are corrected, missing hypotheses of Theorem .2 and of the poverty-trap saving claim are
supplied and two points in the assumptions are checked, as recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **109 theorems**, all new.

* **Production** (§3.1): Assumptions 1–6 (`SolowAssumptions`, `StrictQuasiconcavePos`); the
  intensive form (`intensive`, `solow_intensive_form`); strict concavity of `f` from strict
  quasiconcavity and constant returns (`solow_intensive_strictConcave`), `f' > 0`
  (`solow_intensive_deriv_pos`), hence EconomicGrowth's `Technology` (`solow_technology`);
  Cobb–Douglas satisfies all assumptions (`solow_cobbDouglas_assumptions`); Assumption 1 vs 4 and
  Assumption 2 alone (`solow_assumption1_conflicts_assumption4`,
  `solow_assumption2_alone_counterexample`).
* **The basic model** (§3.1–3.1.1): (3.5) (`eq_3_5`); the unique steady state
  (`solow_steady_existsUnique`), also under the weak boundary conditions
  (`solow_steady_existsUnique_weak`, `solow_global_convergence_weak`); global monotone
  convergence and the book's proof steps (`solow_global_convergence`,
  `solow_convergence_proof_steps`); (3.6) (`eq_3_6`); comparative statics and `k̄/ȳ = s/δ`
  (`solow_steady_strictMono_saving`, `solow_steady_strictAnti_depreciation`,
  `solow_capital_output_ratio`).
* **Other dynamics** (boxes, pp. 75–78): endogenous growth (`solow_endogenous_no_steady_state`,
  `solow_endogenous_growth`, `solow_ak_constant_gap`, `solow_ak_plus_labour`); poverty traps
  (`solow_poverty_trap_unstable`); overshooting with a decreasing map and local stability from the
  slope (`solow_decreasing_map_overshoots`, `solow_local_stability`).
* **The growing economy** (§3.2–3.3): (3.7) and (3.8) (`eq_3_7`, `eq_3_8`); balanced growth and
  convergence (`solow_bgp_existsUnique`, `solow_detrended_convergence`,
  `solow_aggregate_convergence`); growth of income per capita on and off the balanced path
  (`solow_bgp_income_growth`, `solow_transition_growth`, `solow_income_growth_tendsto`); factor
  prices, Euler's theorem and shares (`solow_rental_rate`, `solow_wage_rate`, `solow_euler`,
  `solow_factor_shares`, `solow_cobbDouglas_shares`).
* **Convergence** (§3.4): (3.10)–(3.13) as exact derivatives (`eq_3_10`, `eq_3_11`, `eq_3_12`,
  `eq_3_13`); independence of `s` (`solow_speed_independent_of_saving`,
  `solow_cobbDouglas_forces_offset`); local stability (`solow_steady_locally_stable`, `solow_steady_locallyAttracting`); the p. 88
  saving experiment, corrected (`solow_saving_output_ratio`, `solow_p88_doubling_saving`).
* **Business cycles** (§3.5): the three variants (`solow_rbc_reduces`,
  `solow_harrod_hicks_cobbDouglas`, `solow_investment_specific`, `solow_demand_shock`); (3.17),
  (3.18) and the impulse responses (`eq_3_17`, `solow_irf_log_form`, `eq_3_18`,
  `solow_irf_capital_sum`, `solow_irf_capital_closed_form`); the output response, corrected
  (`solow_irf_output`, `solow_irf_output_printed_false`); `g_k`, `g_A`
  (`solow_level_linearisation`).
* **Uzawa** (Appendix 3.A): Theorem .1 (`theorem_3A_1`, `uzawa_technology_growth`,
  `uzawa_printed_rate_counterexample`); Theorem .2 (`theorem_3A_2`, `uzawa_capital_growth`,
  `uzawa_investment_growth`, `eq_3A_4`, `uzawa_part2_nonneg_consumption`,
  `uzawa_part2_zero_output_counterexample`).
* **Figure claims** (Figs. 3.3, 3.5): three steady states with the figure's crossing pattern
  (`SolowThreeCrossings`), global basins and stability (`solow_poverty_trap_basins`,
  `solow_poverty_trap_stability`); a large enough saving rise leaves one steady state, above
  `k̄₃`, with global convergence, and a temporary rise escapes the trap
  (`solow_poverty_trap_saving_rise`, `solow_poverty_trap_saving_rise_removes`,
  `solow_poverty_trap_temporary_saving`), with a concrete technology
  (`solow_poverty_trap_example`, `solow_poverty_trap_example_dynamics`); a higher `λ` gives a
  smaller gap at every date and fewer steps (`solow_linearised_gap_closed_form`,
  `solow_faster_convergence`), and `λ` falls with `α`, rises with `δ` (`solow_speed_parameters`).

All names are in the namespace `AKMM.Solow`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Production](AKMMSolow/Production.lean) | 13 | Assumptions 1–6, the intensive form and its strict concavity, Cobb–Douglas (AKMM §3.1, pp. 72–73) |
| [BasicModel](AKMMSolow/BasicModel.lean) | 18 | (3.5), steady state, weak conditions, global convergence, (3.6), comparative statics (AKMM §3.1.1, pp. 73–75) |
| [OtherDynamics](AKMMSolow/OtherDynamics.lean) | 7 | Endogenous growth, AK, poverty traps, overshooting, local stability (AKMM boxes, pp. 75–78) |
| [GrowingEconomy](AKMMSolow/GrowingEconomy.lean) | 21 | (3.7), (3.8), balanced growth, growth rates, factor prices and shares (AKMM §3.2–3.3, pp. 78–81) |
| [Convergence](AKMMSolow/Convergence.lean) | 13 | (3.10)–(3.13), local stability, the p. 88 saving experiment (AKMM §3.4, pp. 82–88) |
| [BusinessCycles](AKMMSolow/BusinessCycles.lean) | 13 | Business-cycle variants, (3.17)–(3.18), impulse responses, `g_k`, `g_A` (AKMM §3.5, pp. 88–92) |
| [Uzawa](AKMMSolow/Uzawa.lean) | 11 | Uzawa's theorem in discrete time, Parts I and II (AKMM App. 3.A, pp. 825–826) |
| [FigureClaims](AKMMSolow/FigureClaims.lean) | 13 | Poverty-trap basins, stability and saving (Fig. 3.3, p. 77); faster convergence with higher `λ` (Fig. 3.5, p. 82) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
