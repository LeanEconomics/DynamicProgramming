# AKMM Chapter 12: Labor supply, in Lean

This is the `AKMM/LaborSupply` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 12 (Labor supply, by R. Rogerson and G. L. Violante) of Marina Azzimonti, Per Krusell,
Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 325–367,
with Appendix 12.A (p. 849), cited by the draft's pages. Run the commands below from this
directory. [Return to the library index](../../README.md).

Chapter 12 builds the theory of labour supply from the static model to dynamic life-cycle models,
balanced growth, taxes and business cycles, human capital, and the extensive margin. Every numbered
equation the chapter derives and every precise claim is proved in the book's setting: the static
optimum and the Marshallian, Hicksian, income and Frisch elasticities (along differentiable paths of
optimal hours), two-stage budgeting, the estimation identities, the optimisation-friction
thresholds, balanced-growth (KPR) preferences in both directions (the "only if" under a stated
class, using AKMM Chapter 4's Theorem .4), Prescott's formula, the Imai–Keane condition, lotteries,
Ljungqvist–Sargent, heterogeneous disutility and the Rogerson–Wallenius threshold (in finite-period
versions). The qualitative claims of Figure 12.6 (Imai–Keane life-cycle profiles) are proved by
backward induction, with the decline of the human-capital term corrected (it needs `R ≤ 1` or
falling hours; a proved optimum with `R > 1` has it rising). Not formalised: the facts, tables, the
other figures, the empirical estimates, Chang–Kim and the other simulations. Eleven printed errors
are corrected, among them footnotes 2 and 8, the constant of (12.6), the sign of the Hicksian
compensation, the ordering limit `σ → ∞`, (12.37) itself (its `−1` puts it outside the KPR class),
the appendix's (12.A.1)–(12.A.3), and Prescott's U.S./Italy ratio (1.19, not 1.42), and two claims
read off Figure 12.6 are corrected; each comes with a Lean counterexample or corrected statement, as
recorded in [corrections](docs/corrections.md); every book item is located in the [source
map](docs/source-map.md). The library contains **151 theorems**.

* **The static model** (§12.3.1): the unique interior optimum and (12.1) (`eq_12_1`); the
  differentiated condition (`st_path_identity`); (12.2)–(12.4) (`eq_12_2`, `eq_12_3`, `eq_12_4`),
  utility constant on the compensated path (`st_compensated_utility`), Slutsky
  (`st_slutsky`, `st_substitution_effect`), signs (`st_signs`, `st_zero_income_signs`);
  footnote 2 corrected (`st_footnote_2`, `st_footnote_2_printed_false`); taxes and the
  budget-neutral rebate (`st_tax_as_wage`, `st_balanced_budget`, `st_balanced_budget_hicks_iff`).
* **Richer static models** (§12.3.2–12.3.3): home production (12.5)–(12.6) with the constant
  corrected (`eq_12_5`, `eq_12_6`, `eq_12_6_printed_false`); the unitary household
  (`hh_relative_hours`, `hh_cross_wage`, `hh_added_worker`); leisure in utility (`lt_corner`,
  `lt_elasticity_limits`); the two-period Frisch elasticity and footnote 8 (`tp_frisch`,
  `footnote_8`, `footnote_8_printed_false`).
* **Dynamic elasticities** (§12.4.1): two-stage budgeting (`eq_12_9_to_12_11`, `dyn_two_stage`);
  (12.12)–(12.17) (`eq_12_12` … `eq_12_17`, `dyn_compensation_sign`); the Frisch formula (12.21)
  (`eq_12_21`, `dyn_frisch_separable_path`) and its GHH, Cobb–Douglas and leisure values
  (`dyn_frisch_ghh`, `dyn_ghh_no_income_effect`, `dyn_frisch_cd`, `dyn_frisch_leisure`); the
  ordering (`dyn_ordering`, `dyn_ordering_sigma_zero`, `dyn_ordering_sigma_infty`); (12.23)
  (`eq_12_23`).
* **Estimation and frictions** (§12.4.2): (12.24)–(12.31) (`eq_12_24` … `eq_12_31`,
  `fe_log_approx`, `fe_consumption_data`), with the log-normal step on Mathlib's Gaussian;
  (12.32)–(12.35) and the thresholds (`eq_12_33`, `fr_value`, `eq_12_34`, `fr_gain_strictMono`,
  `eq_12_35`, `fr_threshold`).
* **Balanced growth** (§12.5, App. 12.A): "if" (`eq_12_37_if`, `kpr_homog`, `kpr_static_hours`);
  the printed (12.37) fails (`eq_12_37_printed_not_bgp`); "only if" (`eq_12_A_2`, `eq_12_A_3`,
  `eq_12_A_3_log`, `eq_12_37_only_if`).
* **Taxes, cycles, human capital** (§12.6–12.7): Prescott (`eq_12_39`,
  `eq_12_39_us_italy`); income effects (`ti_effect_ratio`, `ti_subsistence`, `ti_sigma_gt_one`);
  (12.40) (`eq_12_40`, `ti_no_capital`); Imai–Keane (`ik_marginal_earnings`, `eq_12_41`).
* **Figure 12.6, Imai–Keane profiles** (§12.7): backward induction for the human-capital term
  (`ikf_hc_last`, `ikf_hc_succ`, `ikf_hc_diff`); wage and return to work (`ikf_wage_step`,
  `ikf_return_vs_wage`); the decline of the human-capital term (`ikf_hc_antitone`,
  `ikf_hc_step_peak`, `ikf_hc_const_hours`) and its failure for `R > 1` (`ikf_hc_rises`);
  monotone hours (`ikf_hours_up_strict`, `ikf_hours_down_strict`); flat hours and return at
  `R = β = 1` and the naive estimate (`ikf_flat`, `ikf_flat_naive`).
* **Indivisible labour** (§12.8): lotteries and the infinite aggregate Frisch elasticity
  (`il_lottery`, `il_planner`, `il_frisch_infinite`); Ljungqvist–Sargent
  (`il_lagrange_suff`, `il_ljungqvist_sargent`); heterogeneous `ψ` (`il_vtilde_deriv`,
  `il_vtilde_convex`, `il_hetero_frisch`); concentration and Rogerson–Wallenius
  (`il_concentrate`, `il_rw_threshold`, `il_rw_life_cycle`).

All names are in the namespace `AKMM.LaborSupply`. The project imports
[AKMM/DynamicOptimization](../DynamicOptimization/README.md) (Theorem .4, the CRRA
characterisation of balanced growth) and
[EconomicDynamics/NeoclassicalGrowth](../../EconomicDynamics/NeoclassicalGrowth/README.md)
(the GHH marginal utilities, `rb_ghh_mrs`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Static](AKMMLaborSupply/Static.lean) | 26 | (12.1)–(12.4), fn. 2, taxes and transfers (AKMM §12.3.1, pp. 331–335) |
| [StaticExtensions](AKMMLaborSupply/StaticExtensions.lean) | 20 | (12.5)–(12.6), households, leisure, two periods, fn. 8 (AKMM §12.3.2–12.3.3, pp. 335–341) |
| [Dynamic](AKMMLaborSupply/Dynamic.lean) | 24 | (12.9)–(12.23): two-stage budgeting, Marshallian, Hicksian and Frisch elasticities (AKMM §12.4.1, pp. 341–346) |
| [Estimation](AKMMLaborSupply/Estimation.lean) | 18 | (12.24)–(12.35): estimation identities, optimisation frictions (AKMM §12.4.2, pp. 347–352) |
| [BalancedGrowth](AKMMLaborSupply/BalancedGrowth.lean) | 13 | (12.36)–(12.37), (12.A.1)–(12.A.3): KPR preferences (AKMM §12.5, pp. 352–353, p. 849) |
| [TaxesCycles](AKMMLaborSupply/TaxesCycles.lean) | 12 | (12.38)–(12.41): Prescott, income effects, cycles, Imai–Keane (AKMM §12.6–12.7, pp. 353–359) |
| [IndivisibleLabor](AKMMLaborSupply/IndivisibleLabor.lean) | 14 | (12.44): lotteries, Ljungqvist–Sargent, heterogeneity, Rogerson–Wallenius (AKMM §12.8, pp. 359–367) |
| [HumanCapitalProfiles](AKMMLaborSupply/HumanCapitalProfiles.lean) | 24 | Figure 12.6: Imai–Keane life-cycle profiles, human-capital term, hours (AKMM §12.7, pp. 357–358) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
