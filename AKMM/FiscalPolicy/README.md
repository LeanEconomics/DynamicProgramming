# AKMM Chapter 15: Government and public policies, in Lean

This is the `AKMM/FiscalPolicy` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 15 (Government and public policies, by M. Azzimonti, J. Heathcote and K. Storesletten) of
Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), pp. 439–466, with Appendix 15.A (pp. 868–870), cited by the draft's pages. Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 15 studies fiscal policy: debt dynamics and sustainability, proportional taxes in the
neoclassical growth model, tax incidence and the excess cost of taxation, the Laffer curve,
theories of government spending, Ricardian equivalence, Ramsey taxation by the primal approach
and its time inconsistency, pensions and debt with overlapping generations, and progressivity.
Every numbered equation the chapter derives, Definition 15.1 and every precise claim are proved
in the book's setting. The excess cost of taxation is proved positive for all parameter values
by an analytic argument. The claim that it is increasing in the capital tax, and minimal at zero,
is false in general; a Lean counterexample is given. Not formalised: the data and figures, the
numerical tax-reform transition (Figure 15.7, Figure 15.A.1) and the minimality of the excess cost
at the book's own parameters. Seven printed errors are corrected, as recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **136 theorems**.

* **Debt dynamics** (§15.2): (15.1) and the debt-to-GDP recursion (`dd_nominal_debt`,
  `dd_ratio_real`, with Cochrane's `debt_gdp_discrete`: `dd_ratio_const`); (15.2) (`eq_15_2`); the
  stable ratio `b* = d(1 + γ)/(γ − r)`, unique and globally stable for `γ > r`
  (`dd_stationary_iff`, `dd_tendsto_stationary`), divergence for `r > γ` (`dd_tendsto_atTop`); the
  309% example (`dd_box_309`).
* **Distortionary taxes** (§15.3): Definition 15.1 (`definition_15_1`, non-vacuous:
  `dt_example_ce`); (15.6) and the labour condition (`eq_15_6`, `dt_labour_foc`); firms
  (`dt_firm_foc`); the planner (15.7) (`dt_planner_euler`, `eq_15_7`).
* **Long run** (§15.3.1): (15.8)–(15.12) (`eq_15_8`, `eq_15_9`, `eq_15_11`, `eq_15_12`),
  `r` rising and `k/ℓ`, `w` falling in `τ_k` (`lr_rent_strictMonoOn`, `lr_ratio_strictAntiOn`,
  `lr_wage_strictAntiOn`), GHH partials and hours (`ghh_partials`, `lr_hours_strictAntiOn_*`).
* **Incidence** (§15.3.2): worker–capitalist equivalence (`inc_wk_iff_ra`); (15.13) and output
  falling in each tax (`eq_15_13`, `inc_output_strictAntiOn_*`); `c_w`, `c_k` (`inc_cw`, `inc_ck`).
* **Excess cost** (§15.3.2–15.3.3): (15.14) (`eq_15_14`); the flow-utility identity
  (`inc_flow_utility`); positivity (`inc_excess_cost_pos`); the counterexample to monotonicity
  (`inc_excess_cost_not_min_at_zero`); consumption vanishing as `τ_k → 1`
  (`inc_cons_tendsto_zero`); `τ_ℓ = .2529`, `.2985` (`inc_tau_l_025`, `inc_tau_l_0`).
* **Laffer** (§15.3.4): the revenue maximiser `(1/(1 + φ), 0)` (`laf_isMaxOn`,
  `laf_lt_of_pos`), footnote 6 (`footnote_6`), the hump (`laf_hump`).
* **Theories of G** (§15.3.5): `u₁ = u₂` (`tg_first_best`), public capital and increasing returns
  (`tg_irs`), `f_k − δ = f_g − δ_g` (`tg_net_returns_equal`).
* **Ricardian equivalence** (§15.4): `ric_pv_iff`, `ric_budgetSet_eq`, `ric_optimal_iff`,
  `ric_saving`, with Obstfeld–Rogoff's neutrality imported (`ric_obstfeld_rogoff`).
* **Ramsey** (§15.5): the primal approach (`rm_primal`, `eq_15_18`, `rm_walras`), the Lagrangian
  first-order conditions (`rm_foc_c0` … `rm_foc_l1`), separable CRRA (`rm_crra_derivs`,
  `rm_crra_focs`), `τ_{b,1} = 0` and `τ₀ = τ₁ = µ(σ + 1/φ)/(1 + µ + µ/φ)` (`rm_ramsey_taxes`),
  the sign of the tax and of `µ` (`rm_tax_pos`, `rm_mu_pos`); time inconsistency
  (`tc_saves`, `tc_household_line`, `tc_time_inconsistent`).
* **OLG** (§15.6): the budget in ratios (`olg_budget_ratio`), (15.21)–(15.22) (`eq_15_21`,
  `eq_15_22`), PAYG as implicit debt (`olg_payg_eq_debt`), the PV derivative
  (`olg_pv_increasing_iff`), the Pareto improvement (`olg_payg_pareto`), the tax holiday
  (`olg_holiday_taxes`, `olg_holiday_aggregate`).
* **Progressivity** (§15.7, App. 15.A.2): (15.25)–(15.27) (`eq_15_25`, `hsv_hours_optimal`,
  `eq_15_26`, `eq_15_27`), hours falling in `τ` (`hsv_hours_strictAntiOn`, `hsv_hours_tendsto`),
  `Var log c = (1 − τ)²Var log w` (`hsv_var_log_c`), and `ℓ = 1` with wealth effects
  (`app_15_A_2`).

All names are in the namespace `AKMM.FiscalPolicy`. The project imports
[MonetaryEconomics/Cochrane/FiscalConstraints](https://github.com/LeanEconomics/MonetaryEconomics)
(the discrete debt-to-GDP equation, `debt_gdp_discrete`) and
[InternationalEconomics/LifeCycleFiscalPolicy](https://github.com/LeanEconomics/InternationalEconomics)
(Obstfeld–Rogoff's two-period Ricardian neutrality, `two_period_budgetSet_eq_of_pv_eq`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DebtDynamics](AKMMFiscalPolicy/DebtDynamics.lean) | 12 | (15.1)–(15.2), the debt-to-GDP ratio and its stable value (AKMM §15.2, pp. 441–444) |
| [DistortionaryTaxes](AKMMFiscalPolicy/DistortionaryTaxes.lean) | 12 | Definition 15.1, (15.3)–(15.7) (AKMM §15.3, pp. 446–447) |
| [LongRun](AKMMFiscalPolicy/LongRun.lean) | 16 | (15.8)–(15.12), GHH (AKMM §15.3.1, pp. 447–448) |
| [Incidence](AKMMFiscalPolicy/Incidence.lean) | 10 | Worker–capitalist equivalence, (15.13), `c_w`, `c_k` (AKMM §15.3.2, p. 449) |
| [ExcessCost](AKMMFiscalPolicy/ExcessCost.lean) | 15 | (15.14), flow utility, the excess cost of taxation, tax-reform steady states (AKMM §15.3.2–15.3.3, pp. 450–451) |
| [Laffer](AKMMFiscalPolicy/Laffer.lean) | 13 | The Laffer curve, footnote 6 (AKMM §15.3.4, pp. 453–454) |
| [TheoriesOfG](AKMMFiscalPolicy/TheoriesOfG.lean) | 5 | Public goods and public capital (AKMM §15.3.5, pp. 454–455) |
| [Ricardian](AKMMFiscalPolicy/Ricardian.lean) | 7 | Two-period Ricardian equivalence (AKMM §15.4, pp. 455–456) |
| [Ramsey](AKMMFiscalPolicy/Ramsey.lean) | 14 | The primal approach, (15.15)–(15.18), Ramsey taxes (AKMM §15.5–15.5.1, pp. 456–461) |
| [TimeConsistency](AKMMFiscalPolicy/TimeConsistency.lean) | 7 | Time inconsistency of the Ramsey plan (AKMM §15.5.2, pp. 461–462) |
| [OLGPensions](AKMMFiscalPolicy/OLGPensions.lean) | 14 | (15.19)–(15.24), PAYG as debt, the tax holiday (AKMM §15.6, pp. 462–463) |
| [Progressivity](AKMMFiscalPolicy/Progressivity.lean) | 11 | (15.25)–(15.27), App. 15.A.2 (AKMM §15.7, pp. 464–466; p. 869) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
