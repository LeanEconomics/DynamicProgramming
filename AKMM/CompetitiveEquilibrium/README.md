# AKMM Chapter 5: Dynamic Competitive Equilibrium, in Lean

This is the `AKMM/CompetitiveEquilibrium` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 5 and Appendix 5.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 5 defines competitive equilibrium three ways — Arrow–Debreu, sequential and recursive —
for an endowment economy, a labour economy and the neoclassical growth model with a continuum of
consumers, and then for two-period overlapping-generations economies; Appendix 5.A shows that
power utility gives policies linear in individual wealth. Every numbered equation and every
derivation of the text is proved, and every numbered definition is formalised (Definitions 6 and 9
through the conditions the text uses): first-order conditions are derived from optimality by
finite perturbations and shown sufficient under concavity; equilibria are constructed where the
text solves for them (the log endowment and labour economies, the steady states, the closed form
of Appendix 5.A, the log/Cobb–Douglas OG economy). Not formalised: narrative, the HARA remark and
the claims the book asserts without derivation (the weighted planner of fn. 8, non-aggregation
with valued leisure, the perpetual-youth and warm-glow discussions). The project depends on SLP's
`EquilibriumApplications` (the CRRA family and its tangent inequality) and Miao's
`OverlappingGenerations` (convergence of `k_{t+1} = ck_t^α`). Eight printed errors are corrected,
with Lean counterexamples to the steady-state condition `β = 1 − δ + r`, the static labour
first-order condition, the OG steady-state interest rate, the aggregate Euler equation, the
attribution of Appendix 5.A's two equations, Definition 11's "`t > 0`" and the iterated sequential
budget, as recorded in [corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **116 theorems**, all new.

* **The date-0 consumer** (§5.2.1): necessity of `βᵗu′(cₜ) = λpₜ` by perturbation and (5.3)
  (`ce_foc_of_perturb`, `ad_foc`, `ad_foc_multiplier`, `eq_5_3`), sufficiency
  (`ad_foc_sufficient`).
* **The endowment economy** (§5.2.1): Definitions 1–2; log prices, identical growth, perfect
  smoothing, shares `θᵢ` (`endow_log_price`, `endow_log_growth`, `endow_log_smoothing`,
  `endow_log_shares`); existence and uniqueness (`endow_log_existence`); CRRA prices
  `pₜ = βᵗ(Y₀/Yₜ)^σ` (`endow_crra_price`); Definition 2 as a special case
  (`definition_2_of_identical`).
* **The labour economy** (§5.2.2): the firm (`eq_5_6_static`, `labour_firm_fn3`,
  `labour_wage_eq_productivity`); (5.8)–(5.10) (`eq_5_8`, `eq_5_9`, `eq_5_10`); `θᵢ = eᵢ` and equal
  hours (`labour_log_equilibrium`); the static examples, corrected
  (`labour_static_asset_foc`, `labour_static_asset_printed_counterexample`).
* **The growth economy** (§5.2.3): the Cobb–Douglas firm (`growth_firm_foc`,
  `growth_firm_optimal`); (5.15)–(5.17) (`eq_5_15`, `eq_5_16`, `eq_5_17`); the consolidated budget
  and its limit condition (`growth_consolidated_budget`, `growth_foc_sufficient`); `θᵢ = eᵢ`
  (`growth_log_consumption`, `growth_fn6`); (5.18)–(5.20) and fn. 7 (`eq_5_18`, `eq_5_19`,
  `eq_5_20`, `growth_fn7`); the planner's conditions (`growth_planner_foc_K`,
  `growth_planner_foc_L`).
* **Sequential equilibrium** (§5.3): Walras's law (`seq_walras`); (5.21)–(5.22) and the price
  product (`eq_5_21_5_22`, `seq_price_product`); the budgets, corrected (`seq_budget_iterate`,
  `seq_budget_iterate_printed_counterexample`, `seq_lifetime_budget`,
  `seq_lifetime_budget_eq_iff`, `seq_of_lifetime_budget`); equivalence with Arrow–Debreu
  (`seq_optimal_iff_ad`, `seq_equilibrium_is_ad`); Euler's theorem and Walras's law in the growth
  economy (`euler_crs`, `seq_growth_walras`).
* **Steady states** (§5.4.1): `q = β` and `β(1 − δ + r) = 1` from the Bellman equation
  (`ss_rate`, `definition_7_q_eq_beta`, `definition_8_rate`, with
  `definition_8_printed_counterexample`); the value functions and the indeterminate distributions
  (`ss_value`, `definition_7_any_distribution`, `definition_8_any_distribution`).
* **Recursive equilibrium and Appendix 5.A** (§5.4.2): the resource constraint and the aggregate
  Euler equation, corrected (`definition_9_resource`, `definition_9_aggregate_euler`,
  `definition_9_aggregate_euler_printed`); linear policies under power utility
  (`appendix_5A_power`, `appendix_5A_split`, `appendix_5A_mu_lambda`, `aggregation_linear`); the
  closed form `g(k, K) = βr(K)k` (`appendix_5A_closed_form`); Definition 10
  (`definition_10_planner`).
* **Overlapping generations** (§5.5): autarky and (5.24) (`og_autarky`, `eq_5_24`,
  `og_autarky_equilibrium`, `og_negative_rate_example`); Definition 11 corrected
  (`definition_11_printed_counterexample`); the Diamond-type economy and the exercise, corrected
  (`og_growth_euler`, `og_growth_log_equilibrium`, `og_growth_log_convergence`,
  `og_growth_log_rate`, `og_growth_log_rate_printed_counterexample`); the dynastic and altruistic
  long-run rates (`og_dynastic_long_run_rate`, `og_altruism_rate`).

All names are in the namespace `AKMM.CompetitiveEquilibrium`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ADConsumer](AKMMCompetitiveEquilibrium/ADConsumer.lean) | 8 | The date-0 consumer problem, (5.2)–(5.3), perturbation tools (AKMM §5.2.1, pp. 132–133) |
| [EndowmentAD](AKMMCompetitiveEquilibrium/EndowmentAD.lean) | 13 | Definitions 1–2, log and CRRA endowment economies (AKMM §5.2.1, pp. 132–135) |
| [LabourAD](AKMMCompetitiveEquilibrium/LabourAD.lean) | 16 | Definition 3, (5.4)–(5.10), the static examples (AKMM §5.2.2, pp. 135–138) |
| [GrowthAD](AKMMCompetitiveEquilibrium/GrowthAD.lean) | 21 | Definition 4, (5.11)–(5.20), fns. 5–7, the planner (AKMM §5.2.3, pp. 139–142) |
| [Sequential](AKMMCompetitiveEquilibrium/Sequential.lean) | 16 | Definitions 5–6, (5.21)–(5.22), budgets, Walras's law, equivalence (AKMM §5.3, pp. 143–146) |
| [SteadyState](AKMMCompetitiveEquilibrium/SteadyState.lean) | 10 | Definitions 7–8, recursive steady states (AKMM §5.4.1, pp. 147–149) |
| [RecursiveEquilibrium](AKMMCompetitiveEquilibrium/RecursiveEquilibrium.lean) | 13 | Definitions 9–10, aggregation, Appendix 5.A (AKMM §5.4.2, pp. 149–152, 836–837) |
| [OGEconomies](AKMMCompetitiveEquilibrium/OGEconomies.lean) | 19 | Definitions 11–12, (5.24), the OG exercise, model comparisons (AKMM §5.5, pp. 152–157) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
