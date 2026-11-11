# AKMM Chapter 6: Welfare, in Lean

This is the `AKMM/Welfare` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 6 and Appendix 6.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 6 proves the First Welfare Theorem in an abstract economy, maps it to dynastic and
overlapping-generations economies, traces out the Pareto frontier with Negishi weights, studies
the classic inefficiencies (distortionary taxes, an externality, a borrowing constraint, market
power), measures welfare losses, and asks when overlapping-generations equilibria, with or without
production, are efficient; Appendix 6.A proves that a steady state is efficient iff the gross
return is at least one. Every numbered result and derivation of the text is proved: Theorem 6.1;
Theorem 6.2, the Cass criterion, which the book cites without proof, in full under the
assumptions of its fn. 12; Theorem .5; (6.2)–(6.6). The Balasko–Shell theorem, also cited without
proof, is proved for the stationary log economy the book uses (with the finite-value welfare
theorem for any economy); the general statement is not formalised. Seven printed errors are
corrected, with Lean counterexamples to Theorem 6.1 without nonnegative prices, the borrowing
constraint, "optimal iff the limit net rate is `≥ 0`", the storage bond price, the appendix's
`f` and the two warm-glow steady states, as recorded in [corrections](docs/corrections.md); every
book item is located in the [source map](docs/source-map.md). The project depends on AKMM
`CompetitiveEquilibrium` (the date-0 problem and the OG equilibrium of Chapter 5) and Miao
`OverlappingGenerations` (concave tangents, the steady-state Cass sum). The library contains
**110 theorems**, all new.

* **The First Welfare Theorem** (§6.1): Theorem 6.1 with preference relations, endowments and
  shares (`theorem_6_1`), false without `p ≥ 0` (`theorem_6_1_counterexample`); lump-sum taxes
  (`fwt_lump_sum`); infinitely many goods with finite values (`fwt_dynastic`).
* **The Pareto frontier** (§6.2): (6.2) and (6.3) (`eq_6_2`, `eq_6_3`), the planner's first-order
  condition (`dy_planner_foc`), `ψₜ = pₜ` (`negishi_psi_eq_p`), the equilibrium solves the planner
  with weights `1/λᵢ` (`negishi_ce_solves_planner`, `negishi_fwt`).
* **Inefficiencies** (§6.3): the labour-tax wedge (`tax_inelastic_labour`, `tax_labour_wedge`);
  equilibrium and planner hours under a TFP externality (`ext_equilibrium_hours`,
  `ext_planner_hours`, `ext_overwork`); the borrowing-constrained equilibria are autarky with
  `qₜ ≥ 2β` (`borrow_equilibrium_iff`) and are Pareto dominated (`borrow_autarky_not_optimal`);
  Dixit–Stiglitz price index, demand, markup and under-production (`ds_price_index`, `ds_demand`,
  `ds_firm_optimum`, `ds_underproduction`).
* **Welfare measures and policy** (§§6.3.6, 6.5): consumption equivalents
  (`welfare_cev_static`, `welfare_cev_dynamic_log`) and the veil of ignorance
  (`veil_optimum_equal`).
* **OG endowment economies** (§6.4.1): (6.5)–(6.6) and uniqueness (`eq_6_5_6_6`,
  `og_log_equilibrium_iff`); the welfare theorem when `pₜω_{y,t} → 0` (`og_fwt_value`); the
  `(3, 1)`, `(1, 3)`, `(2, 2)` examples; Balasko–Shell for the stationary log economy
  (`og_balasko_shell_stationary_log`); the limit-rate criterion corrected
  (`og_limit_rate_one_counterexample`, `og_limit_rate_gt_one`, `og_limit_rate_lt_one_log`).
* **Production and dynamic efficiency** (§6.4.2, App. 6.A): storage is efficient iff `χ > 1`
  (`storage_optimal_iff`); **Theorem 6.2** (`theorem_6_2`); **Theorem .5** (`theorem_A5`).
* **Warm glow** (§6.4.3): two steady states, the upper one stable and dynamically inefficient
  (`warmglow_two_steady_states`, `warmglow_stable`, `warmglow_inefficient`).

All names are in the namespace `AKMM.Welfare`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [FirstWelfare](AKMMWelfare/FirstWelfare.lean) | 10 | Theorem 6.1, lump-sum and labour taxes (AKMM §§6.1, 6.3.1, pp. 160–168) |
| [Dynastic](AKMMWelfare/Dynastic.lean) | 11 | Infinite-horizon FWT, (6.2)–(6.3), Negishi weights (AKMM §§6.1–6.2, pp. 162–167) |
| [Externality](AKMMWelfare/Externality.lean) | 6 | A TFP externality (AKMM §6.3.2, pp. 168–169) |
| [Borrowing](AKMMWelfare/Borrowing.lean) | 13 | Borrowing constraints and autarky (AKMM §6.3.3, pp. 170–171) |
| [MarketPower](AKMMWelfare/MarketPower.lean) | 16 | Monopolistic competition, (6.4) (AKMM §6.3.5, pp. 172–175) |
| [WelfareMeasures](AKMMWelfare/WelfareMeasures.lean) | 4 | Consumption equivalents, the veil of ignorance (AKMM §§6.3.6, 6.5.2, pp. 175–186) |
| [OGEndowment](AKMMWelfare/OGEndowment.lean) | 20 | (6.5)–(6.6), OG welfare, stationary Balasko–Shell (AKMM §6.4.1, pp. 176–180) |
| [OGProduction](AKMMWelfare/OGProduction.lean) | 19 | Storage, Theorem 6.2, Theorem .5 (AKMM §6.4.2, App. 6.A, pp. 180–183, 838–839) |
| [WarmGlow](AKMMWelfare/WarmGlow.lean) | 11 | Dynamic inefficiency with warm glow (AKMM §6.4.3, p. 183) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
