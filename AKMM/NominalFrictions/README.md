# AKMM Chapter 18: Nominal frictions and business cycles, in Lean

This is the `AKMM/NominalFrictions` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 18 (Nominal frictions and business cycles, by Alisdair McKay and Morten Ravn) of Marina
Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), pp. 533–560, with Appendix 18.A (pp. 871–876), cited by the draft's pages. Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 18 reviews the micro evidence on price rigidity, builds the basic New Keynesian model
with Calvo pricing (preferences, CES demand, household and firm problems, aggregation and price
dispersion, natural output, the three-equation model and determinacy), studies monetary policy
(efficiency and the subsidy, the quadratic loss, the divine coincidence, cost-push shocks,
inflation and price-level targeting, commitment versus discretion), reviews the aggregate
evidence (policy shocks, Galí–Gertler estimation of the Phillips curve), and extends the model
with sticky wages, habits and capital; Appendix 18.A derives the Phillips curve, the Taylor
principle by the Jury criterion and the sticky-wage model. Every derivation the text carries out
is proved in the book's setting, importing Galí's and Miao's New Keynesian projects where they
match the book's model. Not formalised: data, figures, simulations, estimated models (CEE,
Smets–Wouters, Galí–Gertler estimates) and narrative. Nine printed errors are corrected, among
them the expected duration of a price (`1/(1 − θ)`, not `θ/(1 − θ)`), the exponents of the
reset-price recursions (18.7) (`ε` and `ε − 1`, not `1 + ε` and `ε`), the sign of the natural
rate below (18.15), the missing intercept of (18.17), the claim that `|a₀| < 1` is automatic,
the real wage with sticky wages only, and Tobin's `Q = 1` (which needs `ξ′(δ) = 1`), as recorded
in [corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **142 theorems**.

* **Price durations** (§18.2): the printed weights sum to `θ`; the mean duration is `1/(1 − θ)`
  (`dur_printed_weights_sum`, `dur_mean`, `dur_printed_eq_mean_sub_one`).
* **Environment and households** (§18.3): CES demand and the price index (`env_ces`,
  `env_cost_deriv`), marginal cost and profits (`env_marginal_cost`, `env_profit`), the real budget
  constraint, (18.5) and (18.6) as first-order conditions (`eq_18_5`, `eq_18_5_stochastic`,
  `eq_18_6`).
* **The reset price** (§18.3, App. 18.A.1): the envelope condition iterated (`rp_iterate`,
  `rp_series`, `rp_series_envelope`), the rearranged condition and the corrected (18.7)
  (`rp_foc_rearranged`, `eq_18_7`, `rp_pN_rec`, `rp_pD_rec`, `rp_printed_ne_iff`).
* **Aggregation** (§18.3): (18.9)–(18.12), `D ≥ 1` (`eq_18_9`, `eq_18_10`, `eq_18_11`, `eq_18_12`,
  `agg_dispersion_ge_one`, `agg_dispersion_eq_one_iff`).
* **Natural output and rules**: the markup (`nat_markup_foc`, `nat_markup_max`), (18.13)
  (`eq_18_13`), the gap and the intercept (`nat_gap_loglinear`, `nat_rule_intercept`,
  `nat_quarterly_rule`).
* **The three-equation model**: the IS curve with the corrected `r^n` (`eq_18_15_exact`,
  `eq_18_15`, `rn_printed_iff`), the Phillips curve via (18.A.2)–(18.A.6) (`eq_18_A_2`,
  `reset_recursion_instance`, `eq_18_A_3`, `eq_18_A_4`, `eq_18_A_dispersion`, `eq_18_A_5_exact`, `eq_18_16`), `κ`
  (`nk_kappa_pos`, `nk_kappa_antitone`).
* **Determinacy** (18.18), App. 18.A.2: the system, inverse and coefficients (`det_system`,
  `det_inverse`, `det_coeff_eq_AT`, `det_a1`, `det_a0`), Jury (`det_jury_iff`, `det_roots_iff`),
  uniqueness (`eq_18_18`), the Taylor principle (`det_taylor_sufficient`, `det_taylor_necessary`).
* **Policy objectives** (§18.4.1): (18.19) and the output decompositions (`eq_18_19`,
  `eff_output_wage`, `eff_output_dispersion`, `eff_natural_lt`), `x^w` (`eff_welfare_gap`), the
  subsidy (`eff_subsidy`), (18.20) (`eq_18_20_utility`, `eq_18_20_weight`, `eq_18_20_period`).
* **Strategies** (§18.4.2–18.4.4): divine coincidence and cost-push (`pol_divine_coincidence`,
  `pol_costpush_breaks`), price-level targeting (`pol_price_level_rule`), discretion and
  commitment (`pol_discretion_date0`, `pol_commitment_path`, `pol_commitment_date0`,
  `pol_commitment_price_level`, `pol_commitment_better`, `pol_time_inconsistent`).
* **Estimation** (§18.5.2): instrument validity by iterated expectations (`gg_orthogonal`,
  `gg_cov_zero`) and `mc = s_L/α_L` (`gg_marginal_cost`, `gg_log_mc`).
* **Sticky wages** (§18.6.1, App. 18.A.3): labour aggregation and wage dispersion
  (`sw_labour_ces`, `sw_wage_dispersion_ge_one`), the union's condition (`sw_union_foc`), the
  wage and price Phillips curves and the identity (`sw_wage_pc`, `eq_18_24`, `eq_18_23`,
  `eq_18_25`), the sticky-wage-only real wage (`sw_flexprice_real_wage`).
* **Extensions** (§18.6.2): habits (`ext_habit`), Tobin's `Q` (`ext_tobin_q`, `ext_q_one_iff`,
  `ext_q_counterexample`), labour with capital (`ext_labour_elasticity`,
  `ext_units_printed_false`).

All names are in the namespace `AKMM.NominalFrictions`. The project imports Galí's
[MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics) projects
`Gali/BasicNewKeynesianModel` (CES demand, durations, dispersion, Schur–Cohn, Bullard–Mitra),
`Gali/MonetaryPolicyDesign` (welfare approximation, divine coincidence, Exercise 4.6),
`Gali/DiscretionCommitment` (loss weights, commitment and discretion) and `Gali/StickyWagesPrices`
(the wage Phillips curve), and [EconomicDynamics/NewKeynesian](../../EconomicDynamics/NewKeynesian/README.md)
(Miao Chapter 19: `eq_19_3`, `eq_19_13`, `eq_19_17`, `nk_hasDerivAt_pow_div`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Duration](AKMMNominalFrictions/Duration.lean) | 7 | The expected time between price changes (AKMM §18.2, p. 534) |
| [Environment](AKMMNominalFrictions/Environment.lean) | 12 | (18.1)–(18.6): CES demand, the budget constraint, household conditions (AKMM pp. 536–539) |
| [ResetPrice](AKMMNominalFrictions/ResetPrice.lean) | 18 | The firm's Bellman equation, the reset-price condition and (18.7) (AKMM pp. 539–540, 871) |
| [Aggregation](AKMMNominalFrictions/Aggregation.lean) | 9 | (18.9)–(18.12): Calvo index, inflation, dispersion (AKMM pp. 540–541) |
| [NaturalOutput](AKMMNominalFrictions/NaturalOutput.lean) | 10 | The markup, (18.13), (18.14), the rule intercept (AKMM pp. 542–543) |
| [Efficiency](AKMMNominalFrictions/Efficiency.lean) | 15 | (18.19), the decompositions, the subsidy, (18.20) (AKMM §18.4.1, pp. 545–547) |
| [ThreeEquation](AKMMNominalFrictions/ThreeEquation.lean) | 17 | (18.15)–(18.17) and (18.A.1)–(18.A.6) (AKMM pp. 543–544, 871–872) |
| [Determinacy](AKMMNominalFrictions/Determinacy.lean) | 11 | (18.18) by the Jury criterion (AKMM p. 544, App. 18.A.2, p. 873) |
| [Policy](AKMMNominalFrictions/Policy.lean) | 14 | Divine coincidence, cost-push, targeting, commitment vs discretion (AKMM §18.4.2–18.4.4) |
| [Estimation](AKMMNominalFrictions/Estimation.lean) | 8 | Galí–Gertler instruments and marginal cost (AKMM §18.5.2, pp. 553–554) |
| [StickyWages](AKMMNominalFrictions/StickyWages.lean) | 11 | (18.23)–(18.25) and App. 18.A.3 (AKMM pp. 556–558, 873–876) |
| [Extensions](AKMMNominalFrictions/Extensions.lean) | 10 | Habits, adjustment costs, capital (AKMM §18.6.2, pp. 558–560) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
