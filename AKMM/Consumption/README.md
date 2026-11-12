# AKMM Chapter 11: Consumption, in Lean

This is the `AKMM/Consumption` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 11 (Consumption, by G. L. Violante) of Marina Azzimonti, Per Krusell, Alisdair McKay and
Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 287–323, cited by the draft's
pages. Run the commands below from this directory. [Return to the library index](../../README.md).

Chapter 11 moves from complete-markets risk sharing to the income fluctuation problem — the
deterministic case, the permanent income hypothesis, borrowing constraints and precautionary saving
— and then to Huggett's and Aiyagari's stationary equilibria. Every numbered equation the chapter
derives and every precise claim is proved, mostly in the book's own setting: the PIH runs on Miao's
abstract conditional expectations, mean-preserving spreads are the convex order, and the equilibrium
material reuses Miao's Chapter 17 and Stokey–Lucas–Prescott's Theorem 12.13. Not formalised: the
empirical material, the numerical figures, the claims read off Figures 11.2, 11.4, 11.5, 11.7 and
11.9 (deferred), and results the book only cites, among them the ACHLLM continuous-time uniqueness
theorem. Seven printed errors are corrected (and three minor slips recorded), with Lean
counterexamples to the log-utility MPC, the HARA sign of `κ`, the capital-income-risk claim, the
coefficient of (11.41), the DARA condition for bounded wealth and footnote 27, as recorded in
[corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **139 theorems**.

* **Risk sharing** (§11.2): autarky (11.1) and fn. 1 (`eq_11_1`, `footnote_1`); (11.3) from the
  Arrow–Debreu equilibrium of AKMM Chapter 7 (`eq_11_3`); CRRA shares (11.4) and history-independent
  shares of the aggregate (`eq_11_4`, `rs_crra_share_eqm`); the single crossing (11.5) and the less
  risk-averse household absorbing aggregate risk (`eq_11_5`, `rs_less_risk_averse_absorbs`).
* **The bond economy and the deterministic problem** (§11.2.3, §11.3.1): (11.10)–(11.11); the
  Euler equation (11.13) from optimality and its sufficiency, with a concrete log optimum
  (`eq_11_13`, `cd_optimal_of_euler`, `cd_log_optimal`); (11.14)–(11.16) (`eq_11_15`,
  `cd_optimal_eq_11_15`, `eq_11_16`); MPCs out of transitory and permanent income
  (`cd_mpc_betaR_one`, `cd_mpc_permanent`); the log-utility MPC is `1 − β`, not `≃ r`
  (`cd_mpc_log`, `cd_mpc_log_printed_counterexample`).
* **The PIH** (§11.3.2): Hall's martingale (11.18)–(11.19), the annuity rule (11.20), the
  deterministic case and certainty equivalence (`eq_11_18`, `eq_11_19`, `eq_11_20`, `eq_11_21`,
  `pih_certainty_equivalence`); news (11.22)–(11.24); permanent and transitory shocks (11.27)
  (`eq_11_27`); Blundell–Preston (11.28), exact at `r = 0` (`eq_11_28`); saving for a rainy day
  (`pih_rainy_day`).
* **Borrowing constraints** (§11.3.3): random-walk and i.i.d. income (11.30) (`pih_random_walk`,
  `eq_11_30`), hitting the limit (`bc_iid_hits`), (11.32), the natural borrowing limit
  (`bc_natural_limit`, `bc_natural_limit_cons_nonpos`), (11.33)–(11.34) (`eq_11_33`,
  `eq_11_34_spread`).
* **Prudence** (§11.3.4): (11.35) and precautionary saving under a convex-order spread
  (`eq_11_35_unique`, `pr_spread_raises_saving`, `pr_two_point_iff`); DARA ⇒ prudence
  (`pr_dara_prudent`); Blanchard–Mankiw (11.36), exact for quadratic `u′` (`eq_11_36_exact`);
  (11.38)–(11.40) (`eq_11_38`, `eq_11_39`, `eq_11_40`); HARA and fn. 19 (`pr_hara_kappa_const`,
  `pr_kappa_crra`), with `κ < 0` possible (`pr_hara_kappa_neg`).
* **Capital income risk and the lognormal Euler equation**: return risk raises saving iff
  relative prudence is at least 2 (`cr_second_deriv_nonneg_iff`, `cr_spread_raises_saving`), not
  under prudence alone (`cr_printed_counterexample`); (11.41) with coefficient `σ/2`
  (`eq_11_41`, `eq_11_41_printed_false`, `cs_zeldes_euler`).
* **Bounded wealth** (§11.3.5): the book's argument given (11.44) (`bw_bounded_of_ratio`), the
  theorem from Miao's Lemma 8.3.3 (`bw_bounded_wealth`, `bw_bounded_wealth_crra`), and DARA does
  not give `α → 0` (`bw_dara_not_ara_zero`).
* **Huggett and Bewley** (§11.4.1): the stationary equilibrium and Walras's law
  (`hg_IsStationaryEqm`, `hg_goods_clear_zero_supply`, `hg_eqm_iff_miao`, concrete instances
  `hg_cycle_eqm`, `hg_cycle_huggett`); continuity of `A(r)` from SLP Theorem 12.13
  (`hg_A_continuous`); `A(−1) = −a` (`hg_A_at_minus_one`); existence (`hg_existence`,
  `hg_existence_eqm`); `r* < 1/β − 1` (`hg_rate_below_cm`); (11.50) (`eq_11_50`); saving rises with
  `r` iff `σ < 1` (`hg_saving_increasing_iff`).
* **Aiyagari** (§11.4.2): footnote 27 corrected (`footnote_27`, `footnote_27_printed_false`),
  `K(r)` (`ai_capital_demand_props`, `ai_Kd_tendsto_zero`), existence (`ai_existence`),
  precautionary wealth `K* > K^{CM}` (`ai_precautionary_wealth`), the representative-agent MPC
  (`ai_mpc_representative`).

All names are in the namespace `AKMM.Consumption`. The project depends on AKMM Chapter 7
(`AKMMUncertainty`: the Arrow–Debreu equilibrium and its first-order conditions) and AKMM
Chapter 5 (`AKMMCompetitiveEquilibrium`: the finite-perturbation lemma), Miao's `CompleteMarkets` (the event tree),
`RationalExpectations` (conditional expectations) and `IncompleteMarkets` (Chapters 8 and 17: the
income fluctuation problem, the Huggett and Aiyagari economies), and Stokey–Lucas–Prescott's
`WeakConvergence` (Theorem 12.13).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [RiskSharing](AKMMConsumption/RiskSharing.lean) | 10 | (11.1)–(11.5), fn. 1: autarky, complete-markets risk sharing, heterogeneous risk aversion (AKMM §11.2, pp. 288–290) |
| [Deterministic](AKMMConsumption/Deterministic.lean) | 23 | (11.10)–(11.16), fn. 12–15: the bond economy, the deterministic problem, the MPC (AKMM §11.2.3–11.3.1, pp. 294–298) |
| [PIH](AKMMConsumption/PIH.lean) | 20 | (11.18)–(11.30): Hall, the annuity rule, news, permanent/transitory shocks, rainy days (AKMM §11.3.2–11.3.3, pp. 297–302) |
| [BlundellPreston](AKMMConsumption/BlundellPreston.lean) | 5 | (11.28): consumption and income inequality (AKMM p. 300) |
| [BorrowingConstraints](AKMMConsumption/BorrowingConstraints.lean) | 10 | (11.32)–(11.33), the natural borrowing limit (AKMM §11.3.3–11.3.4, pp. 302–305) |
| [Prudence](AKMMConsumption/Prudence.lean) | 22 | (11.34)–(11.40), fn. 17–19: convex order, prudence, DARA, Blanchard–Mankiw, concavity, HARA (AKMM §11.3.4, pp. 304–309) |
| [CapitalRisk](AKMMConsumption/CapitalRisk.lean) | 8 | Capital income risk, corrected (AKMM pp. 309–310) |
| [Lognormal](AKMMConsumption/Lognormal.lean) | 4 | (11.41) and the Zeldes equation, corrected (AKMM pp. 310–311) |
| [BoundedWealth](AKMMConsumption/BoundedWealth.lean) | 8 | (11.42)–(11.46): bounds on wealth accumulation (AKMM §11.3.5, pp. 312–314) |
| [Huggett](AKMMConsumption/Huggett.lean) | 20 | (11.47)–(11.50): stationary equilibrium, existence, `r* < 1/β − 1`, positive supply (AKMM §11.4.1, pp. 315–320) |
| [AssetDemandContinuity](AKMMConsumption/AssetDemandContinuity.lean) | 2 | Continuity of `A(r)` from SLP Theorem 12.13 (AKMM p. 317) |
| [Aiyagari](AKMMConsumption/Aiyagari.lean) | 7 | The production economy, fn. 27, precautionary wealth, the MPC box (AKMM §11.4.2, pp. 320–323) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
