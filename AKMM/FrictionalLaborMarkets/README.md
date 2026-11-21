# AKMM Chapter 20: Frictional Labor Markets, in Lean

This is the `AKMM/FrictionalLaborMarkets` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 20 (Frictional labor markets, by T. Mukoyama and A. Şahin) of Marina Azzimonti, Per Krusell,
Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 593–625,
with Appendix 20.A, pp. 879–887. Pages are cited by the draft's running heads. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 20 studies unemployment arising from search frictions:
- the lake model of unemployment;
- the Diamond–Mortensen–Pissarides model: matching, the Beveridge curve, Nash bargaining, job
  creation, the steady state and its instability, and efficiency (the Hosios condition);
- the log-linearised solution, the unemployment volatility puzzle and rigid wages;
- endogenous separations;
- the DMP model inside the neoclassical growth model, with Arrow-security prices;
- the McCall search model, mean-preserving spreads, frictional wage dispersion and the Diamond
  paradox.

Every numbered equation the chapter and its appendix derive and every precise claim are proved in
the book's setting. All proofs are analytic.

Thirteen printed errors are corrected, among them:
- the sign of `B` in (20.25);
- the leading `β` of the planner's condition (20.A.2)–(20.A.3);
- the formulas for `κ` and `K̄` in 20.A.8;
- the argument order of (20.6);
- `w̃ = max{w̄, y}` (it must be `min`);
- the value `Mm = 1.031` (the formula gives about `1.049`);
- the characterisation (20.56) of mean-preserving spreads, which needs equal means;
- the comparative statics in `η`, which need `θ̄^ηη` increasing in `η`.

Added hypotheses: continuity and limit conditions for the existence of `ū` and `θ̄`; footnote 6's
condition on an interval containing the path; `Γ ≠ 0` for `G = Θ/Γ`; no atom of the offer
distribution at `w*` for Leibniz's rule. The book's bounds `M ≤ u, v` are inconsistent with
Cobb–Douglas matching and are kept separate. The Hosios condition is proved at the level of
first-order conditions, as in the book (the planner's problem is not convex).

Not formalised:
- the data, figures, calibrations and simulations (Tables 20.1–20.10, Figures 20.1–20.10);
- the family's dynamic programs (20.33), (20.46) and the functional fixed point of §20.8 (the
  book computes it and does not claim existence);
- the converse of (20.56) with equal means (Rothschild–Stiglitz, cited).

The corrections are recorded in [corrections](docs/corrections.md), and every book item is
located in the [source map](docs/source-map.md). The library contains **187 theorems**.

* **The lake model** (§20.3): the unique steady state (20.2) (`eq_20_2`), global stability via
  Sargent–Stachurski's contractions (`lake_globallyStable`, `lake_tendsto`), the expected
  duration `1/λ` as a series and as a fixed point (`lake_duration_series`,
  `lake_duration_recursion`).
* **Matching** (§20.4.1):
  - matching functions (`MatchFn`), `λ_w = θλ_f` (`eq_20_3`, `match_lamW_eq`), monotonicity;
  - the Beveridge curve: unique `ū`, existence, downward slope (`eq_20_5`, `eq_20_6`,
    `match_ubar_unique`, `match_ubar_exists`, `match_beveridge_anti`);
  - Euler's theorem and the elasticity (`match_euler`, `match_elast_eq`); Cobb–Douglas
    (`eq_20_23`, `cd_not_bounded`).
* **Equilibrium** (§20.4.2):
  - Nash bargaining (`eq_20_15`, `eq_20_A_1`), the job-creation equation (`eq_20_16`) and the wage
    (`eq_20_A_2`);
  - the steady state: uniqueness, existence, comparative statics (`eq_20_17`, `ss_unique`,
    `ss_exists`, `ss_cd_existsUnique`, `ss_theta_mono_z`);
  - footnotes 6–7: monotone, explosive dynamics and the immediate jump (`fn6_rhs_strictMonoOn`,
    `fn7_slope_gt_one`, `fn7_diverge_above`, `fn7_jump`).
* **Efficiency** (§20.4.3, 20.A.3): (20.18)–(20.22) (`eq_20_18`, `eq_20_19`, `eq_20_20`,
  `eq_20_22`); the planner's conditions (`planner_foc_theta`, `planner_foc_u`, `eq_20_A_3`);
  the Hosios condition (`hosios`, `hosios_node`) and its failure without constant returns
  (`hosios_nonCRS`).
* **Log-linearisation** (§20.6): (20.25)–(20.27) as exact derivatives (`eq_20_25`, `eq_20_26`,
  `eq_20_27`); the comparative statics of the response (`ll_cs_kappa` … `ll_cs_sigma`); rigid
  wages amplify (`ll_rigid_gt`).
* **Endogenous separations** (§20.7): (20.28)–(20.32) (`eq_20_28`, `eq_20_29`, `eq_20_31`,
  `eq_20_32`), `G = Θ/Γ` (`eq_20_A_6`, `es_G`), the volatility ratio (`es_std_ratio`) and the exact
  cancellation under rigid wages (`es_rigid_cancel`, `es_rigid_G`).
* **The growth model** (§20.8): factor prices (`ngm_rental`, `ngm_y`), the Arrow-security price
  (`eq_20_36`, `ngm_arrow_foc`), asset values (`ngm_asset_value`), (20.42)–(20.45) and (20.48),
  and the calibration formulas of 20.A.8 (`ngm_calib_K`, `ngm_calib_kappa`).
* **McCall** (§20.9):
  - (20.50)–(20.55) via Miao's Exercise 8.2 (`eq_20_51`, `eq_20_53`, `mc_reservation`,
    `eq_20_55`);
  - comparative statics in `β`, `b`, `σ` and the partial derivatives (`mc_cs_beta`, `mc_cs_b`,
    `mc_cs_sigma`, `mc_G_partials`), Leibniz's rule (`mc_I_hasDerivAt`, `mc_G_w`);
  - a shift of all offers (`mc_shift_bounds`, `mc_shift_deriv`).
* **Dispersion** (§20.9): mean-preserving spreads (`mps_mean`, `mps_ibp`, `eq_20_56_of_mps`,
  `eq_20_56_not_sufficient`), (20.57)–(20.58) and the reservation wage under spreads
  (`mc_mps_reservation`), the mean–min ratio (`mm_formula_of_bellman`, `mm_back_of_envelope`).
* **The Diamond paradox** (§20.9): the unique Nash equilibrium wage is the reservation wage, for
  every search cost (`diamond_paradox`).

All names are in the namespace `AKMM.FrictionalLaborMarkets`. The project imports:
- [EconomicDynamics/SearchAndMatching](../../EconomicDynamics/SearchAndMatching/README.md)
  (Miao Ch. 18, discrete time: matching functions and Cobb–Douglas matching `dm_cdMatching`,
  Nash bargaining `jd_nash_iff`, affine recursions `jd_affine_sol`, `jd_affine_tendsto`);
- [EconomicDynamics/Applications](../../EconomicDynamics/Applications/README.md) (Miao Ch. 8:
  McCall search with job loss, Exercise 8.2, whose timing is the book's);
- [GeneralStates/AdditionalApplications](../../GeneralStates/AdditionalApplications/README.md)
  (Sargent–Stachurski Vol. 2 Ch. 8: `IsMPS`, `integral_max_le_of_isMPS`);
- [FiniteStates/OperatorsFixedPoints](../../FiniteStates/OperatorsFixedPoints/README.md)
  (Sargent–Stachurski Vol. 1 Ch. 2: `IsContractionOn`, `GloballyStable`; its lake model has
  positive entry and exit rates and is not the book's).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Lake](AKMMFrictionalLaborMarkets/Lake.lean) | 15 | §20.3: the lake model, convergence, expected duration |
| [Matching](AKMMFrictionalLaborMarkets/Matching.lean) | 25 | §20.4.1: matching functions, the Beveridge curve, Euler's theorem, Cobb–Douglas |
| [DMP](AKMMFrictionalLaborMarkets/DMP.lean) | 11 | §20.4.2–20.4.3: Nash bargaining, job creation (20.16), wages, (20.18)–(20.19) |
| [SteadyState](AKMMFrictionalLaborMarkets/SteadyState.lean) | 24 | §20.4.2: the steady state (20.17), footnotes 6–7 |
| [Efficiency](AKMMFrictionalLaborMarkets/Efficiency.lean) | 13 | §20.4.3, 20.A.3: the planner and the Hosios condition |
| [LogLinear](AKMMFrictionalLaborMarkets/LogLinear.lean) | 22 | §20.6, 20.A.4: log-linearisation, comparative statics, rigid wages |
| [EndogenousSeparation](AKMMFrictionalLaborMarkets/EndogenousSeparation.lean) | 17 | §20.7, 20.A.5: endogenous separations |
| [NGM](AKMMFrictionalLaborMarkets/NGM.lean) | 20 | §20.8, 20.A.6–20.A.8: the DMP model in the growth model |
| [McCall](AKMMFrictionalLaborMarkets/McCall.lean) | 23 | §20.9: the McCall model and its comparative statics |
| [MeanPreserving](AKMMFrictionalLaborMarkets/MeanPreserving.lean) | 11 | §20.9: mean-preserving spreads, the mean–min ratio |
| [Diamond](AKMMFrictionalLaborMarkets/Diamond.lean) | 6 | §20.9: the Diamond paradox |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
