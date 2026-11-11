# Miao Chapter 18: Search and Matching Models of Unemployment, in Lean

This is the `EconomicDynamics/SearchAndMatching` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 18 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 18 develops the Diamond–Mortensen–Pissarides model of equilibrium unemployment: matching,
Nash bargaining over wages and job creation, the steady state and its comparative statics,
transitional dynamics, efficiency and the Hosios condition, endogenous job destruction with
idiosyncratic productivity, and the model embedded in a business-cycle economy. The chapter
states no numbered results; every derivation the text carries out and Exercises 1–5 (their
mathematical content) are proved, except the nonlinear uniqueness of the saddle paths (the
linearised versions are proved), the business-cycle model's steady state and log-linearisation,
which the text does not derive, and the calibration of Exercise 5. The corrections are recorded
in [corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **233 theorems**, all new.

* **The basic DMP model** (§18.1): the matching function and the rates `q(θ)`, `θq(θ)` with
  elasticity `ξ ∈ (0, 1)` (`eq_18_1`, `dm_q_elasticity`); the Bellman equations, Nash bargaining
  and the wage (`eq_18_6` … `eq_18_15`, `dm_nash_solution`); the steady state exists uniquely iff
  `A > b` (`dm_ss_unique`, `dm_ss_exists`, `dm_ss_not_exists`), the Beveridge curve slopes down and
  is convex (`dm_beveridge_anti`, `dm_beveridge_convex`), comparative statics (`dm_cs_A`,
  `dm_cs_b`); transitional dynamics, where the sign of `a₂₁` is misprinted and unemployment need
  not fall monotonically (`dm_a21_sign`, `dm_saddle_path`, `dm_transition_not_monotone`); large
  firms (`eq_18_23` … `eq_18_27`); efficiency and the Hosios condition, with the planner's
  first-order condition and "ξ = β" corrected (`eq_18_28`, `dm_hosios`, `dm_planner_foc_N_misprint`,
  `dm_hosios_misprint`); Exercises 1–2 (`dm_ex1_steady`, `ex_18_2_efficiency`).
* **Endogenous job destruction** (§18.2): the reservation productivity and the job creation and
  destruction conditions, with the timing of (18.41)–(18.42) corrected (`eq_18_40`, `eq_18_41`,
  `eq_18_42`); the steady state exists uniquely (`jd_steady_state_existsUnique`, with a concrete
  instance `jd_example_steady_state`); comparative statics in productivity
  (`jd_compstat_kappaA`); the linearised saddle path (`jd_saddle`).
* **Business cycles** (§18.3): household and firm conditions and the Nash wage
  (`eq_18_49` … `eq_18_56`), where the printed household value of employment fails under the
  printed budget (`jd_hh_Vn_book_budget`); Exercises 3–5 (`ex_18_3_reservation`, `ex_18_4_hosios`,
  `ex_18_5_rho`).

All names are in the namespace `Miao.SearchAndMatching`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DMMatching](SearchAndMatching/DMMatching.lean) | 21 | §18.1: the matching function, job-filling and job-finding rates, the Beveridge curve |
| [DMBellman](SearchAndMatching/DMBellman.lean) | 13 | §18.1: values of jobs and workers, free entry, Nash bargaining and the wage equation |
| [DMSteadyState](SearchAndMatching/DMSteadyState.lean) | 23 | §18.1: the steady state — job creation and wage curves, Beveridge curve, comparative statics |
| [DMDynamics](SearchAndMatching/DMDynamics.lean) | 21 | §18.1: transitional dynamics — linearisation, saddle path and the phase diagram |
| [DMLargeFirm](SearchAndMatching/DMLargeFirm.lean) | 10 | §18.1: large firms |
| [DMEfficiency](SearchAndMatching/DMEfficiency.lean) | 11 | §18.1: efficiency — the planner's problem and the Hosios condition |
| [DMExercise1](SearchAndMatching/DMExercise1.lean) | 12 | Exercise 18.1: firms own capital, households trade firm shares |
| [DMExercise2](SearchAndMatching/DMExercise2.lean) | 7 | Exercise 18.2: the planner's problem with endogenous job destruction |
| [JDBasics](SearchAndMatching/JDBasics.lean) | 10 | Tools for Miao §§18.2–18.3: Nash bargaining, first-order and envelope conditions |
| [JDDistribution](SearchAndMatching/JDDistribution.lean) | 17 | The productivity distribution of Miao §18.2: the option-value integral |
| [JDEndogenous](SearchAndMatching/JDEndogenous.lean) | 18 | Endogenous job destruction: the equilibrium conditions (Miao §18.2, pp. 600–603) |
| [JDSteadyState](SearchAndMatching/JDSteadyState.lean) | 22 | Endogenous job destruction: steady state, comparative statics, dynamics (Miao §18.2) |
| [JDBusinessCycle](SearchAndMatching/JDBusinessCycle.lean) | 24 | Unemployment and business cycles (Miao §18.3, pp. 607–614) |
| [JDExercises](SearchAndMatching/JDExercises.lean) | 24 | Exercises 18.3–18.5 (Miao, p. 614) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
