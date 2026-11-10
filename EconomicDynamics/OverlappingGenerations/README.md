# Miao Chapter 16: Overlapping Generations Models, in Lean

This is the `EconomicDynamics/OverlappingGenerations` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 16 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 16 studies overlapping generations economies: Samuelson's pure-exchange model with fiat
money, its offer curve, monetary and autarkic equilibria and their optimality; Diamond's
production economy, its steady states, stability and dynamic (in)efficiency; and rational
bubbles. Every numbered definition, proposition and example (Definitions 16.1.1–16.1.3,
Propositions 16.1.1–16.1.3, Examples 16.1.1–16.1.2), the derivations of the text and Exercises 1–9
are proved, except the general Balasko–Shell and Cass optimality theorems, which the book cites
(their stationary versions are proved), the indeterminacy example of Figure 16.9, for which the
text gives no economy, and the nonlinear saddle path of the bubble economy (its linearisation is
proved). The corrections are recorded in [corrections](docs/corrections.md), and every book item
is located in the [source map](docs/source-map.md). The library contains **363 theorems**; 103 of
them are carried over from Chapter 1.

* **Exchange economies** (§16.1): equilibrium as a difference equation in real balances
  (`ox_ofSaving_isMonetary`, `ox_monetary_eulerRel`); autarky is the only nonmonetary equilibrium
  (`ox_nonmonetary_autarky`); the offer curve, its slopes and backward bending
  (`ox_offer_slope_z_pos`, `ox_offer_backward_iff`); stability is misstated at `|slope| = 1`
  (`ox_unstable_counterexample`); Examples 16.1.1–16.1.2, whose low-interest-rate path is not an
  equilibrium (`example_16_1_1_right`, `example_16_1_2_not_monetary`); **Propositions
  16.1.1–16.1.3** (`proposition_16_1_1`, `proposition_16_1_2`, `proposition_16_1_3`) and the
  stationary Balasko–Shell criterion (`ox_balasko_shell_stationary`); Exercises 1–2.
* **The Diamond model** (§16.2): the saving function and the map `G` (`op_saving_exists`,
  `op_G_exists`, `op_G_strictMono`); the "odd/even number of steady states" claims are false
  (`op_odd_counterexample`, `op_even_counterexample`) and Diamond's condition (ii) must read
  `G′(0) > 1` (`op_diamond_conditions`, `op_diamond_conditions_printed`); global and local stability
  (`op_global_convergence`); the golden rule and dynamic inefficiency (`op_golden_rule_unique`,
  `op_dynamic_inefficiency`), with the printed planner conditions corrected
  (`op_planner_foc_printed`).
* **Bubbles** (§16.3): the bubbly steady state is the golden rule (`op_bubbly_steady_golden`) and
  exists iff the bubbleless economy is dynamically inefficient (`op_bubbly_exists_iff`); the
  phase diagram, with the slope of the `Δk = 0` locus corrected (`op_kLocus_slope_printed`).
* **Exercises 3–9**: CRRA and log/Cobb–Douglas Diamond economies, CES technology, depreciation,
  government debt, social security, and the linearised bubble system's saddle (`ex_16_9_saddle`).

All names are in the namespace `Miao.OverlappingGenerations`. `Basics`, `Scalar` and
`PhaseDiagram` are copied from [EconomicDynamics/DifferenceEquations](../DifferenceEquations/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](OverlappingGenerations/Basics.lean) | 3 | The system (1.20), Assumptions 1.4.1–1.4.2, Definitions 1.4.1–1.4.5 (from Chapter 1) |
| [Scalar](OverlappingGenerations/Scalar.lean) | 61 | §1.1: scalar first-order equations, Examples 1.1.1–1.1.2 (from Chapter 1) |
| [PhaseDiagram](OverlappingGenerations/PhaseDiagram.lean) | 39 | §1.5, and a 2×2 saddle toolkit (from Chapter 1) |
| [OXPreferences](OverlappingGenerations/OXPreferences.lean) | 11 | Preferences of the Samuelson (1958) exchange economy |
| [OXEconomy](OverlappingGenerations/OXEconomy.lean) | 23 | The Samuelson (1958) exchange economy with fiat money |
| [OXExistence](OverlappingGenerations/OXExistence.lean) | 9 | Existence of monetary equilibrium (Proposition 16.1.1) |
| [OXOfferCurve](OverlappingGenerations/OXOfferCurve.lean) | 20 | The offer curve and the dynamics of the special case |
| [OXOptimality](OverlappingGenerations/OXOptimality.lean) | 18 | Pareto optimality in the exchange economy |
| [OXExamples](OverlappingGenerations/OXExamples.lean) | 16 | Examples 16.1.1 and 16.1.2 |
| [OXExercises](OverlappingGenerations/OXExercises.lean) | 14 | Exercises 16.1 and 16.2 |
| [OPHousehold](OverlappingGenerations/OPHousehold.lean) | 12 | The young agent's saving problem in the Diamond model |
| [OPDiamond](OverlappingGenerations/OPDiamond.lean) | 53 | The Diamond (1965) model: equilibrium law of motion and steady states |
| [OPEfficiency](OverlappingGenerations/OPEfficiency.lean) | 15 | Dynamic efficiency in the Diamond model |
| [OPBubbles](OverlappingGenerations/OPBubbles.lean) | 22 | Asset price bubbles in the Diamond model |
| [OPExercises](OverlappingGenerations/OPExercises.lean) | 34 | Exercises 16.3, 16.4 and 16.6–16.9 |
| [OPExercisesCES](OverlappingGenerations/OPExercisesCES.lean) | 13 | Exercise 16.5: the Diamond model with CES technology |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
