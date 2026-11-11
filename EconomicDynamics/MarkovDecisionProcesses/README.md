# Miao Chapter 5: Markov Decision Process Model, in Lean

This is the `EconomicDynamics/MarkovDecisionProcesses` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 5 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 5 sets up the Markov decision process and casts a series of economic problems as
instances. The model, Definitions 5.1.1–5.1.2, Assumptions 5.1.1–5.1.4 and Lemma 5.1.1 are
formalised, with the history measures built by Ionescu Tulcea; every example and all six
exercises are instances of the model satisfying its assumptions, with the equivalences the text
asserts proved. The corrections are recorded in [corrections](docs/corrections.md), and every
book item is located in the [source map](docs/source-map.md). The library contains
**193 theorems**.

* **The model** (§5.1): plans and feasibility, a measurable selection gives a feasible Markov
  plan and is necessary for it (`lemma_5_1_1`, `lemma_5_1_1_iff`), the measures on finite and
  infinite histories (`mu`, `eq_5_2`, `muInf`), well-defined objectives (`J_welldefined`,
  `abs_J_le`), values and optimal plans (`V0`, `V`), Example 5.1.1 (`example_5_1_1a_pos`).
* **Examples** (§5.2): Rust's discrete choice (`rust_assumptions`), optimal stopping with the
  stopping value equal to the MDP value (`V_toMDP`) — the book's `Γ(ŝ) = ∅` makes no plan
  feasible (`bookΓ_infeasible`) — option exercise, exit and the secretary problem
  (`secretary_prob`), bandits (`bandit_P_frozen`, `bandit_book_false`), and optimal control with
  the control value equal to the MDP value (`V0_control`).
* **Exercises**: job search, the American put, the two-best secretary problem, Pandora's problem,
  the Ramsey model with either set of controls giving the same values (`ex_5_5`), inventory.

All names are in the namespace `Miao.MarkovDecisionProcesses`. `HistoryTools` is copied from
[RecursiveMethods/StochasticDP](../../RecursiveMethods/StochasticDP/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [HistoryTools](MarkovDecisionProcesses/HistoryTools.lean) | 6 | Histories (copied from SLP Ch 9) |
| [Basics](MarkovDecisionProcesses/Basics.lean) | 8 | (5.1), Definitions 5.1.1–5.1.2, Assumption 5.1.1 |
| [Histories](MarkovDecisionProcesses/Histories.lean) | 12 | Finite histories |
| [Objective](MarkovDecisionProcesses/Objective.lean) | 22 | (5.2)–(5.6), Lemma 5.1.1, Assumptions 5.1.2–5.1.4 |
| [KernelTools](MarkovDecisionProcesses/KernelTools.lean) | 4 | Kernel builders |
| [Simulation](MarkovDecisionProcesses/Simulation.lean) | 8 | Transport between models |
| [Trajectory](MarkovDecisionProcesses/Trajectory.lean) | 15 | Infinite histories by Ionescu Tulcea |
| [Example511](MarkovDecisionProcesses/Example511.lean) | 7 | Example 5.1.1 |
| [Deterministic](MarkovDecisionProcesses/Deterministic.lean) | 2 | Deterministic problems |
| [Randomized](MarkovDecisionProcesses/Randomized.lean) | 4 | Randomized plans |
| [DiscreteChoice](MarkovDecisionProcesses/DiscreteChoice.lean) | 8 | §5.2.1: Rust |
| [OptimalStopping](MarkovDecisionProcesses/OptimalStopping.lean) | 29 | §5.2.2: stopping as an MDP |
| [StoppingExamples](MarkovDecisionProcesses/StoppingExamples.lean) | 14 | Option exercise, exit, Exercises 1–2 |
| [Secretary](MarkovDecisionProcesses/Secretary.lean) | 6 | The secretary problem, Exercise 3 |
| [Bandit](MarkovDecisionProcesses/Bandit.lean) | 15 | §5.2.3: bandits, task selection, Exercise 4 |
| [OptimalControl](MarkovDecisionProcesses/OptimalControl.lean) | 20 | §5.2.4: control as an MDP |
| [ControlExercises](MarkovDecisionProcesses/ControlExercises.lean) | 13 | Exercises 5–6 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
