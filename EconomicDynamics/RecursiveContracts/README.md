# Miao Chapter 22: Recursive Contracts, in Lean

This is the `EconomicDynamics/RecursiveContracts` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 22 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 22 studies dynamic contracts with the promised value as the state: risk sharing with
limited commitment, repeated moral hazard (hidden action) and the inverse Euler equation, and
hidden information with its long-run immiseration. Every numbered result (Propositions
22.2.1–22.2.3, Assumptions 22.3.1–22.3.2, Lemmas 22.3.1–22.3.3, Propositions 22.3.1–22.3.4), the
derivations of the text and Exercises 1–4 are proved, except: the equivalence of the sequence
and recursive problems and the validity of the first-order approach in §22.2 (cited results,
taken as hypotheses); strict concavity, existence and uniqueness of optimal contracts and the C¹
property of the value function in §22.3 (concavity of the value function is proved); Zhang's
characterisation with stochastic stopping times (the deterministic version is proved); the
β → 1 limit of Exercise 3; and the computational parts of Exercise 2. The corrections are
recorded in [corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **277 theorems**, all new.

* **Limited commitment** (§22.1): the autarky value and the participation and promise-keeping
  constraints (`eq_22_1`, `eq_22_2`); the Bellman equation in the promised value, concavity and
  monotonicity of `P` (`lc_bellman_concave`, `lc_bellman_antitone`), the first-order and envelope
  conditions (`eq_22_5` … `eq_22_9`); the optimal contract — consumption never falls and rises only
  when the participation constraint binds (`lc_optimal_contract`, `eq_22_11`); "promised values
  never decrease" holds for i.i.d. income and fails for Markov income
  (`lc_iid_promised_value`, `lc_promise_decrease_counterexample`); the Lagrangian method
  (`eq_22_10`, `lc_lagrangian_sufficiency`); Zhang's characterisation and Exercises 1–2
  (`lc_zhang_identity`, `ex_22_1c`, `lc_ex_22_1c_min_not_attained`).
* **Hidden action** (§22.2): the first-order approach and the conditions (22.16)–(22.22)
  (`eq_22_16` … `eq_22_22`), the envelope condition (`ha_envelope_condition`); **Propositions
  22.2.1–22.2.2**, the latter needing a strictly increasing likelihood-ratio derivative
  (`proposition_22_2_1`, `proposition_22_2_2`, `ha_flat_mlrc_density`); the **inverse Euler
  equation**, printed with the wrong density (`proposition_22_2_3`,
  `ha_proposition_22_2_3_printed_false`); the agent would like to save (`ha_wants_to_save`).
* **Hidden information** (§22.3): **Lemmas 22.3.1–22.3.2** (`lemma_22_3_1`, `lemma_22_3_2`);
  **Proposition 22.3.1**, the value function exists uniquely and is concave, by a new repair
  argument since the book's sketch breaks promise keeping (`proposition_22_3_1`,
  `proposition_22_3_1_concave`, `hi_T_concaveOn`); **Propositions 22.3.2–22.3.3**; **Lemma 22.3.3**,
  false with one state (`hi_lemma_22_3_3_one_state`); **Proposition 22.3.4**, immiseration — the
  promised value tends to `−∞` almost surely, by martingale convergence, with a concrete CARA
  instance (`proposition_22_3_4`, `hi_poverty_example`); Exercises 3–4, the printed constant in
  Exercise 4 being inconsistent (`ex_22_4`, `ex_22_4_printed_inconsistent`).

All names are in the namespace `Miao.RecursiveContracts`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [LCAutarky](RecursiveContracts/LCAutarky.lean) | 8 | The endowment chain and the autarky value (Miao §22.1, pp. 774–775) |
| [LCSequence](RecursiveContracts/LCSequence.lean) | 10 | The sequence problem with one-sided limited commitment (Miao §22.1, pp. 774–776) |
| [LCBellman](RecursiveContracts/LCBellman.lean) | 21 | The Bellman equation with the promised value as the state (Miao §22.1.1, pp. 776–778) |
| [LCInstances](RecursiveContracts/LCInstances.lean) | 5 | Solutions of the Bellman equation with log utility, and the Markov counterexample |
| [LCDeterministic](RecursiveContracts/LCDeterministic.lean) | 8 | Discounted values of deterministic sequences |
| [LCLagrangian](RecursiveContracts/LCLagrangian.lean) | 8 | The Lagrangian method of Marcet and Marimon (Miao §22.1.2, pp. 778–780) |
| [LCZhang](RecursiveContracts/LCZhang.lean) | 26 | Zhang's minimum consumption function, deterministic case (Miao §22.1.3, pp. 780–781) |
| [LCExercise221](RecursiveContracts/LCExercise221.lean) | 15 | Exercise 22.1 and the alternative characterisation (Miao §22.1.3, pp. 780–781, 797–798) |
| [LCExercise222](RecursiveContracts/LCExercise222.lean) | 1 | Exercise 22.2: the AR(1) endowment (Miao, p. 798) |
| [HAModel](RecursiveContracts/HAModel.lean) | 13 | Hidden action: the repeated moral-hazard model |
| [HAIntegrals](RecursiveContracts/HAIntegrals.lean) | 10 | Hidden action: expectations over the output interval |
| [HAPropositions](RecursiveContracts/HAPropositions.lean) | 26 | Hidden action: the dynamics of the optimal contract |
| [HIBasics](RecursiveContracts/HIBasics.lean) | 17 | Hidden information: the model and the incentive constraints |
| [HIAssumption](RecursiveContracts/HIAssumption.lean) | 9 | Assumption 22.3.1 and the DARA step of Proposition 22.3.1 |
| [HIBellman](RecursiveContracts/HIBellman.lean) | 39 | The principal's Bellman equation and Proposition 22.3.1 |
| [HIOptimal](RecursiveContracts/HIOptimal.lean) | 14 | Optimal contracts: Propositions 22.3.2–22.3.3, (22.27)–(22.30), Lemma 22.3.3 |
| [HIConcavity](RecursiveContracts/HIConcavity.lean) | 16 | Concavity of the value function (Proposition 22.3.1) |
| [HIPoverty](RecursiveContracts/HIPoverty.lean) | 12 | Long-run poverty: Proposition 22.3.4 |
| [HIExercises](RecursiveContracts/HIExercises.lean) | 19 | Exercises 22.3 and 22.4 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
