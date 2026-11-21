# Source map

Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), Chapter 5, "Markov Decision
Process Model". Page numbers are those of the author's draft of 21 April 2013, pp. 135–156. Lean
names are relative to `Miao.MarkovDecisionProcesses`. Where the Lean statement departs from the
book, see [corrections](corrections.md). The chapter has six exercises.

## Copied from Stokey, Lucas and Prescott

| Source | Lean modules |
| --- | --- |
| `RecursiveMethods/StochasticDP` (histories) | `HistoryTools` |

## §5.1 Model setup (pp. 135–143)

| Source | Claim | Lean |
| --- | --- | --- |
| (5.1), pp. 135–137 | The Markov decision process: times, spaces, `Γ`, kernels, rewards | `MDP`, `MDP.IsMarkov`, `MDP.IsStationary`, `NonemptyValued` |
| Definition 5.1.1, p. 137 | Plans, Markov and stationary plans | `Plan`, `IsPlan`, `IsMarkovian`, `IsStationaryPlan` |
| Definition 5.1.2, p. 137 | Feasible plans | `IsFeasible`, `feasiblePlans` |
| Assumption 5.1.1, Lemma 5.1.1, p. 138 | A measurable selection gives a feasible (Markov, stationary) plan; conversely; `Π(s₀)` may be empty | `HasMeasurableSelection`, `lemma_5_1_1`, `selectionPlan_markov`, `selection_of_feasible`, `lemma_5_1_1_iff`, `no_selection_example` |
| (5.2), p. 138 | The measure on finite histories (Tulcea) | `mu`, `isProbabilityMeasure_mu`, `eq_5_2`, `mu_succ_lintegral`, `integral_mu_succ`, `mu_congr`, `stepKernel` |
| p. 138 | Under a Markov plan the states form a Markov process | `mu_markovian` |
| p. 139 | The measure on infinite histories | `muInf`, `muInf_marginal`, `muInf_zero`, `muInf_unique`, `partialTraj_map_splitSeg` |
| Assumptions 5.1.2–5.1.4, pp. 139–140 | Discounting and rewards | `Assumption512`, `Assumption513`, `Assumption514`, `assumption_5_1_3_of_bounded`, `assumption_5_1_4_of_bounded`, `assumption_5_1_4_of_boundedOn` |
| (5.3)–(5.4), p. 140 | The objectives; well-defined under the assumptions | `J0T`, `eq_5_3`, `J`, `eq_5_4`, `partialSum_eq`, `measurable_rew`, `J_spec`, `J_welldefined`, `abs_J_le`, `tendsto_partialSum_of_bddAbove`, `tendsto_partialSum_of_bddBelow` |
| (5.5)–(5.6), p. 141 | Value functions and optimal plans | `V0`, `V`, `IsValueOf`, `isValueOf_iff`, `V0_char`, `V_char`, `IsOptimalPlan0`, `IsOptimalPlan`, `IsOptimalPlan0.isGreatest` |
| Example 5.1.1, p. 141 | A static problem without an optimum | `V0_one`, `example_5_1_1a_pos`, `example_5_1_1a_nonpos`, `example_5_1_1a_empty`, `example_5_1_1b` |
| p. 142 | Deterministic problems | `detKernel_apply`, `mu_det`, `J0T_det` |
| pp. 142–143 | Randomized plans | `RPlan`, `IsFeasibleR`, `rmu`, `isProbabilityMeasure_rmu`, `detRPlan_feasible_iff` |

## §5.2 Examples (pp. 143–155)

| Source | Claim | Lean |
| --- | --- | --- |
| §5.2.1, pp. 143–144 | Discrete choice (Rust's bus engine) | `rust`, `rustKernel`, `rust_cdf_keep`, `rust_cdf_replace`, `rust_nonneg`, `rust_assumptions` |
| §5.2.2, pp. 144–145 | Optimal stopping as an MDP with an absorbing state; the values agree | `StoppingProblem`, `toMDP`, `stopRule`, `aliveSet`, `stopValue`, `stopValueInf`, `J0T_toMDP`, `J_toMDP`, `stopValue_toPlan`, `V0_toMDP`, `V_toMDP`, `toMDP_assumptions`, `bookΓ_infeasible` |
| (5.7)–(5.8), p. 146 | Option exercise; the American call | `eq_5_7_5_8`, `optionExercise_assumptions`, `americanCall_beta` |
| (5.9)–(5.10), p. 147 | Exit | `eq_5_9_5_10`, `exitProblem_assumptions` |
| pp. 147–149 | The secretary problem | `secretary`, `secretary_Q`, `secretary_assumptions`, `card_bestOfAll`, `card_bestOfFirst`, `secretary_prob` |
| §5.2.3, pp. 149–151 | The bandit model; frozen arms | `Bandit`, `armKernel`, `bandit_P_apply`, `bandit_P_rect`, `bandit_P_frozen`, `bandit_book_false`, `bandit_assumptions` |
| p. 151 | A two-armed bandit with a constant arm is a stopping problem | `ex_bandit_constant_arm`, `retirePay_shift`, `retirePay_succ`, `banditPay_retireSeq` (deterministic risky arm); the stochastic case is not formalised |
| pp. 151–152 | Task selection | `taskSelection`, `taskSelection_assumptions` |
| §5.2.4, pp. 153–155 | Optimal control as an MDP; (5.11)–(5.14); the values agree | `ControlProblem`, `controlKernel`, `controlKernel_rect`, `controlKernel_rect_of_indep`, `ctrlX`, `controlObj`, `controlV`, `J0T_control`, `J_control`, `controlPlan_feasible`, `inducedPolicy_controlPlan`, `V0_control` |

## §5.3 Exercises (pp. 155–156)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 1 | Job search as optimal stopping | `jobSearch`, `ex_5_1_accept`, `ex_5_1` |
| Ex 2 | The American put | `americanPut`, `ex_5_2` |
| Ex 3 | Secretary problem: one of the two best | `secretaryTwo`, `rank3`, `ex_5_3` |
| Ex 4 | Pandora's problem as a bandit | `pandora`, `pandoraKernel`, `ex_5_4`, `ex_5_4_collect` |
| Ex 5 | The stochastic Ramsey model, with `(C, I, N)` or `(K′, N)` as controls | `ramsey1`, `ramsey2`, `ex_5_5`, `ex_5_5_assumptions`, `ReparamOK`, `reparamPlan`, `J0T_reparam`, `J_reparam`, `V0_reparam`, `V_reparam` |
| Ex 6 | Inventory management | `inventory`, `ex_5_6` |
