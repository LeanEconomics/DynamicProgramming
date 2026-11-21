# Source map: Miao Chapter 13

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 13, Complete
Markets Exchange Economies, pp. 415–454. Lean names are relative to `Miao.CompleteMarkets`. The
three parts model the event tree the same way (histories as lists of shocks, newest first) but each
with its own structure: `POEconomy` for §13.1–13.3, `RDTree` for §13.4–13.5, `BPTree` for
§13.6–13.8. Departures from the book are in [corrections](corrections.md).

## §§13.1–13.3 and Exercises 13.1–13.2

### §13.1 Uncertainty, preferences and endowments (`POEventTree`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 415–416 | Histories `sᵗ = (s₀, …, s_t)`, `s₀` given; a node is the list of later shocks, newest first | `List S`, `po_successor` |
| p. 416 | Each node has a unique immediate predecessor `sᵗ⁻`; successors `sᵗ⁺` | `po_unique_predecessor`, `po_successor` |
| p. 416 | Probabilities `Pr(sᵗ)`, `Pr(s₀) = 1` | `POProb`, `po_sum_continuations`, `po_sum_pr_time`, `po_iid`, `po_coin` |
| p. 416 | Conditional probabilities `Pr(sᵀ | sᵗ)`, nodes `sᵀ | sᵗ` | `po_condPr`, `po_condPr_sum`, `po_condPr_root` |
| p. 416 | Adapted processes; `L∞`, `L¹`, `L∞₊` | `po_Linfty`, `po_L1`, `po_Lplus`, `po_Lplus_subset_Linfty` |
| p. 416 | Agents, endowments `yⁱ ∈ L∞₊`, common `β ∈ (0, 1)` | `POEconomy`, `po_exampleEconomy` |
| (13.1), p. 416 | Discounted expected utility `Uⁱ(cⁱ)`, well defined on `L∞₊` | `po_w`, `po_U`, `po_w_nonneg`, `po_w_root`, `po_sum_w_time`, `po_summable_w`, `eq_13_1` |
| Assumption 13.1.1, p. 416 | Strictly increasing, `C²`, strictly concave, Inada | `Assumption13_1_1`, `assumption_13_1_1_sqrt`, `po_exampleEconomy_assumption`, `po_differentiableAt`, `po_strictAntiOn_deriv` |

### §13.2 Pareto optimum (`POPareto`)

| Source | Claim | Lean |
| --- | --- | --- |
| (13.2), p. 417 | Feasibility | `po_Feasible`, `po_perturb`, `po_perturb_feasible` |
| p. 417 | Pareto optimality; the planner's problem `max Σᵢ λⁱ Uⁱ(cⁱ)` | `po_ParetoOptimal`, `po_SolvesPlanner` |
| Proposition 13.2.1, p. 417 | PO iff planner solution for some nonzero `λ ∈ ℝᴵ₊` | `proposition_13_2_1` |
| Proof, "only if", p. 417 | `𝒰` convex by concavity, misses `Y`; separating hyperplane; `λ ≥ 0` | `po_U_concave`, `po_Lplus_comb`, `po_planner_of_pareto` |
| Proof, "if", pp. 417–418 | Weighted-utility contradiction; transfer from a zero-weight agent | `po_planner_improvement`, `po_transfer_improvement`, `po_U_mono`, `po_U_update`, `po_update_mem`, `po_tsum_update`, `po_pareto_of_planner_pos` |
| p. 418 | First-order conditions `uⁱ'(cⁱ_t)/uʲ'(cʲ_t) = λʲ/λⁱ` | `po_planner_foc`, `po_planner_foc_ratio` |
| (13.3), p. 418 | `cⁱ_t = (uⁱ')⁻¹(λᵢ⁻¹ λ₁ u¹'(c¹_t))` | `eq_13_3` |
| (13.4), p. 418 | `Σᵢ (uⁱ')⁻¹(λᵢ⁻¹ λ₁ u¹'(c¹_t)) = Σᵢ yⁱ_t` | `eq_13_4` |
| p. 418 | Consumption depends only on the aggregate endowment | `po_risk_sharing`, `po_consumption_fn_aggregate` |
| p. 418 | Markov aggregate state: no history dependence | `po_no_history_dependence` |

### §13.3 Time 0 trading (`POTimeZero`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 418 | Arrow–Debreu state prices `q⁰_t(sᵗ)`, `q⁰₀(s₀) = 1` | hypothesis `q [] = 1` where used |
| (13.5), p. 419 | Budget constraint; well defined for `q⁰ ∈ L¹` | `po_cost`, `eq_13_5`, `po_cost_update`, `po_sum_cost` |
| Definition 13.3.1, p. 419 | Arrow–Debreu equilibrium | `po_ADEquilibrium`, `po_example_ADEquilibrium` |
| (13.6), p. 419 | `βᵗ uⁱ'(cⁱ_t) Pr(sᵗ) = μᵢ q⁰_t(sᵗ)`, `μᵢ = uⁱ'(cⁱ₀(s₀))` | `eq_13_6` |
| (13.7), p. 419 | `q⁰_t(sᵗ) = βᵗ uⁱ'(cⁱ_t) Pr(sᵗ) / uⁱ'(cⁱ₀(s₀))` | `eq_13_7` |
| (13.8), p. 419 | `uⁱ'(cⁱ_t)/uʲ'(cʲ_t) = μᵢ/μⱼ` | `eq_13_8` |
| (13.9), p. 419 | `cⁱ_t = (uⁱ')⁻¹(u¹'(c¹_t) μᵢ/μ₁)` | `eq_13_9` |
| (13.10), p. 419 | Feasibility in terms of `c¹_t` | `eq_13_10` |
| pp. 419–420 | The equilibrium allocation is the planner's with `λᵢ = μᵢ⁻¹`; shadow prices `ξ = q⁰` | `po_AD_solves_planner`, `po_AD_shadow_price`, `po_planner_of_foc`, `po_utility_gain_le`, `po_optimal_of_foc`, `po_tangent`, `po_deriv_pos` |
| Example 13.3.1, p. 420 | CRRA: `cⁱ = cʲ(μᵢ/μⱼ)^{−1/γ}`, `cⁱ = μᵢ^{−1/γ}/Σⱼ μⱼ^{−1/γ} · ȳ` | `po_crra_hasDerivAt`, `example_13_3_1`, `example_13_3_1_shares` |
| pp. 420–421 | Negishi algorithm, steps 1–3 and the stopping point | `po_negishi_step3`, `po_negishi_fixed_point` |
| p. 421 | Scaling `μ` rescales prices; `q⁰₀(s₀) ≠ 1` in general | `po_negishi_scale`, `po_negishi_q0` |
| p. 421, step 4 | Iterate to convergence | Not formalised (the text claims no convergence) |
| Theorem 13.3.1, p. 421 | First Welfare Theorem | `theorem_13_3_1`, `po_local_nonsatiation` |
| Theorem 13.3.2, pp. 421–422 | Second Welfare Theorem | `theorem_13_3_2` (corrected), `theorem_13_3_2_counterexample`, `po_pareto_foc` |
| pp. 422–423 | Proof outline: Hahn–Banach, Yosida–Hewitt, Mackey continuity, cheaper point | Not formalised in this setting (the proof of `theorem_13_3_2` uses first-order conditions instead); the abstract versions are SLP Theorems 15.4, 15.6 and the Remark (`theorem_15_4`, `theorem_15_6`, `remark_cheaper_point` in [RecursiveMethods/ParetoOptimaEquilibria](../../../RecursiveMethods/ParetoOptimaEquilibria/README.md)) |
| pp. 423–424 | Asset prices `p₀`, `p_t(sᵗ)`; need `q⁰ ∈ L¹`; with (13.7) | `po_assetPrice`, `po_assetPrice_summable`, `po_assetPrice_root`, `po_assetPrice_eq` |

### Exercises (`POExercises`)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 13.1, (13.37), p. 452 | Representative agent `U_λ`; `(ȳ, p)` no-trade equilibrium; `c` solves (13.37) | `po_repSet`, `po_Ulam`, `ex_13_1` |
| Exercise 13.2, p. 452 | Constant aggregate endowment: Pareto optima | `ex_13_2`, `ex_13_2_converse` |

## §13.4–§13.5 and Exercises 13.3, 13.4, 13.8

### §13.1 setting used in §13.4–13.5

| Source | Claim | Lean |
| --- | --- | --- |
| p. 416 | Event tree, `Pr(sᵗ)`, conditional probabilities, conditional expectations | `RDTree`, `rd_uniformTree`, `rd_dsum`, `rd_paths`, `rd_mem_paths`, `rd_dsum_succ`, `rd_dsum_succ'`, `rd_dsum_add_len`, `rd_dsum_Pr`, `rd_condPr`, `rd_condPr_sum`, `rd_condE`, `rd_condE_root`, `rd_condE_one` |
| p. 416 | `L^∞`, `L^∞₊`, `L¹` | `rd_Bdd`, `rd_LinfPos`, `rd_L1`, `rd_L1_mul`, `rd_L1_mul_abs`, `rd_L1_mul_tendsto`, `rd_L1_tendsto` |
| (13.1), p. 416 | Discounted expected utility; strictly increasing when `u` is | `rd_EU`, `rd_EU_summable`, `rd_eq_13_1`, `rd_StrictIncr`, `rd_Mono` |
| (13.2), (13.5), Def. 13.3.1, p. 417–419 | Feasibility, Arrow–Debreu budget and equilibrium (in this setting; §13.3 itself is the PO project) | `rd_Feasible`, `rd_ADBudget`, `rd_ADEqm` |
| p. 417 | Pareto optimality | `rd_ParetoOptimal` |
| Thm 13.3.1, p. 421 (used on p. 433) | First Welfare Theorem in this setting | `rd_first_welfare` |

### §13.4 Sequential trading

### Investment opportunities (pp. 424–426)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 424 | Securities, prices `p_t(sᵗ)`, one-period payoffs `f_{t+1}`, payoff matrix `D_{t+1}(sᵗ)` | `rd_fz`, `rd_prev`, `rd_payoffMatrix`, `rd_payoffMatrix_mulVec`, `rd_payoffMatrix_transpose_mulVec` |
| (13.11a)–(13.11b), p. 425 | Sequential budget constraints | `rd_Budget`, `eq_13_11`, `rd_net`, `rd_budget_iff_net`, `rd_BudgetEq` |
| (13.12), p. 425 | Arrow securities and their budget | `rd_arrowPayoff`, `rd_arrowIn`, `rd_ArrowBudget`, `eq_13_12` |
| p. 425 | Stock: payoff `p_{t+1} + d_{t+1}`; riskless bond: payoff `1` | Payoff processes `f`; instances: `rd_oneArb_converse_fails`, `rd_statePrice_not_L1`, Example 13.5.1 (`rd_exp`) |
| pp. 425–426 | Two-period bond = one-period payoff `q_{1,t+1}`; call option = one-period payoff `p^c_{t+1}` | `rd_multiperiod_price`, `rd_twoPeriodBond` |

### Ponzi schemes and portfolio constraints (pp. 426–427)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 426 | Ponzi scheme | `rd_Ponzi` |
| (13.13), p. 426 | Debt constraints | `rd_ThetaDC` |
| (13.14), p. 427 | Borrowing constraints | `rd_ThetaBC` |
| (13.15), p. 427 | Short-sales constraints | `rd_ThetaSC` |
| p. 427 | Admissible sets `Θᵃ(p, f)` and the agent's problem | `rd_SeqFeas`, `rd_Solves`, `rd_SolvesC` |

### Radner equilibrium (pp. 427–428)

| Source | Claim | Lean |
| --- | --- | --- |
| Def. 13.4.1, p. 427 | Radner equilibrium with debt constraints (and with borrowing constraints, p. 428) | `rd_RadnerDC`, `rd_RadnerBC` |
| Def. 13.4.1 | The goods-market condition follows from the budget equalities and `∑ θⁱ = θ̄` | `rd_goods_clearing`, `rd_prev_sum` |
| p. 428 | With zero supply, market clearing is (13.2) | `definition_13_4_1` |

### Arbitrage and state prices (pp. 428–430)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 428 | Arbitrage opportunity, one-period arbitrage | `rd_Arb`, `rd_ArbOn`, `rd_OneArb`, `rd_OneArbOn` |
| p. 428 | A Ponzi scheme is an arbitrage | `rd_ponzi_arb` |
| p. 428 | No arbitrage ⇒ no one-period arbitrage at any node | `rd_noArb_noOneArb`, `rd_noArbOn_noOneArbOn`, `rd_arb_loc`, `rd_loc` |
| p. 428 | The converse may fail | `rd_oneArb_converse_fails` |
| p. 428 | Recession set `R(Θᵃ)` | `rd_Rec` |
| Thm 13.4.1, p. 429 | Optimum with strictly increasing utility ⇒ no arbitrage on `R(Θᵃ)` | `theorem_13_4_1` |
| Thm 13.4.2, p. 429 (DC) | No one-period arbitrage on `R(Θ_DC)` ⇔ positive state prices with (13.16) | `theorem_13_4_2`, `rd_StatePrice`, `rd_node_stiemke`, `rd_arbRow`, `rd_qOf`, `rd_statePrice_qOf`, `rd_noOneArb_of_statePrice` |
| Thm 13.4.2, p. 429 (BC) | Same for `R(Θ_BC)` — false as printed; corrected | `theorem_13_4_2_BC_counterexample`, `theorem_13_4_2_BC` |
| p. 429 (proof) | `R(Θ_DC) = {f_{t+1} · θ_t ≥ 0}`, `R(Θ_BC) = {p_t · θ_t ≥ 0}` | `rd_rec_DC`, `rd_rec_BC`, `rd_nonneg_of_forall_lam` |
| p. 429 (proof) | Stiemke's Lemma | `rd_stiemke`, `rd_simplex`, `rd_simplex_convex`, `rd_simplex_compact` |
| (13.16), p. 429 | No-arbitrage pricing equation | `rd_StatePrice`, `rd_statePrice_mul`, `rd_statePrice_dot` |
| p. 430 | Only ratios restricted; normalise `q⁰(s⁰) = 1` | `rd_statePrice_smul`, `eq_13_17_normalize` |
| (13.17), p. 430 | State price deflator, stochastic discount factor | `rd_deflator`, `rd_SDF` |
| (13.18), p. 430 | `p_t = (1/π_t) E_t[π_{t+1} f_{t+1}] = E_t[M_{t+1} f_{t+1}]` | `eq_13_18` |
| p. 430 | Theorem 13.4.2 does not imply `π, q⁰ ∈ L¹` | `rd_statePrice_not_L1` |
| p. 430 | `R(Θ_SC) = {θ ≥ 0}` | `rd_rec_SC` |
| p. 430 | (13.16) does not apply under short-sales constraints; it holds as an inequality | `rd_SC_no_statePrice`, `rd_SC_inequality` |

### Complete markets (pp. 430–432)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 430–431 | Dynamically complete markets (book's definition) | `rd_CompletePrinted`; always true with positive prices: `rd_completePrinted_of_pos`, `rd_rollover` |
| p. 431 / Ex. 13.8 | Complete ⇔ rank `D_{t+1}(sᵗ) = S` (corrected definition) | `rd_Complete`, `ex_13_8`, `rd_backward`, `rd_rank_iff_span`, `rd_rank_iff_injective`; printed: `ex_13_8_printed_if`, `ex_13_8_counterexample` |
| Thm 13.4.3, p. 431 | Complete markets + no arbitrage ⇒ unique state prices up to scale | `theorem_13_4_3`, `rd_statePrice_unique`, `rd_ratio_solves`; with the printed definition: `theorem_13_4_3_counterexample` |
| p. 431 (proof) | `x_{t+1} = (DᵀD)⁻¹ Dᵀ p_t` | `theorem_13_4_3_formula` |
| p. 431 | Complete set of Arrow securities | `rd_arrow_rank` |
| p. 432 | Arrow price from first-order conditions, `Q = βu′(c_{t+1}) Pr(s′|sᵗ)/u′(c_t)` | `rd_arrow_price` (uses `rd_euler_eq`, `rd_DC_slack`) |
| p. 432 | It does not depend on `i` | `rd_arrow_price_common` |
| p. 432 | `q⁰_{t+1}(sᵗ⁺¹) = Q_t(s_{t+1}|sᵗ) q⁰_t(sᵗ)` | `rd_arrow_statePrice` |
| p. 432 (with (13.7)) | Euler equations make `βᵗ Pr u′(c)/u′(c₀)` a state price process | `rd_statePrice_of_euler` |

### Equilibrium with transversality condition (pp. 432–434)

| Source | Claim | Lean |
| --- | --- | --- |
| (13.19), p. 432 | Present-value budget at `sᵗ` up to horizon `T` | `eq_13_19` (state prices), `eq_13_19_E` (book's `E_t` form), equality version `rd_pv_eq` |
| (13.20), p. 432 | At the root | `eq_13_20` |
| (13.21), p. 433 | Transversality condition | `rd_TVC` |
| (13.22), p. 433 | Limit at the root | `eq_13_22`, `rd_AD_of_lowerTail` |
| (13.23), p. 433 | Limit at `sᵗ` (needs the conditional transversality condition) | `eq_13_23`, `rd_AD_of_lowerTail_at`; counterexample from (13.21) alone: `eq_13_23_counterexample` |
| Def. 13.4.2, p. 433 | Competitive equilibrium with transversality condition | `rd_CETVC` |
| p. 433 | Its allocation is an Arrow–Debreu equilibrium allocation (zero holdings) | `definition_13_4_2` |
| p. 433 | … hence Pareto optimal | `rd_cetvc_pareto` |
| pp. 433–434 | Pareto optima are supported: (13.22) is (13.5); the Arrow–Debreu equilibrium given by the Second Welfare Theorem is a CE with TVC (replication by complete markets) | `rd_ad_cetvc`, `rd_repl`, `rd_repl_payoff`, `rd_repl_value`, `rd_repl_budget`, `rd_repl_sum_zero`, `rd_W`, `rd_W_rec`, `rd_W_dsum`, `rd_W_tendsto` |

### Natural debt limit (pp. 434–435)

| Source | Claim | Lean |
| --- | --- | --- |
| (13.24), p. 434 | `f_t · θ_{t−1} ≥ −(1/π_t) E_t ∑ π y` | `eq_13_24` |
| p. 434 | Natural debt limit | `rd_naturalDebtLimit` |
| p. 435 | Never binds when consumption is strictly positive | `rd_naturalDebt_nonbinding` |
| p. 435 | Natural borrowing limit via (13.18) | `rd_naturalBorrowing` |
| p. 435 | Short-sales limit when `p` is bounded | No formal content (no limit is stated) |
| — | Bounded borrowing/debt limits imply (13.22) | `rd_AD_of_BC`, `rd_AD_of_DC`, `rd_summable_subtree` |

### §13.5 Equivalence of equilibria

| Source | Claim | Lean |
| --- | --- | --- |
| Thm 13.5.1, p. 435 | Radner eqm with nonbinding constraints ⇔ CE with TVC (complete markets, zero supply) | definitions `rd_RadnerBCnb`, `rd_RadnerDCnb`; "if" (corrected): `theorem_13_5_1_if`; "if" as printed false: `theorem_13_5_1_counterexample`; "only if" (expected utility): `theorem_13_5_1_onlyIf` |
| Ex. 13.5.1, p. 436 | Magill–Quinzii economy: Arrow–Debreu equilibrium | `example_13_5_1_AD`, `rd_exU`, `rd_exy`, `rd_exc`, `rd_exq`, `rd_exR`, `rd_exζ` |
| Ex. 13.5.1 | Bond prices `p₀ = 1`, `p_t = t²/(t+1)²` | `example_13_5_1_prices`, `rd_exp` |
| Ex. 13.5.1 | Same allocation with `θ¹_t = −(t+1)² ∑_{n>t} 1/n²` is a CE with TVC | `example_13_5_1_CETVC`, `rd_exθ`, `rd_ex_budget`, `rd_ex_value` |
| Ex. 13.5.1 | `π_T p_T θ¹_T = −∑_{n>T} 1/n² → 0` | `example_13_5_1_TVC` |
| Ex. 13.5.1 | `p_T θ¹_T = −∑_{s≥1} T²/(T+s)² → −∞`; not a Radner eqm with borrowing constraints | `example_13_5_1_unlimited`, `example_13_5_1_not_Radner` |
| pp. 436–437 | Agent 2 progressively more patient; PV of agent 1's endowment → ∞ | `example_13_5_1_patience` |
| Assumption 13.5.1, p. 437 | Uniform lower bound on impatience | `rd_impPlan`, `rd_Assumption1351Printed`, `rd_Assumption1351`, `rd_assumption1351_of_printed` |
| p. 437 | Satisfied by continuous discounted expected utility (corrected: plans in `[0, ȳ]`) | `assumption_13_5_1`; printed form fails: `assumption_13_5_1_printed_fails` |
| pp. 437–438 (proof, "if") | Scaling argument: `(1 − α) p_t · θⁱ_t < κ ȳ_t`, then `p_t · θⁱ_t > −(I−1)κȳ/(1−α)`; bounded `p · θ` satisfies the TVC; BC set ⊂ TVC set | `rd_impatience_bound`, `rd_scaled_plan_le`, `theorem_13_5_1_if`, `rd_AD_of_BC`, `rd_AD_of_DC` |
| pp. 438–439 (proof, "only if") | Separation, Mackey continuity, unique `π` | Not formalised as sketched; the statement is proved for (13.1) in `theorem_13_5_1_onlyIf` (with `rd_budget_binds`, `rd_gradIneq_antitone`, `rd_statePrice_of_euler`, `rd_statePrice_unique`) |

### Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Ex. 13.3, p. 452 | Prove Theorem 13.4.1 | `ex_13_3` |
| Ex. 13.4, p. 452 | First-order conditions, borrowing constraints | `ex_13_4_BC_foc` (necessity), `rd_euler_dir`, `rd_euler_eq`, `rd_Phi`, `rd_Phi_eq`, `rd_BC_feas` |
| Ex. 13.4 | First-order conditions, short-sales constraints | `ex_13_4_SC_foc` |
| Ex. 13.4 | First-order conditions, debt constraints | `ex_13_4_DC_foc` (rank `S`) |
| Ex. 13.4, (13.39) | FOC + TVC sufficient (borrowing) | `ex_13_4_BC_suff`, equilibrium: `ex_13_4_BC_eqm` |
| Ex. 13.4, (13.40) | FOC + TVC sufficient (short sales) | `ex_13_4_SC_suff` |
| Ex. 13.4, (13.38) | FOC + TVC sufficient (debt) | `ex_13_4_DC_suff` |
| Ex. 13.4 | Necessity of the transversality conditions | Not formalised |
| Ex. 13.4 (tools) | Concavity, telescoping, perturbation | `rd_GradIneq`, `rd_gradIneq_of_concave`, `rd_sqrt_gradIneq`, `rd_telescope`, `rd_foc_xi`, `rd_suff_core`, `rd_gain_le`, `rd_EU_pert`, `rd_net_loc_self`, `rd_net_loc_child`, `rd_net_loc_other` |
| Ex. 13.8, p. 454 | Complete ⇔ rank `S` | `ex_13_8` (corrected definition), `ex_13_8_printed_if`, `ex_13_8_counterexample` |

## §§13.6–13.8 and Exercises 13.5–13.7, 13.9–13.10

### §13.6 Asset price bubbles

| Source | Claim | Lean |
| --- | --- | --- |
| p. 439 | No bubble on assets with finite maturity | `bp_no_bubble_finite_maturity` (with `bp_condExp_congr_length`) |
| p. 439 | The no-arbitrage pricing equation `p_t = (1/π_t) E_t[π_{t+1}(p_{t+1} + d_{t+1})]` | `bp_Prices` |
| p. 439 | Forward substitution `p_t = (1/π_t)∑_{j=1}^T E_t π_{t+j}d_{t+j} + (1/π_t)E_t π_{t+T}p_{t+T}` | `eq_13_6_forward`, `bp_forward_mul` |
| p. 440 | The fundamental value `v_t(d)` (the series converges for `p, d ≥ 0`) | `bp_fundamental`, `bp_summable_dividends`, `bp_mul_fundamental` |
| p. 440 | The bubble `b_t = p_t − v_t(d)` | `bp_bubble` |
| p. 440 | `b_t = lim_T (1/π_t) E_t[π_{t+T} p_{t+T}]` | `eq_13_6_bubble_limit` |
| p. 440 | `0 < b_t ≤ p_t` (corrected to `0 ≤ b_t ≤ p_t`) | `eq_13_6_bubble_bounds`, `eq_13_6_bubble_pos_counterexample` |
| p. 440, (13.25) | Discounted martingale property `b_t = (1/π_t)E_t[π_{t+1}b_{t+1}]` | `eq_13_25`, `eq_13_25_iterate`, `bp_fundamental_prices` |
| p. 440 | A bubble vanishing at the root vanishes everywhere | `bp_bubble_eq_zero_of_root` |
| p. 427, Def. 13.4.1 (used in Thm 13.6.1) | Radner equilibrium with debt constraints | `BPRadnerEqm`, instance in `theorem_13_6_1_instance` |
| p. 432, (13.20) (used in proof) | `E ∑_{t≤T} π_t cⁱ_t + E π_T p_T·θⁱ_T ≤ π_0 p_0·θⁱ_{−1} + E ∑_{t≤T} π_t yⁱ_t` | `bp_eq_13_20`, `bp_pv_payoff`, `bp_pr_mul_condExp_one` |
| p. 441, (13.26) | Summed over agents, in the limit | `eq_13_26`, `bp_pv_price_root`, `bp_summable_pv_of_le` |
| p. 441, (13.27) | Strict inequality under a bubble in positive supply | `eq_13_27` |
| p. 441 | "for at least one agent `i`, `E∑π_t cⁱ_t < π_0p_0·θⁱ_{−1} + E∑π_t yⁱ_t`" | `bp_exists_agent_slack` |
| p. 440, Theorem 13.6.1 | Santos–Woodford: finite PV of aggregate endowment ⇒ no bubble on assets in positive supply | `theorem_13_6_1`, `theorem_13_6_1_instance` |
| pp. 441–442, Example 13.6.1 | Kocherlakota: `(c, θ̂, p̂)`, `p̂ = p + η/π`, `θ̂ = θp/p̂`, is an equilibrium | `example_13_6_1`, `bp_ex1361_price`, `bp_ex1361_hold`, `bp_ex1361_price_pos` |
| p. 442 | `π_t/π_{t+1} = (p̂_{t+1} + d_{t+1})/p̂_t` | `example_13_6_1_prices` |
| p. 442 | Identical budget constraints and borrowing constraints | `bp_budget_transfer`, `bp_payoff_eq`, `bp_ex1361_value`, `bp_borrowCon`, `bp_natLimit` |
| p. 442 | Transversality `lim π_t p̂_t θ̂_t = lim π_t p_t θ_t = 0` | `example_13_6_1_tvc` |
| p. 442 | The bubble component is `b_t = η/π_t` | `example_13_6_1_bubble` |
| pp. 443–444, Example 13.6.2 | Werner: `p_t = η/3` with the stated consumption and portfolios is an equilibrium | `example_13_6_2`, `bp_werner_optimal`, `bp_werner_eta_facts`, `bp_werner_adm`, `bp_alt_succ`, `bp_alt`, `bp_werner_eta`, `bp_werner_y`, `bp_werner_c`, `bp_werner_θ` |
| p. 444 | Initial endowments `y¹_0 = B + η/3`, `y²_0 = A − η/3` make the date-0 budgets hold | `bp_werner_y`, `example_13_6_2` |
| p. 444 | "The transversality condition holds" | `example_13_6_2_tvc` (form (13.40)); `example_13_6_2_tvc_21_fails` (form (13.21) fails) |
| p. 444 | `π_t = 1`, fundamental value zero, PV of aggregate endowments infinite | `example_13_6_2_prices` |
| p. 444 | Another equilibrium with `p = 0`, no trade | `example_13_6_2_autarky` |
| p. 444 | The short-sales constraint binds infinitely often | `example_13_6_2_binds` |

### §13.7 Recursive formulation

| Source | Claim | Lean |
| --- | --- | --- |
| p. 444 | `Pr(s^t) = Pr(s_t|s_{t−1}) ⋯ Pr(s_1|s_0)`; `Pr(s_{t+1}|s^t) = Pr(s_{t+1}|s_t)` | `bp_markovPr`, `bp_markovTree`, `eq_13_7_markov` |
| p. 445, (13.28)–(13.29) | Law of motion `w' = G(w, s, s')`; agent `i`'s Bellman problem and constraints | `bp_rceFeasible`, `bp_rceObj` |
| p. 445, Definition 13.7.1 | Recursive competitive equilibrium with debt constraints | `BPRCE`, `definition_13_7_1_instance` |
| p. 445 | Market clearing forces aggregate wealth = value of trees (justifies restricting (ii)) | `bp_rce_walras` |
| p. 446 | One agent's wealth can be removed from the state using market clearing | `bp_rce_aggregate_wealth` |
| p. 446 | Complete markets: wealth distribution can be dropped; existence may fail (Kubler–Schmedders) | Not formalised (discussion, no derivation) |

### §13.8 Asset pricing

| Source | Claim | Lean |
| --- | --- | --- |
| p. 446 | Conditional moments at a node | `bp_E`, `bp_Cov`, `bp_Var`, `bp_sd`, `bp_E_add`, `bp_E_sub`, `bp_E_mul_left`, `bp_E_const`, `bp_E_finsetSum`, `bp_Cov_eq_dev`, `bp_Cov_comm`, `bp_Cov_affine_left`, `bp_Cov_sub_const`, `bp_Cov_sum_left`, `bp_Var_nonneg`, `bp_Cov_sq_le` |
| p. 446, (13.30) | `p_j = E[M f_j]` ⇒ `E[M R_j] = 1` | `eq_13_30` |
| p. 446 | `R_f = 1/E[M]` | `bp_riskfree` |
| p. 447 | `E[(R_j − R_f) M] = 0` | `bp_excess` |
| p. 447, (13.31) | `E[R_j − R_f] = −Cov(M, R_j − R_f)/E[M]` | `eq_13_31` |
| p. 447 | `Cov ≥ −σσ` and the Hansen–Jagannathan bound `σ(M)/E[M] ≥` Sharpe ratio | `bp_cov_ge_neg_sd`, `bp_hansen_jagannathan` |
| p. 447 | The tightest bound uses the highest Sharpe ratio | Not formalised (remark) |
| p. 448, CAPM | `E[R_m − R_f] = −bVar(R_m)/E[M]`, `E[R_j − R_f] = −bCov(R_m, R_j)/E[M]` | `bp_capm_market`, `bp_capm_asset` |
| p. 448, CAPM | `E[R_j − R_f] = β_j E[R_m − R_f]` (corrected beta) | `bp_capm`, `bp_capm_book_beta_counterexample`, `bp_half` |
| pp. 448–449, (13.32) | Factor pricing: `−Cov(M, R_j − R_f) = −∑ b_k Cov(F_k, R_j) = …` | `eq_13_32_cov` |
| p. 449 | `E[R_j − R_f] = ∑_k β_{jk}λ_k` | `bp_factor_pricing` |
| p. 449, CCAPM | Euler equation of the representative agent (from optimality) and the SDF `M = βu'(C')/u'(C)` | `bp_ccapm_euler`, `bp_ccapm_sdf` |
| pp. 449–450, (13.33) | `r_f = −E m − σ_m²/2` | `eq_13_33`, `bp_integral_exp_gaussian`, `bp_euler_gaussian`, `bp_mean_gaussian`, `bp_var_gaussian`, `bp_memLp_gaussian`, `bp_integrable_id_gaussian` |
| p. 450, (13.34) | `E[r_j − r_f] + σ_j²/2 = −σ_{jm}` | `eq_13_34` |
| p. 450 | `m = ln β − γΔc` | `bp_ccapm_log_sdf`, `bp_ccapm_m_law` |
| p. 450, (13.35) | `r_f = −ln β + γg − γ²σ_c²/2` | `eq_13_35`, `bp_rf` |
| pp. 450–451 | `r_f` falls with `β`, rises with `g`, falls with `σ_c²` | `eq_13_35_beta`, `eq_13_35_growth`, `eq_13_35_risk` |
| p. 450, (13.36) | Equity premium `= γσ_{jc}` (corrected to `γσ_c Cov(r_j, ε)`) | `eq_13_36`, `eq_13_36_counterexample` |
| p. 451 | Equity premium and riskfree rate puzzles | Not formalised (empirical discussion) |

### §13.9 Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| p. 453, Exercise 13.5 | Kocherlakota: continuum of equilibria indexed by `η` (CRRA, zero supply) | `ex_13_5`, `ex_13_5_continuum`, `ex_13_5_share_counterexample`; objects `bp_k5_Y`, `bp_k5_defl`, `bp_k5_price`, `bp_k5_wealth`, `bp_k5_share`, `bp_k5_cons`, `bp_k5_value`, `bp_k5_hold`; lemmas `bp_k5_Y_pos`, `bp_k5_defl_pos`, `bp_k5_defl_zero`, `bp_k5_marginal`, `bp_k5_prices`, `bp_k5_summable_y`, `bp_k5_pv_pos`, `bp_k5_share_sum`, `bp_k5_pv_cons`, `bp_k5_value_tail` |
| p. 453, Exercise 13.6 | `θ_{−1} = 0`, `d = 0`: continuum with `q_t = η/π_t`, the book's formulas | `ex_13_6`, `ex_13_6_formulas` |
| p. 453, Exercise 13.6 | The equilibrium with `q_t = 0` | `ex_13_6_autarky` |
| p. 453, Exercise 13.6 | The allocation is Pareto optimal | `ex_13_6_pareto`, `bp_detParetoOptimal` |
| p. 454, Exercise 13.7 | Kocherlakota 2008: `q = βPr`, `p^f = βd/(1 − β)` support the equilibrium with `D = y/(1−β)` | `ex_13_7`, `bp_k08Budget`, `bp_k08U`, `bp_k08_geom` |
| p. 454, Exercise 13.7 | With `D̂ = y/(1−β) − b`, `b_t = βE_t b_{t+1}`: equilibrium with `p = p^f + b` | `ex_13_7_bubble`, `ex_13_7_prices`, `bp_k08_martingale` |
| p. 454, Exercise 13.9 | Log utility: wealth portfolio price and return; `M = 1/R_w` | `ex_13_9_wealth`, `ex_13_9_sdf` |
| p. 454, Exercise 13.9 | Derive the CAPM (exact with two states; fails in general) | `ex_13_9_capm_two_states`, `ex_13_9_capm_counterexample`, `bp_third` |
| p. 454, Exercise 13.10 | Static CCAPM, exponential utility, normal returns: `E[R_j] − R_f = αCov(C, R_j)` and the CAPM | `ex_13_10_pricing`, `ex_13_10_capm`, `bp_gaussian_stein`, `bp_integrableExpSet_gaussian` |

### Shared machinery

| Source | Claim | Lean |
| --- | --- | --- |
| §13.1 | Event tree, node sums, conditional expectations, tower property, iterated expectations | `BPTree`, `bp_nodeSum`, `bp_condExp`, `bp_pv`, `bp_detTree`, `bp_nodeSum_zero`, `bp_nodeSum_succ`, `bp_nodeSum_congr`, `bp_nodeSum_add`, `bp_nodeSum_smul`, `bp_nodeSum_neg`, `bp_nodeSum_sub`, `bp_nodeSum_finsetSum`, `bp_nodeSum_const`, `bp_nodeSum_mono`, `bp_nodeSum_nonneg`, `bp_nodeSum_eq_zero_iff`, `bp_nodeSum_single`, `bp_nodeSum_succ_mono`, `bp_condExp_zero`, `bp_condExp_succ`, `bp_condExp_add`, `bp_condExp_congr`, `bp_condExp_add_fun`, `bp_condExp_smul`, `bp_condExp_sub_fun`, `bp_condExp_const`, `bp_condExp_mono`, `bp_condExp_nonneg`, `bp_condExp_finsetSum`, `bp_nodeSum_condExp`, `bp_condExp_root`, `bp_pv_add`, `bp_pv_mono`, `bp_pv_nonneg`, `bp_pv_finsetSum` |
| Def. 13.4.1 (deterministic) | Deterministic one-asset economy, budget set, equilibrium, utility | `bp_detBudget`, `BPDetEqm`, `bp_detU`, `bp_detAdm`, `bp_tail`, `bp_tail_succ`, `bp_sum_add_tail`, `bp_tail_tendsto`, `bp_tail_nonneg` |
| Examples 13.6.1–13.6.2, Ex. 13.5–13.6 | Euler–Kuhn–Tucker sufficiency; log and CRRA supergradients | `bp_det_partial`, `bp_det_sufficiency`, `bp_log_supergradient`, `bp_rpow_sub_one_div_le`, `bp_crra_supergradient`, `bp_crra_mono`, `bp_crra` |
