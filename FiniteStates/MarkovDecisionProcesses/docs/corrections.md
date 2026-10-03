# Corrections to the source

Places where a claim in Chapter 5 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In
each case the Lean statement proves the stated version and cites the
original. Entries are recorded when found and revised if formalisation shows
the finding itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| §5.3.2, p. 167 | The Gumbel distribution with mode `μ` has CDF `F(z) = exp(−exp(z − μ))`. | That function is decreasing in `z`, so it is not a distribution function. The Gumbel CDF is `exp(−exp(−(z − μ)))`; `gumbelCDF` uses the corrected sign, and Exercise 5.3.2 is proved for it (`gumbelCDF_shift`, `gumbelCDF_monotone`). |
| (5.33)–(5.35), p. 165 | The shock space `E` "is allowed to be continuous" and the operator integrates against a density. | Formalised for a finite shock space with a distribution `φ`, the discretised form in which, as the book says, "all the optimality theory for MDPs applies"; sums replace integrals. Exercise 5.3.1 and Proposition 5.3.1 are proved in that setting (`Structural`). The feasible set is allowed to depend on the shock, `Γ(y, ε)`, which §5.3.3 needs. |
| Prop 5.3.3, p. 167 | Proof: "straightforward algebra shows `R(g + c) = Rg + βc`"; Blackwell's condition. | Proved exactly that way (`gumbelR_add_const`, `isContractionOn_gumbelR`); the derivation of (5.36) from Lemma 5.3.2 (the expected maximum of Gumbel shocks) is probabilistic and not formalised, so the operator (5.36) is taken as the definition. |
| (5.13), p. 133 | The maximisation in the cake-eating Bellman equation is printed over `0 ≤ w' ≤ w` (garbled in the text). | The no-borrowing constraint `c = w − w'/R ≥ 0` is `w' ≤ Rw`, consistent with `Γ(w, y) = {s : s ≤ R(w + y)}` on p. 149; that is the feasible set used (`cakeEating`). |
| Ex 5.1.2, p. 132 | Write the inventory kernel using only `x, a, x'` and the parameters. | For feasible `a ≤ K − x`: `P(x, a, x') = (1 − p)ˣ` if `x' = a`, `p(1 − p)^{x+a−x'}` if `a < x' ≤ x + a`, else `0` (`inventoryKernel_eq`). For infeasible pairs the update is clamped at `K` so that every row is a distribution; those rows never enter the theory. |
| Prop 5.1.1 (iv), Ex 5.1.13, p. 139 | "(iii) implies (iv)". | Proved with the explicit witness: any `v*`-greedy policy, which exists by Exercise 5.1.11 (i) (`MDP.isOptimal_greedy_vstar`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 129 | `r` and `P` are defined on the feasible pairs `G` only. | `r : X → A → ℝ` and `P : X → A → X → ℝ` are given on all of `X × A`, with `P(x, a, ·)` a distribution for every `a`. Any kernel on `G` extends this way (use any distribution off `G`), the values off `G` never enter since maximisation is over `Γ(x)` and policies are feasible, and functions on `G` can then be represented as functions on `X × A`, which §5.3.5 uses. |
| (5.16), p. 134 | `Σ` is finite and nonempty, so the maximum in (5.21) exists. | `Policy` is a subtype of `X → A`, a `Fintype` under decidable equality on `X` and `A`; nonemptiness is `MDP.policy_nonempty` from `Γ(x) ≠ ∅`. `[DecidableEq X] [DecidableEq A]` appear on everything downstream of `v*`. |
| (5.17), p. 134 | `v_σ` is an expected discounted sum along the `P_σ`-chain. | `v_σ` is defined as the unique fixed point of `T_σ`, equivalently `(I − βP_σ)⁻¹ r_σ` or the series (5.18); the chain is not constructed, in keeping with Chapter 3. |
| Ex 5.1.6, p. 135 | `‖r‖_∞` is the supremum over `G`. | Any bound `R` with `|r(x, σ(x))| ≤ R` along the policy gives `|v_σ| ≤ R/(1 − β)` (`MDP.abs_vσ_le`). |
| Ex 5.1.9, p. 136 | `E_x[∑_{t<k} βᵗr(Xₜ, σ(Xₜ)) + βᵏv(X_k)]`. | Stated in matrix form, `∑_{t<k} βᵗP_σᵗ r_σ + βᵏP_σᵏ v`, the expectations being the entries of `P_σᵗ` (`MDP.iterate_Tσ_eq`). |
| Ex 5.1.10, p. 136 | The least element of `{T_σ v}`. | Attained by the policy that minimises the action value in each state (`MDP.antiGreedy`). |
| (5.22), p. 136 | Greedy policies are feasible. | `MDP.IsGreedy` includes feasibility. |
| Algorithm 5.3, p. 141 | HPI "always converges to an exact optimal policy in a finite number of steps" (proved in Chapter 8). | The two facts per step are proved: the value never falls (`MDP.vσ_le_vσ_of_isGreedy`) and if it stops changing the current policy is optimal (`MDP.isOptimal_of_hpi_fixed`). Finite termination also needs that the values strictly increase while suboptimal, which is Chapter 8's. |
| p. 144 | The subgradient (5.26) is defined for `S ⊂ ℝⁿ`. | Lemma 5.1.2 is stated on all of `ℝ^X`. |
| §5.1.2.2, p. 131 | The firm "can store at most `K` items"; `Γ(x) = {0, …, K − x}`. | States and actions are `Fin (K + 1)`; feasibility `a ≤ K − x` is `inventory_mem_Γ`. Demand is geometric with `p ∈ (0, 1)`; the reward's expected revenue and the kernel are `tsum`s over demand. |
| Ex 5.1.4, p. 133 | `W ⊂ ℝ₊` finite, `R` a gross interest rate. | Wealth values `wealth : W → ℝ`, `R : ℝ`; a feasible action must exist in every state, `∀ w, ∃ w', wealth w' ≤ R·wealth w`, which holds when `0 ∈ W`. The same for `savings`, `stochasticReturns`, `transientIncome`. |
| Ex 5.1.5, p. 134 | Employment is permanent at the accepted wage. | `jobSearchKernel`: from `(1, w)` the state stays `(1, w)`; from `(0, w)` acceptance leads to `(1, w)` and rejection draws `(0, w')` from `Q(w, ·)`; the reward is the wage when employed or accepting, `c` when rejecting. |
| §5.2.3, p. 157 | `Y` is a grid "contained in `ℝ₊`" of output values; `Γ(x) = Y` nonempty. | Output values `out : Y → ℝ`, `[Nonempty Y]`; likewise `lab` for the hiring model. |
| Ex 5.2.2, p. 156 | `a₁ > 0`. | `0 < a₁` in `investmentReward_le_at_Ybar`; the maximum is over all real `y`. |
| Ex 5.2.3, p. 160 | `ℓᵅ` with real `α`. | `Real.rpow`; the exercise's OPI procedure is the generic Algorithm 5.4. |
| §5.3.1.3, p. 165 | `E` nonempty (there is a shock). | `[Nonempty E]` where the reduced and full operators are compared (`Structural.isContractionOn_Rred`, `Structural.isFixedPt_Rred_gred`). |
| §5.3.3, p. 168 | Returns `η > 0`. | Return values `ret : Et → ℝ` are unrestricted; the reward uses `w'/η` as written. |
| §5.3.5.1, p. 172 | `M` maximises over `Γ(x)`. | `MDP.Mop` does; `E` and `D` act on all of `X × A`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| §5.1.1, (5.1) | Lifetime rewards `E ∑ βᵗ r(Xₜ, Aₜ)` as expectations along a controlled chain | The chapter's theory is stated through `P_σ` and the operators; the probabilistic construction is Volume 2 material. |
| §5.1.4.1, p. 140 | VFI's greedy policy is exactly optimal for large `k` (Theorem 8.1.1) | Chapter 8. |
| §5.1.4.2–5.1.4.4, pp. 141–145 | Finite termination of HPI, quadratic convergence (5.27) cited from Puterman, global convergence of OPI | Deferred by the book to Chapter 8 or cited; the per-step facts are proved. |
| Example 5.1.1, Figures 5.1–5.5 | Illustrations | Descriptive. |
| Ex 5.2.1, Listings 5.1–5.7, Figures 5.6–5.14 | Code, timings, simulations, histograms | Computational. |
| §5.3.1.2, p. 164 | The labour supply model of Keane et al. | Human capital `h_t = h_{t−1} + d_{t−1}` is unbounded, so the state space is infinite; the generic model (5.33) that the section abstracts from it is formalised instead. |
| Lemma 5.3.2, p. 167 | The maximum of independent Gumbel shocks plus constants is Gumbel with mode `−γ + ln ∑ exp(cᵢ)`; the mean `μ + γ` | Statements about integrals against the Gumbel density, cited from Huijben et al.; not claimed. |
| Algorithm 5.5, p. 178 | Convergence of refactored OPI | Reduces to regular OPI by `MDP.Rσ_iterate_E`, whose convergence is Chapter 8's. |
| §5.4 Chapter notes, (5.42) | Literature; the LP formulation | Not applicable. |
