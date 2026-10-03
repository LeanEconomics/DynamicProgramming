# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 5, "Markov Decision Processes" (pp. 128–181). Result, equation and
exercise numbers are the book's; page numbers are book pages. Lean names are
relative to `SargentStachurski.MarkovDecisionProcesses`. Where the Lean
statement adds a hypothesis the book leaves implicit, or departs from the
printed claim, see [corrections](corrections.md).

## Earlier-chapter facts restated (Basics)

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, p. 71, Ex 2.3.2 | Markov matrices, products, powers, distributions | `IsMarkov`, `IsMarkov.mul`, `IsMarkov.pow`, `IsDistribution` |
| Vol. 1, (3.12), Ex 2.2.27, Ex 3.2.1 | `(Ph)(x)`, `f ≤ g ⇒ Pf ≤ Pg`, `P𝟙 = 𝟙`, `|Ph(x)| ≤ ‖h‖` | `mulVec_apply_eq`, `IsMarkov.mulVec_le_mulVec`, `IsMarkov.mulVec_const`, `IsMarkov.abs_mulVec_le`, `IsMarkov.norm_mulVec_le`, `IsMarkov.abs_mulVec_sub_le` |
| Vol. 1, p. 22, (1.17), Thm 1.2.3 | Global stability, contractions, Banach's theorem | `GloballyStable`, `IsContractionOn`, `IsContractionOn.fixedPt_unique`, `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt`, `IsContractionOn.exists_fixedPt`, `IsContractionOn.globallyStable_univ` |
| Vol. 1, Prop 2.2.7 | Ordered operators have ordered fixed points; `u ≤ Tu ⇒ u ≤ u*` | `fixedPt_le_of_le`, `le_fixedPt_of_le_apply` |
| Vol. 1, Lemma 2.2.4, Lemma 2.2.2 | Blackwell's condition; `|max f − max g| ≤ max |f − g|` | `isContractionOn_of_blackwell`, `abs_sup'_sub_sup'_le` |

## §5.1.1 The MDP model (pp. 128–130)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 129 | `M = (Γ, β, r, P)`; feasible pairs `G`; `P(x, a, ·) ∈ D(X)` | `MDP`, `MDP.Feasible`, `MDP.isDistribution_P` |
| (5.2), p. 129 | The Bellman equation | `MDP.bellman_equation` (in `Bellman`) |

## §5.1.2 Examples (pp. 130–134)

| Book | Claim | Lean |
| --- | --- | --- |
| (5.3)–(5.4), p. 130 | The renewal problem; its kernel | `renewalKernel`, `renewal` |
| Ex 5.1.1, p. 131 | The renewal kernel is stochastic | `renewalKernel_nonneg`, `renewalKernel_rowsum` |
| p. 131 | (5.3) is the MDP Bellman equation (5.2) | `renewal_bellman`, `sup'_bool` |
| (5.5)–(5.9), pp. 131–132 | Inventory dynamics, feasible orders, reward, kernel | `inventoryNext`, `inventoryNext_of_feasible`, `geomPmf`, `tsum_geomPmf`, `expectedRevenue`, `inventoryReward`, `inventoryKernel`, `inventoryKernel_nonneg`, `inventoryKernel_rowsum`, `inventory`, `inventory_mem_Γ` |
| Ex 5.1.2, p. 132 | The kernel (5.9) for geometric demand in closed form | `tsum_geomPmf_tail`, `inventoryKernel_eq` |
| (5.11)–(5.12), Ex 5.1.3, p. 132 | The inventory Bellman operator is a `β`-contraction | `MDP.isContractionOn_T` applied to `inventory` |
| (5.13), Ex 5.1.4, p. 133 | Cake eating as an MDP; its Bellman equation | `detKernel`, `detKernel_nonneg`, `detKernel_rowsum`, `sum_mul_detKernel`, `cakeEating`, `cakeEating_bellman` |
| Ex 5.1.5, p. 134 | Job search with Markov wages as an MDP on `{0, 1} × W`; the Bellman equation of Vol. 1 (3.23) | `jobSearchKernel`, `jobSearchKernel_nonneg`, `jobSearchKernel_rowsum`, `jobSearch`, `jobSearch.sum_mul_kernel_stay`, `jobSearch.sum_mul_kernel_reject`, `jobSearch.vstar_employed`, `jobSearch.vstar_unemployed` |

## §5.1.3 Optimality (pp. 134–139)

| Book | Claim | Lean |
| --- | --- | --- |
| (5.16), p. 134 | Feasible policies `Σ`; `P_σ ∈ M(ℝ^X)`; `r_σ` | `MDP.IsFeasible`, `MDP.Policy`, `MDP.defaultPolicy`, `MDP.policy_nonempty`, `MDP.Pσ`, `MDP.isMarkov_Pσ`, `MDP.rσ` |
| (5.17)–(5.18), pp. 134–135 | `v_σ = ∑ βᵗP_σᵗ r_σ = (I − βP_σ)⁻¹ r_σ` | `MDP.vσ`, `MDP.vσ_eq`, `MDP.isUnit_one_sub_smul_Pσ`, `MDP.vσ_eq_inv`, `MDP.summable_pow_smul_mulVec`, `MDP.vσ_eq_tsum` |
| Ex 5.1.6, p. 135 | `−‖r‖/(1 − β) ≤ v_σ ≤ ‖r‖/(1 − β)` | `MDP.abs_vσ_le` |
| (5.19)–(5.20), p. 135 | The policy operator `T_σ v = r_σ + βP_σ v` | `MDP.B`, `MDP.Tσ`, `MDP.Tσ_apply`, `MDP.Tσ_eq` |
| Ex 5.1.7, p. 135 | `T_σ` order preserving, a `β`-contraction, `v_σ` its unique fixed point, `T_σᵏv → v_σ` | `MDP.Tσ_monotone`, `MDP.abs_Tσ_sub_le`, `MDP.isContractionOn_Tσ`, `MDP.isFixedPt_vσ`, `MDP.eq_vσ_of_isFixedPt`, `MDP.tendsto_iterate_Tσ` |
| Ex 5.1.8, p. 135 | `T_σᵏ 0 = ∑_{t<k} βᵗP_σᵗ r_σ` | `MDP.iterate_Tσ_zero` |
| Ex 5.1.9, p. 136 | `T_σᵏ v` is the `k`-period payoff with terminal value `v` | `MDP.iterate_Tσ_eq` |
| (5.21), p. 136 | `v* = ⋁_σ v_σ`; optimal policies | `MDP.vstar`, `MDP.vσ_le_vstar`, `MDP.IsOptimal`, `MDP.isOptimal_iff` |
| (5.22), p. 136 | `v`-greedy policies | `MDP.IsGreedy`, `MDP.greedy`, `MDP.greedy_mem`, `MDP.greedyPolicy` |
| Ex 5.1.10, p. 136 | `{T_σ v}` has least and greatest elements | `MDP.isGreatest_T`, `MDP.antiGreedy`, `MDP.isLeast_Tσ_antiGreedy` |
| (5.24), p. 137 | The Bellman operator | `MDP.T`, `MDP.T_apply`, `MDP.B_le_T`, `MDP.Tσ_le_T`, `MDP.T_monotone` |
| Ex 5.1.11, p. 137 | (i) greedy policies exist; (ii) greedy iff `T_σ v = Tv`; (iii) `T = ⋁_σ T_σ` | `MDP.isGreedy_greedy`, `MDP.isGreedy_iff_Tσ_eq_T`, `MDP.Tσ_eq_T_of_isGreedy`, `MDP.T_apply_eq_sup'` |
| Ex 5.1.12, p. 137 | `T` is a `β`-contraction | `MDP.abs_B_sub_le`, `MDP.isContractionOn_T`, `MDP.globallyStable_T` |
| Prop 5.1.1, pp. 137–139 | (i) `v*` the unique solution of the Bellman equation; (ii) `Tᵏv → v*`; (iii) optimal iff `v*`-greedy, (5.25); (iv) an optimal policy exists (Ex 5.1.13) | `MDP.isFixedPt_T_vstar`, `MDP.eq_vstar_of_isFixedPt`, `MDP.bellman_equation`, `MDP.tendsto_iterate_T`, `MDP.norm_iterate_T_sub_vstar_le`, `MDP.isOptimal_iff_isGreedy`, `MDP.isOptimal_greedy_vstar`, `MDP.exists_isOptimal` |

## §5.1.4 Algorithms (pp. 139–145)

| Book | Claim | Lean |
| --- | --- | --- |
| Algorithm 5.2, p. 140 | VFI converges to `v*` | `MDP.tendsto_iterate_T` |
| Algorithm 5.3, p. 141 | HPI: the improvement step `v_σ ≤ v_σ'`; termination gives an optimal policy | `MDP.vσ_le_vσ_of_isGreedy`, `MDP.isOptimal_of_hpi_fixed` |
| (5.26), Lemma 5.1.2, p. 144 | `βP_σ` is a subgradient of `T` at `v` for `v`-greedy `σ` | `MDP.subgradient_of_isGreedy` |
| p. 144 | The Newton step `(I − βP_σ)⁻¹(Tv − βP_σ v) = (I − βP_σ)⁻¹ r_σ = v_σ` | `MDP.newton_step_eq_vσ` |
| Algorithm 5.4, p. 145 | OPI: `m = 1` is VFI; `T_σᵐ v → v_σ` | `MDP.opi_one_step_eq_vfi`, `MDP.tendsto_opi_inner` |

## §5.2 Applications (pp. 145–161)

| Book | Claim | Lean |
| --- | --- | --- |
| §5.2.1, p. 146 | The inventory MDP, Prop 5.1.1 applies | `inventory` with `MDP.isOptimal_iff_isGreedy` |
| §5.2.2.1, p. 149 | Savings: `Γ(w, y) = {s ≤ R(w + y)}`, `r = u(w + y − s/R)`, `P = 1{w' = s}Q(y, y')` | `choiceKernel`, `choiceKernel_nonneg`, `choiceKernel_rowsum`, `sum_mul_choiceKernel`, `savings`, `savings.mem_Γ` |
| (5.29)–(5.30), pp. 149–150 | The savings Bellman and policy operators; `P_σ`, `r_σ` | `savings.T_apply`, `savings.Tσ_apply`, `savings.Pσ_apply`, `savings.rσ_apply` |
| §5.2.3, pp. 156–157 | Investment: profit, (5.32), the MDP, its Bellman operator | `investmentReward`, `investment`, `investment_T_apply` |
| Ex 5.2.2, p. 156 | `Ȳ = (a₀ − c + z)/(2a₁)` maximises current profit when `γ = 0` | `investmentReward_le_at_Ybar` |
| Ex 5.2.3, p. 160 | The hiring model is an MDP; its Bellman equation | `hiringReward`, `hiring`, `hiring_bellman` |

## §5.3 Modified Bellman equations (pp. 162–178)

| Book | Claim | Lean |
| --- | --- | --- |
| (5.33), p. 165 | The structural model as an MDP on `Y × E` | `Structural`, `Structural.toMDP` |
| (5.34), p. 165 | The expected value function depends on `(y, a)` only | `Structural.E_toMDP`, `Structural.Ered`, `liftEV`, `Structural.E_toMDP_eq_lift` |
| (5.35), p. 166 | The expected value Bellman operator | `Structural.Rred`, `Structural.R_lift` |
| Ex 5.3.1, p. 166 | `R` is order preserving and a `β`-contraction | `Structural.Rred_monotone`, `norm_liftEV_sub_le`, `norm_le_norm_liftEV`, `Structural.isContractionOn_Rred` |
| p. 166 | `g*` the fixed point of `R`, by successive approximation; `v* = max{r + βg*}` | `Structural.gred`, `Structural.gstar_eq_lift`, `Structural.isFixedPt_Rred_gred`, `Structural.eq_gred_of_isFixedPt`, `Structural.tendsto_iterate_Rred`, `Structural.vstar_eq` |
| Prop 5.3.1, p. 166 | Optimal iff `σ(y, ε) ∈ argmax {r(y, ε, a) + βg*(y, a)}` | `Structural.isOptimal_iff` |
| p. 167, Ex 5.3.2 | The Gumbel CDF (sign corrected); `Z ∼ G(μ) ⇒ Z + λ ∼ G(μ + λ)` | `gumbelCDF`, `gumbelCDF_monotone`, `gumbelCDF_shift` |
| (5.36), Prop 5.3.3, p. 167 | The log-sum-exp operator is a `β`-contraction | `gumbelR`, `logSumExp_mono`, `logSumExp_add_const`, `gumbelR_monotone`, `gumbelR_add_const`, `isContractionOn_gumbelR` |
| §5.3.3, pp. 168–169 | Stochastic returns: the MDP, (5.37), the Bellman equation and its expected value form, `R_σ` | `stochasticReturns`, `stochasticReturns.Ered_apply`, `stochasticReturns.bellman_equation`, `stochasticReturns.gred_eq`, `Structural.Rσ_lift` |
| Ex 5.3.3, p. 169 | Transient and persistent income: both Bellman equations | `transientIncome`, `transientIncome.bellman_equation`, `transientIncome.gred_eq` |
| (5.39), Ex 5.3.4, p. 171 | The Q-factor Bellman operator is order preserving and a `β`-contraction | `MDP.S`, `MDP.S_apply`, `MDP.S_monotone`, `MDP.isContractionOn_S` |
| Prop 5.3.4, p. 172 | Optimal iff `σ(x) ∈ argmax q*(x, a)` | `MDP.qstar`, `MDP.IsQGreedy`, `MDP.isOptimal_iff_isQGreedy` |
| p. 172, (5.40) | `E`, `D`, `M`; `T = MDE`, `R = EMD`, `S = DEM` | `MDP.E`, `MDP.D`, `MDP.Mop`, `MDP.D_E`, `MDP.T_eq_Mop_D_E`, `MDP.R` |
| Ex 5.3.5, p. 173 | Explicit `R` and `S` | `MDP.R_apply`, `MDP.S_apply` |
| Ex 5.3.6, p. 174 | `Rᵏ = ETᵏ⁻¹MD = EMSᵏ⁻¹D`, `Sᵏ = DRᵏ⁻¹EM = DETᵏ⁻¹M`, `Tᵏ = MSᵏ⁻¹DE = MDRᵏ⁻¹E` | `MDP.R_iterate_succ`, `MDP.R_iterate_succ'`, `MDP.S_iterate_succ`, `MDP.S_iterate_succ'`, `MDP.T_iterate_succ`, `MDP.T_iterate_succ'` |
| Ex 5.3.7, p. 174 | `E`, `M` nonexpansive, `D` a `β`-contraction | `MDP.norm_E_sub_le`, `MDP.norm_Mop_sub_le`, `MDP.norm_D_sub_le`, `MDP.E_monotone`, `MDP.D_monotone`, `MDP.Mop_monotone`, `MDP.R_monotone` |
| Lemma 5.3.5, p. 174 | `R`, `S`, `T` are `β`-contractions | `MDP.isContractionOn_R`, `MDP.isContractionOn_S`, `MDP.norm_T_sub_le` |
| Prop 5.3.6, p. 175 | `g* = Ev*`, `q* = Dg*`, `v* = Mq*`, and their explicit forms | `MDP.gstar`, `MDP.isFixedPt_R_gstar`, `MDP.eq_gstar_of_isFixedPt`, `MDP.isFixedPt_S_qstar`, `MDP.eq_qstar_of_isFixedPt`, `MDP.vstar_eq_Mop_qstar`, `MDP.gstar_apply`, `MDP.qstar_apply`, `MDP.vstar_apply_eq_sup'_qstar`, `MDP.tendsto_iterate_R`, `MDP.tendsto_iterate_S` |
| p. 175, Cor 5.3.7, p. 176 | `g`-greedy, `q`-greedy; `v*`-greedy ⟺ `g*`-greedy ⟺ `q*`-greedy ⟺ optimal | `MDP.IsGGreedy`, `MDP.isGreedy_iff_isGGreedy_E`, `MDP.isGGreedy_iff_isQGreedy_D`, `MDP.isGreedy_vstar_iff_isGGreedy_gstar`, `MDP.isGGreedy_gstar_iff_isQGreedy_qstar`, `MDP.isOptimal_iff_isGGreedy` |
| p. 177 | `M_σ`; `R_σ = EM_σD`, `S_σ = DEM_σ`, `T_σ = M_σDE` | `MDP.Mσ`, `MDP.Tσ_eq_Mσ_D_E`, `MDP.Rσ`, `MDP.Sσ` |
| Ex 5.3.8, (5.41), p. 177 | `R_σᵏ = ET_σᵏ⁻¹M_σD` | `MDP.Rσ_iterate_succ`, `MDP.Sσ_iterate_succ` |
| Algorithm 5.5, p. 178 | Refactored OPI: `g_{k+1} = R_σᵐ g_k` with `g_k = Ev_k` gives `g_{k+1} = Ev_{k+1}`; the same policies are selected | `MDP.Rσ_iterate_E`, `MDP.isGGreedy_E_iff` |
