# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 4, "Optimal Stopping" (pp. 105–127). Result, equation and exercise
numbers are the book's; page numbers are book pages. Lean names are relative
to `SargentStachurski.OptimalStopping`. Where the Lean statement adds a
hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## Earlier-chapter facts restated (Basics)

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, p. 71, p. 31 | Markov matrices; distributions | `IsMarkov`, `IsDistribution` |
| Vol. 1, (3.12), Ex 2.2.27, Ex 3.2.1 | `(Ph)(x) = ∑ h(x')P(x, x')`; `f ≤ g ⇒ Pf ≤ Pg`; `P𝟙 = 𝟙`; `|Ph(x)| ≤ ‖h‖` | `mulVec_apply_eq`, `IsMarkov.mulVec_le_mulVec`, `IsMarkov.mulVec_const`, `IsMarkov.abs_mulVec_le`, `IsMarkov.norm_mulVec_le`, `IsMarkov.abs_mulVec_sub_le` |
| Vol. 1, p. 22, (1.17), Thm 1.2.3 | Global stability; contractions; uniqueness, rate, convergence, existence, global stability on the whole space | `GloballyStable`, `IsContractionOn`, `IsContractionOn.fixedPt_unique`, `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt`, `IsContractionOn.exists_fixedPt`, `IsContractionOn.globallyStable_univ` |
| Vol. 1, Prop 2.2.7 | `S ≤ T`, `T` order preserving with convergent iterates `⇒` fixed points of `S` lie below the limit | `fixedPt_le_of_le` |
| Vol. 1, Ex 2.2.30, (2.9), p. 93, Ex 3.2.4 | Increasing functions are closed; stochastic dominance; monotone Markov operators and their characterisation | `isClosed_monotone`, `FOSD`, `MonotoneIncreasing`, `monotoneIncreasing_iff` |

## §4.1.1 Theory (pp. 105–111)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 106 | A stopping problem `S = (β, P, c, e)`; policies `σ : X → {0, 1}` | `StoppingProblem`, `Policy` |
| Example 4.1.1, p. 106 | IID job search as a stopping problem | `StoppingProblem.iidJobSearch` |
| Example 4.1.2, p. 106 | A perpetual American call as a stopping problem | `StoppingProblem.perpetualOption` |
| (4.1), p. 107 | Optimal policy: `v_σ*(x) = max_σ v_σ(x)` | `StoppingProblem.IsOptimal`, `StoppingProblem.isOptimal_iff_vσ_eq` |
| (4.2)–(4.3), p. 107 | `v_σ(x) = σ(x)e(x) + (1 − σ(x))[c(x) + β ∑ v_σ(x')P(x, x')]` | `StoppingProblem.vσ_eq`, `StoppingProblem.vσ_of_stop`, `StoppingProblem.vσ_of_continue`, `StoppingProblem.vσ_eq_r_add` |
| p. 107 | `r_σ = σe + (1 − σ)c`, `L_σ = β(1 − σ)P` | `StoppingProblem.r`, `StoppingProblem.L`, `StoppingProblem.L_apply`, `StoppingProblem.L_nonneg`, `StoppingProblem.L_rowsum_le` |
| (4.4), p. 107 | `v_σ = (I − L_σ)⁻¹ r_σ`; the Neumann series `∑ L_σᵗ r_σ` | `StoppingProblem.isUnit_one_sub_L`, `StoppingProblem.vσ_eq_inv`, `StoppingProblem.summable_L_pow_mulVec`, `StoppingProblem.vσ_eq_tsum`, `StoppingProblem.norm_L_mulVec_le`, `StoppingProblem.norm_L_pow_mulVec_le` |
| Ex 4.1.1, p. 107 | `ρ(L_σ) < 1` | `complexify`, `specRad`, `norm_le_of_rowsum_abs_le`, `specRad_le_norm`, `StoppingProblem.norm_L_le`, `StoppingProblem.specRad_L_lt_one` |
| (4.5), p. 108 | The policy operator `T_σ`; `T_σ v = r_σ + L_σ v` | `StoppingProblem.Tσ`, `StoppingProblem.Tσ_eq` |
| Ex 4.1.2, p. 108 | `T_σ` is order preserving | `StoppingProblem.Tσ_monotone` |
| Prop 4.1.1, Ex 4.1.3, p. 108 | `T_σ` is a contraction of modulus `β`; `v_σ` its unique fixed point; iterates converge | `StoppingProblem.abs_Tσ_sub_le`, `StoppingProblem.isContractionOn_Tσ`, `StoppingProblem.vσ`, `StoppingProblem.isFixedPt_vσ`, `StoppingProblem.eq_vσ_of_isFixedPt`, `StoppingProblem.tendsto_iterate_Tσ` |
| (4.6), p. 108 | `v* = ⋁_σ v_σ` | `StoppingProblem.vstar`, `StoppingProblem.vσ_le_vstar`, `StoppingProblem.exists_vσ_eq_vstar` |
| (4.7)–(4.8), p. 109 | Bellman equation and Bellman operator `Tv = e ∨ (c + βPv)` | `StoppingProblem.T`, `StoppingProblem.T_apply`, `StoppingProblem.bellman_equation` |
| Ex 4.1.4, p. 109 | `T` is an order-preserving self-map | `StoppingProblem.T_monotone` |
| Prop 4.1.2 (i), Ex 4.1.5, p. 109 | `T` is a contraction of modulus `β` | `StoppingProblem.abs_T_sub_le`, `StoppingProblem.isContractionOn_T`, `StoppingProblem.globallyStable_T` |
| Prop 4.1.2 (ii), pp. 109–110 | The unique fixed point of `T` is `v*`; `T_σ v ≤ Tv`; a greedy `σ` has `T_σ v = Tv` | `StoppingProblem.isFixedPt_T_vstar`, `StoppingProblem.eq_vstar_of_isFixedPt`, `StoppingProblem.Tσ_le_T`, `StoppingProblem.Tσ_eq_T_of_isGreedy` |
| (4.9), p. 110 | `v`-greedy policies; the tie-stopping greedy policy | `StoppingProblem.IsGreedy`, `StoppingProblem.greedy`, `StoppingProblem.isGreedy_greedy` |
| Prop 4.1.3, p. 110 | Optimal iff `v*`-greedy; an optimal policy exists | `StoppingProblem.isOptimal_iff_isGreedy`, `StoppingProblem.isOptimal_greedy_vstar` |
| §4.1.1.7, p. 111 | Value function iteration converges to `v*` | `StoppingProblem.tendsto_iterate_T`, `StoppingProblem.norm_iterate_T_sub_vstar_le` |

## §4.1.2 Firm valuation with exit (pp. 111–114)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 111 | The firm's stopping problem; `T_σ`; `T v = s ∨ (π + βQv)` | `firmExit`, `firmExit.Tσ_apply`, `firmExit.T_apply` |
| p. 112 | `v*` unique solution of the Bellman equation; `v* = s ∨ h*`; exit when `h* ≤ s` | `firmExit.bellman_equation`, `firmExit.vstar_eq_max`, `firmExit.sigmaStar_eq_true_iff` |
| §4.1.2.2, p. 114 | `w = (I − βQ)⁻¹π = π + βQw` is the value of `σ ≡ 0`; `w ≤ v*` | `firmExit.noExitValue`, `firmExit.noExitValue_eq`, `firmExit.noExitValue_eq_inv`, `firmExit.noExitValue_le_vstar` |
| Ex 4.1.7, p. 114 | `Q ≫ 0` and `s > w(z)` somewhere `⇒ w ≪ v*` | `firmExit.noExitValue_lt_vstar` |
| Ex 4.1.8, p. 114 | `max_ℓ (pℓ^{1/2} − wℓ) = p²/(4w)`; the Bellman equation with stochastic prices | `isGreatest_profit`, `priceFirm`, `priceFirm_bellman` |

## §4.1.3 Monotonicity (pp. 114–116)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.10), p. 114 | Continuation value `h* = c + βPv*` | `StoppingProblem.hstar`, `StoppingProblem.hstar_apply` |
| Lemma 4.1.4, p. 114 | `e, c` increasing, `P` monotone `⇒ h*, v*` increasing | `StoppingProblem.monotone_T_of_monotone`, `StoppingProblem.monotone_vstar`, `StoppingProblem.monotone_hstar` |
| Example 4.1.3, p. 115 | The firm's `v*`, `h*` increasing | `firmExit.monotone_vstar_hstar` |
| Ex 4.1.9, p. 115 | `e` decreasing, `h*` increasing `⇒ σ*` decreasing | `StoppingProblem.antitone_sigmaStar` |
| Example 4.1.4, p. 115 | The firm's optimal policy is decreasing | `firmExit.antitone_sigmaStar` |
| Ex 4.1.10, p. 115 | `e` constant, `c` increasing, `P` monotone `⇒ σ*` decreasing | `StoppingProblem.antitone_sigmaStar_of_const` |
| Ex 4.1.11, p. 115 | `e` increasing, `h*` decreasing `⇒ σ*` increasing | `StoppingProblem.monotone_sigmaStar` |
| Example 4.1.5, p. 116 | IID job search: `h*` constant, `σ*` increasing | `StoppingProblem.hstar_const_of_iid`, `StoppingProblem.monotone_sigmaStar_of_iid` |
| p. 116 | A monotone policy on a totally ordered set is a threshold policy | `exists_threshold_of_monotone`, `exists_threshold_of_antitone` |

## §4.1.4 Continuation values (pp. 116–119)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.11)–(4.12), p. 117 | `v* = e ∨ h*`; `h* = c + βP(e ∨ h*)` | `StoppingProblem.vstar_eq_max_hstar`, `StoppingProblem.isFixedPt_C_hstar` |
| (4.13), Prop 4.1.5, p. 117 | `C` is a `β`-contraction with unique fixed point `h*`; `Cᵏh → h*`; `σ* = 1{e ≥ h*}` | `StoppingProblem.C`, `StoppingProblem.C_apply`, `StoppingProblem.C_monotone`, `StoppingProblem.abs_C_sub_le`, `StoppingProblem.isContractionOn_C`, `StoppingProblem.eq_hstar_of_isFixedPt`, `StoppingProblem.tendsto_iterate_C`, `StoppingProblem.sigmaStar`, `StoppingProblem.sigmaStar_eq_greedy`, `StoppingProblem.isGreedy_sigmaStar`, `StoppingProblem.isOptimal_sigmaStar`, `StoppingProblem.sigmaStar_eq_true_iff` |
| p. 118 | `P((w, z), (w', z')) = φ(w')Q(z, z')` is Markov; `(Pv)(w, z)` independent of `w` | `productKernel`, `productKernel_apply`, `isMarkov_productKernel`, `productKernel_mulVec`, `productProblem` |
| (4.14), p. 118 | The Bellman operator on `W × Z` | `productProblem.T_apply` |
| (4.15), p. 118 | The reduced continuation value operator on `ℝ^Z`; `h*(w, z) = h̃(z)` | `productProblem.reducedC`, `productProblem.reducedC_monotone`, `productProblem.isContractionOn_reducedC`, `productProblem.reducedH`, `productProblem.isFixedPt_reducedH`, `productProblem.eq_reducedH_of_isFixedPt`, `productProblem.tendsto_iterate_reducedC`, `productProblem.hstar_indep`, `productProblem.hstar_eq_reducedH`, `productProblem.sigmaStar_eq_true_iff` |
| Example 4.1.6, p. 118 | IID job search: `Z` a point, the reduced operator is Vol. 1 (1.33) | `reducedC_unit` |
| §4.1.4.3, Ex 4.1.12, p. 119 | The firm with IID scrap values; its continuation value operator on `ℝ^Z` | `scrapFirm`, `scrapFirm_reducedC` |
| Ex 4.1.13, p. 119 | `φ_a ≼_F φ_b ⇒ σ*_a ≥ σ*_b` (finite scrap distribution) | `scrapFirm_reducedC_le`, `scrapFirm_sigmaStar_ge` |

## §4.2.1 American options (pp. 119–122)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 120 | Dates `{1, …, T + 1}`, `m(t) = min{t + 1, T + 1}`; the model's data | `AmericanOption`, `AmericanOption.Time`, `AmericanOption.next`, `AmericanOption.alive`, `AmericanOption.next_of_alive`, `AmericanOption.next_of_not_alive`, `AmericanOption.next_next_of_last`, `AmericanOption.β_pos`, `AmericanOption.β_lt_one` |
| p. 120 | `P((t, w, z), (t', w', z')) = 1{t' = m(t)}φ(w')Q(z, z')` | `AmericanOption.timeKernel`, `AmericanOption.isMarkov_timeKernel`, `AmericanOption.timeKernel_mulVec`, `AmericanOption.problem`, `AmericanOption.problem_P`, `AmericanOption.problem_mulVec` |
| p. 121 | Exit reward `1{t ≤ T}(z + w − K)`; the Bellman equation | `AmericanOption.e`, `AmericanOption.bellman_equation` |
| (4.16), p. 121 | The continuation value operator on `ℝ^{T × Z}`; `Cᵏh → h*`; `σ*(t, w, z) = 1{e ≥ h*(t, z)}`; optimality | `AmericanOption.reducedC_apply`, `AmericanOption.hstar`, `AmericanOption.hstar_eq`, `AmericanOption.tendsto_iterate_reducedC`, `AmericanOption.sigmaStar_eq_true_iff`, `AmericanOption.isOptimal_sigmaStar` |
| p. 122 | The exercise region expands with `t` | `AmericanOption.vstar_nonneg_antitone`, `AmericanOption.hstar_antitone`, `AmericanOption.exercise_region_expands` |

## §4.2.2 Research and development (pp. 122–126)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.17), p. 125 | Constant costs: the stopping problem and its Bellman equation | `rdConstant`, `rdConstant.bellman_equation` |
| Ex 4.2.1, p. 125 | The continuation value operator; `h*` increasing when `π` is and `P` is monotone | `rdConstant.C_apply`, `rdConstant.monotone_hstar` |
| Ex 4.2.2, p. 125 | `σ*` increasing when `π` is increasing and `(Xₜ)` is IID | `rdConstant.monotone_sigmaStar` |
| (4.18), p. 125 | IID costs: the problem on `(c, x)` and its Bellman equation | `rdIID`, `rdIID.bellman_equation` |
| (4.19)–(4.20), p. 126 | The expected value function `g`; `v* = max{π, −c + βg}`; `g = Rg` | `rdIID.g`, `rdIID.vstar_eq`, `rdIID.R`, `rdIID.isFixedPt_R_g` |
| Ex 4.2.3, p. 126 | `R` is a `β`-contraction; `g*` unique, computable by successive approximation; `σ*(c, x) = 1{π(x) ≥ −c + βg*(x)}` | `rdIID.isContractionOn_R`, `rdIID.eq_g_of_isFixedPt`, `rdIID.tendsto_iterate_R`, `rdIID.sigmaStar_eq_true_iff` |
