# Source map: Miao Chapter 20

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 20, Recursive
Utility, pp. 675–736. Lean names are relative to `Miao.RecursiveUtility`. Page references are the
draft's running heads. The stochastic parts are on finite event trees or finite-state Markov paths;
lognormal results use Mathlib's `gaussianReal`. `SS.` names are Sargent–Stachurski's, copied.
Departures from the book are in [corrections](corrections.md).

## §§20.1–20.2.1 and Exercise 20.1

### Part IV and Chapter 20 introductions

| Source | Claim | Lean |
| --- | --- | --- |
| p. 673 | Part IV introduction (dynamic programming squared) | not formalised: description of later chapters, no mathematical claim |
| p. 675 | With time-additive utility the MRS at constant consumption is `1/β`, independent of the level | `ku_intro_partial`, `ku_intro_mrs_const` |
| p. 675 | With a fixed interest rate the consumer saves or borrows without limit except when `βR = 1` | `ku_intro_knife_edge`, `ku_intro_growth` |
| p. 675 | Becker (1980): the most patient household owns all capital | not formalised: cited result, not derived |
| p. 676 | Time-additive power utility: EIS `= 1/`RRA | `ku_intro_rra`, `ku_intro_eis` |
| p. 676 | The coin example: indifference to the timing of resolution | `ku_intro_timing` |
| pp. 676–677 | Equity premium, Ellsberg and Allais motivation | not formalised: narrative (Allais is formalised on p. 687) |

### §20.1.1 Koopmans's utility (pp. 677–679)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 677 | Streams, `₁c`, `ₜc`, the space `L` of bounded streams in `ℝˡ₊` | `ku_shift`, `ku_tail`, `ku_cons`, `ku_bddSeq`, `ku_bddSeq_closed`, `ku_cons_zero`, `ku_shift_cons`, `ku_cons_shift`, `ku_tail_zero`, `ku_tail_succ` |
| (20.1), p. 678 | Recursive utility representation `U(c) = W(u(c₀), U(₁c))` | `ku_Represents`, `eq_20_1` |
| p. 678 | Example: time-additive utility | `eq_20_1_additive` |
| p. 678 | Axioms (K1)–(K3) | `ku_K1`, `ku_K2`, `ku_K3` |
| p. 678 | "Any preference order with a recursive representation satisfies Koopmans's Axioms" (corrected) | `ku_K1_of_recursive`, `ku_K2_of_recursive`, `ku_K3_iff_of_recursive`; counterexamples `ku_K1_counterexample`, `ku_K3_counterexample`, `ku_const_mem_bddSeq` |
| p. 678 | Koopmans (1960): (K1)–(K3) give (20.1); ordinal uniqueness | `ku_koopmans_1960`, `ku_ordinal_unique` |
| Definition 20.1.1, p. 678 | Dynamic consistency | `definition_20_1_1` |
| p. 678 | "Axiom (K1) ensures dynamic consistency" | `ku_dynConsistent_of_K1`, `ku_dynConsistent_of_recursive` |
| p. 678 | Subjective discount factor `β(x) = ∂W/∂U` at `(x, x, …)` | `ku_IsSubjDiscount` |
| p. 679 | EIS `= d ln(c_s/c_t)/d ln MRS_{s,t}` | defined through Example 20.1.2: `example_20_1_2`, `example_20_1_2_misprint` |
| Example 20.1.1, p. 679 | Uzawa: discount factor `β(u(c₀))`; Epstein–Hynes: `β(c₀)` | `example_20_1_1`, `example_20_1_1_epstein_hynes`; existence `example_20_1_1_exists` |
| Example 20.1.2, p. 679 | CES aggregator: discount factor `β` | `ku_ces`, `ku_ces_pos`, `ku_ces_rpow`, `ku_ces_hasDerivAt_x`, `ku_ces_hasDerivAt_y`, `example_20_1_2_const`, `example_20_1_2_discount` |
| Example 20.1.2, p. 679 | CES aggregator: MRS and EIS `= 1/ρ` | `ku_shift_update_zero`, `ku_shift_update_succ`, `example_20_1_2_mrs`, `example_20_1_2`, `example_20_1_2_misprint` |

### §20.1.2 Construction (pp. 679–683)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 680 | `C(L)`, the operator `T_W f(c) = W(c₀, f(₁c))`, (W1)–(W4) | `ku_TW`, `ku_TW_continuous`; (W1)–(W4) are hypotheses of `theorem_20_1_1*` |
| Theorem 20.1.1, p. 680 | `T_W` has a unique fixed point, the unique solution of `U(c) = W(c₀, U(₁c))` | `theorem_20_1_1` (on `ku_Lθ 1 K`, `ku_seqθ_one`) |
| Theorem 20.1.1, p. 680 | (W3) ⇒ `U` increasing | `theorem_20_1_1_mono`, `ku_TW_monotone` |
| Theorem 20.1.1, p. 680 | (W3)–(W4) ⇒ `U` concave | `theorem_20_1_1_concave`, `ku_TW_concave`, `ku_ConcaveS`, `ku_concaveS_of_tendsto` |
| p. 680 | `W(x, y) = x^{1−γ}/(1 − γ) + βy` is outside the framework | `ku_additive_not_W1` |
| p. 681 | (W5), (W6) | hypotheses of `theorem_20_1_2*`; `ku_W5_misprint` |
| p. 681 | `θ`-norm, `ℓ^∞_θ`, Banach | `ku_seqθ`, `ku_Lθ`, `ku_thetaNorm`, `ku_thetaNorm_seqθ`, `ku_Lθ_surj`, `ku_Lθ_complete`, `ku_bshift`, `ku_bshift_apply`, `ku_σθ`, `ku_seqθ_σθ`, `ku_seqθ_zero`, `ku_continuous_σθ`, `ku_continuous_head`, `ku_head_mem`, `ku_continuous_W`, `ku_convex_Lθ`, `ku_σθ_mix` |
| p. 681 | `C_ϕ(ℓ^∞_θ)` with the `ϕ`-norm is a Banach space | `ku_InC`, `ku_norm`, `ku_ex_7_1_norm`, `ku_ex_7_1` (copied, Exercise 7.1) and the other `KUWeighted` lemmas |
| Theorem 20.1.2, p. 681 | Unique `U ∈ C_ϕ` with `W(c₀, U(₁c)) = U(c)`; `T_Wⁿ0 → U` | `theorem_20_1_2`, `ku_TW_mapsTo`, `ku_TW_contraction`, `ku_TW_exists_unique`, `ku_TW_tendsto` |
| Theorem 20.1.2, p. 681 | (W6) ⇒ `U` concave | `theorem_20_1_2_concave` |
| Theorem 20.1.2, p. 681 | Strict concavity (corrected hypotheses) | `theorem_20_1_2_strict` |
| Proof, p. 681 | `T_W` increasing; `T_W0 ∈ C_ϕ` | `theorem_20_1_2_T0` |
| Proof, p. 682 | `T_W(f + aϕ) ≤ T_Wf + aϕδ sup ϕ(₁c)/ϕ(c)`; Theorem 7.3.6 applies | `theorem_20_1_2_disc`, `theorem_20_1_2_via_7_3_6`, `ku_thm_7_3_6_of_continuous` (copied) |
| Proof, p. 682 | `‖U − T_Wⁿ0‖_ϕ ≤ ‖U‖_ϕ(δ sup ϕ(₁c)/ϕ(c))ⁿ → 0` | `ku_TW_iterate_bound`, `ku_TW_tendsto`; uniqueness among `ϕ`-bounded functions `ku_TW_unique_of_bound` |
| p. 682 | Example `W(x, y) = x^{1−γ} + βy`, `ϕ(c) = 1 + |c|_θ^{1−γ}`: `W(c₀, 0)` is `ϕ`-bounded | `ku_exW`, `ku_exϕ`, `ku_exϕ_pos`, `ku_head_le_norm`, `ku_example_682_W0`, `ku_example_682_misprint`, `ku_zeroθ` |
| p. 682 | `βϕ(₁c) < ϕ(c)`, hence `β sup ϕ(₁c)/ϕ(c) < 1` (corrected) | `ku_norm_σθ_le`, `ku_example_682_ratio`, `ku_example_682_sup`, `ku_pointwise_not_sup` |
| pp. 680, 682 | The example has a unique recursive utility, `U(c) = ∑ βᵗc_t^{1−γ}` | `ku_example_682`, `ku_example_682_series`, `ku_exW_continuousOn`, `ku_exW_lipschitz`, `ku_exϕ_continuous` |
| p. 683 | Partial-sum approach for aggregators unbounded below | not formalised: cited (Boyd 1990), not derived |

### §20.2 and §20.2.1 Epstein–Zin preferences (pp. 683–687)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 683 | Finite-state Markov filtration, adapted processes, `E_t` | `ku_Meas`, `ku_Adapted`, `ku_E`, `ku_update_agree`, `ku_E_meas`, `ku_Reach`, `ku_reach_update`, `ku_reach_pred` |
| Definition 20.2.1, p. 684 | Dynamic utility | `definition_20_2_1`; instance `ku_ezFin_dynUtility`, `ku_ezFin_meas` |
| Definition 20.2.2, p. 684 | Dynamic consistency | `definition_20_2_2`; `ku_dynConsistent_of_eq_20_2`, `ku_ez_dynConsistent` |
| Definition 20.2.3, p. 684 | Conditional certainty equivalent | `definition_20_2_3`; instances `ku_E_isCE`, `ku_kpCE_isCE`, `ku_expCE_isCE` |
| (20.2), p. 684 | Recursive utility `U_t = W(c_t, M_t(U_{t+1}))` | `eq_20_2` |
| p. 685 | Uncertainty aggregator `R` | `ku_UncertaintyAgg`, `ku_definition_20_2_3_uncertaintyAgg` |
| p. 685 | Time-additive EU, `W = u⁻¹(u(x) + βu(y))`, `M_t = u⁻¹E_tu`: `V_t = u(c_t) + βE_tV_{t+1} = E_t∑β^{s−t}u(c_s)` | `ku_timeAdditive_eu`, `ku_timeAdditive_eu_sum`, `ku_additive_sum`, `ku_Eiter`, `ku_Eiter_zero`, `ku_Eiter_succ`, `ku_Eiter_abs_le` |
| p. 685 | `W = u(x) + βy`, `R_t = E_t`: `U_t = E_t∑β^{s−t}u(c_s)` | `ku_timeAdditive_R` |
| p. 686 | Kreps–Porteus certainty equivalent | `ku_kpCE`, `ku_kpCE_eq_kpR`, `ku_E_pos`, `ku_kpCE_pos`, `ku_kpCE_isCE`, `ku_kpCE_mono`, `ku_kpCE_strictMono` |
| (20.3), p. 686 | The Epstein–Zin recursion | `eq_20_3`, `ku_ces_strictMonoOn` |
| p. 686 | Relative risk aversion `γ` | `ku_ez_rra` |
| p. 686 | EIS `1/ρ` | `ku_ez_eis` (via `SS.ces_eis`) |
| p. 686 | `γ = ρ` is time-additive expected power utility | `ku_ez_expected_power`, `ku_ez_expected_power_sum` |
| p. 686 | Scale invariance (homotheticity) | `ku_ez_markov`, `ku_ces_homog`, `ku_ez_markov_homogeneous`, `ku_ezFin_homog` |
| p. 686 | Weil's exponential certainty equivalent; translation invariance | `ku_expCE`, `ku_expCE_isCE`, `ku_expCE_translation` |
| (20.4), p. 686 | Weil's recursion | `eq_20_4` |
| (20.5), p. 686 | `ρ → 1`: `V_t = ln U_t` satisfies (20.5) | `ku_ces_limit`, `eq_20_5` |
| p. 687 | Robust-control interpretation; preference for early or late resolution | not formalised: interpretation referring to §9.6; resolution is treated later in the chapter |

### §20.2.1 Chew–Dekel risk aggregator (pp. 687–691)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 687 | Independence axiom | not formalised: statement of the axiom; its consequence for the Allais choices is formalised |
| p. 687 | Allais choices: EU gives `a₁ ≽ a₂` iff `a₃ ≽ a₄` | `ku_allais`, `ku_allais_u0` |
| p. 688 | `a₁ ≻ a₂` and `a₄ ≻ a₃` is inconsistent with EU | `ku_allais_paradox` |
| p. 688 | Certainty equivalent `U(μ, …, μ) = U(c)`; unique if `U` strictly increasing | `ku_ce_unique`, `ku_ce_exists`, `ku_ce_counterexample` |
| (20.6), p. 688 | Chew–Dekel certainty equivalent | `eq_20_6`, `ku_wsum_pos` |
| p. 689 | Properties (i)–(iv) of `M` | for EU: `ku_euM_i`, `ku_euM_ii`, `ku_euM_iii`, `ku_euM_iv`, `ku_euM_iv_misprint`; (i) for the others `ku_wM_i`, `ku_gulM_i` |
| p. 689 | Expected utility member: `μ = (∑ p c^α)^{1/α}`, conditions for `α ≤ 1` | `ku_euM`, `ku_euM_ce`, `ku_euM_ii`, `ku_euM_iii` |
| pp. 689–690 | Weighted utility: `μ = (∑ p c^{γ+α}/∑ p c^γ)^{1/α} = (∑ p̂ c^α)^{1/α}` | `ku_wM`, `ku_wM_zero`, `ku_wM_ce`, `ku_wM_eq` |
| p. 689 | Parameter conditions (i)/(ii) and their implications | `ku_wM_params`, `ku_wM_local`, `ku_wM_params_not_necessary` |
| p. 690 | Recursive weighted utility | `ku_recWeighted_ce`, `ku_recWeighted` |
| p. 690 | Disappointment aversion; `δ = 0` is EU; the certainty equivalent | `ku_gulM`, `ku_gulM_i`, `ku_gulM_zero`, `ku_gulM_ce`, `ku_gulM_ce_hat`, `ku_gulM_hat_misprint` |
| p. 691 | Recursive disappointment-aversion utility | `ku_recGul` |

### Exercise 20.1 (p. 735)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 20.1 | Finite-horizon Epstein–Zin utility, `U_T = c_T` | `ku_ezAux`, `ku_ezFin`, `ku_ezFin_T`, `ku_ezFin_succ`, `ku_PosPlan`, `ku_convex_PosPlan`, `ku_ezAux_pos`, `ku_ezFin_pos` |
| Ex 20.1 | `U_t` strictly concave for `t < T` if `ρ, γ > 0` (false; concave) | `ex_20_1`, `ex_20_1_not_strict`, `ku_kpCE_homog`, `ku_Q`, `ku_Q_markov`, `ku_ces_eq_kpR`, `ku_ces_concave` |

## §20.2.2–§20.3 and Exercises 20.2–20.3

### Common setting (`AABasics`, `AALimits`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 683 | Conditional expectations on a finite state space | `aa_E`, `aa_E_const`, `aa_E_mono`, `aa_E_add`, `aa_E_smul`, `aa_E_pos` |
| (20.3), (20.11), p. 686 | CES aggregator, Kreps–Porteus certainty equivalent, finite-horizon Epstein–Zin recursion | `aa_W`, `aa_KP`, `aa_ezU`, `aa_W_pos`, `aa_KP_pos`, `aa_KP_const`, `aa_W_diag`, `aa_W_strictMonoOn`, `aa_KP_mono`, `aa_ezU_pos` |
| p. 696 | `t`-step expectations on the tree; law of iterated expectations | `aa_Ex`, `aa_linear_unroll` |
| pp. 694–700 | `t⁻¹ ln E e^{tv} → E v`; the soft minimum `−k⁻¹ ln E e^{−kv} → min v` | `aa_logmgf_hasDerivAt`, `aa_tendsto_logmgf`, `aa_softmin_bounds`, `aa_tendsto_softmin` |

### §20.2.2 Ambiguity aversion

### Maxmin expected utility and recursive multiple priors (`AAMaxmin`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 692 | Ellsberg paradox: no single prior strictly prefers urn 1 for both bets | `aa_ellsberg_no_prior` |
| p. 692 | Maxmin utility `min_{q ∈ Δ} ∫ u dq` | `aa_maxmin`, `aa_E_ge_neg`, `aa_maxmin_bdd`, `aa_maxmin_le`, `aa_le_maxmin`, `aa_maxmin_attained`, `aa_maxmin_singleton` |
| pp. 692–693 | Maxmin utility resolves the Ellsberg paradox | `aa_ellsbergPriors`, `aa_ellsbergPrior`, `aa_ellsbergPrior_isDistribution`, `aa_E_bool`, `aa_ellsberg_black`, `aa_ellsberg_white`, `aa_ellsberg_maxmin` |
| p. 692, footnote 1 | Choquet expected utility | not formalised (footnote, no derivation) |
| (20.7), p. 693 | Recursive multiple-priors utility; properties of `R_t` | `aa_rmpU`, `aa_maxmin_mono`, `aa_maxmin_add_const`, `aa_maxmin_const`, `aa_maxmin_smul`, `aa_maxmin_superadditive` |
| p. 693 | Epstein–Schneider: with rectangular priors `min_P E^P[∑ βᵗu(c_t)]` satisfies the recursion | `aa_selU`, `aa_selU_eq_sum`, `aa_rmpU_isLeast_selection`, `aa_rectangular_recursion` |
| p. 693 | Without rectangularity dynamic consistency may fail | `aa_nrPrior`, `aa_nonrectangular_counterexample` |
| p. 693 | Hayashi's form `U_t = W(c_t, R_t(U_{t+1}))` contains (20.7) | `aa_hayashiU`, `aa_hayashiU_additive` |

### Variational, divergence and multiplier utility (`AAVariational`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 693 | Variational utility; `c(q) = 0` gives maxmin | `aa_Δ`, `aa_variational`, `aa_variational_zero` |
| p. 694 | `w`-weighted `φ`-divergence and divergence utility | `aa_phiDiv`, `aa_divU`, `aa_phiDiv_self`, `aa_phiDiv_nonneg`, `aa_divU_bdd` |
| p. 694 | `p` is among the nearby models; smaller `θ` is more ambiguity averse | `aa_divU_le_E`, `aa_divU_mono` |
| p. 694 | `θ → ∞` gives expected utility | `aa_riskSensitive_tendsto` |
| p. 695 | MMR: probabilistic sophistication for `w = 1`; Ellsberg | not formalised (cited, no derivation) |
| p. 695 | Relative entropy `φ(x) = x ln x − x + 1` (`φ ≥ 0`, `φ(1) = 0`, `φ(t)/t → ∞`) gives multiplier utility | `aa_klPhi`, `aa_klPhi_one`, `aa_klPhi_nonneg`, `aa_klPhi_superlinear`, `aa_phiDiv_kl` |
| p. 695 | Solving the minimisation gives `−θ ln ∫ exp(−u/θ) dp` | `aa_multiplier_isLeast`, `aa_divU_kl` |
| p. 695 | Robustness enhances risk aversion by `1/θ` | `aa_expU`, `aa_riskSensitive_eq_ce`, `aa_expU_arrowPratt` |
| pp. 695–696 | Gini index `φ(x) = (x − 1)²/2` gives `E c − Var(c)/(2θ)` on `c − Ec ≤ θ` | `aa_chiPhi`, `aa_chiPhi_one`, `aa_chiPhi_nonneg`, `aa_chiPhi_superlinear`, `aa_Var`, `aa_chi2_identity`, `aa_chi2_mmv` |

### Recursive divergence utility (`AADivergence`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 696 | One-step densities `m_{t+1}`, `E_t m_{t+1} = 1` | `aa_Admissible`, `aa_admissible_one`, `aa_admissible_isDistribution`, `aa_distort` |
| (20.8), p. 696 | `M_{t+1} = m_{t+1}M_t`, `M₀ = 1`, a martingale | `aa_M`, `aa_M_martingale` |
| p. 696 | `R_t(x) = min E_t[m x + θwφ(m)]`, `U_t = u(c_t) + βR_t(U_{t+1})` | `aa_divObj`, `aa_divR`, `aa_rdU`, `aa_rdUm`, `aa_divObj_ge`, `aa_divR_le`, `aa_divObj_sub` |
| pp. 696–697 | `U₀ = E∑βᵗM_t{u(c_t) + βθE_t[wφ(m)]}`; discounted divergence | `aa_rdUm_unroll`, `aa_Ex_change`, `aa_rdUm_eq_sum` |
| p. 696 | Dynamic consistency: the recursion equals the time-zero minimisation | `aa_rdU_le_rdUm`, `aa_rdU_isGLB` |
| pp. 695–696 | Relative entropy: the recursive multiplier operator | `aa_divR_kl` |

### Smooth ambiguity utility (`AASmoothAmbiguity`)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.9), p. 697 | Static smooth ambiguity; affine `v` is Bayesian; concave `v` below Bayesian | `aa_predictive`, `aa_predictive_isDistribution`, `aa_E_predictive`, `aa_kmmU`, `aa_kmm_affine`, `aa_kmm_concave_le` |
| p. 698 | Posterior and likelihood by Bayes' rule | `aa_posterior`, `aa_posterior_isDistribution`, `aa_posterior_martingale` |
| (20.10), p. 698 | Generalized recursive smooth ambiguity; `v ∘ u⁻¹` linear gives Epstein–Zin with hidden states | `aa_smoothM`, `aa_smoothM_linear` |
| (20.11)–(20.15), pp. 698–699 | Homothetic specification | `aa_powU`, `aa_powUinv`, `aa_powUinv_powU`, `aa_ju`, `aa_smoothM_power`, `aa_juU`, `aa_juU_pos`, `aa_ju_eq_powMean` |
| p. 699 | `η = γ`: ambiguity neutral, Epstein–Zin | `aa_ju_neutral`, `aa_juU_neutral` |
| p. 699 | Ambiguity aversion `η > γ`; higher `η` lowers utility | `aa_jensen_rpow`, `aa_powMean`, `aa_powMean_mono`, `aa_ju_antitone`, `aa_ju_le_KP`, `aa_KP_le_ju`, `aa_W_ju_antitone` |
| (20.16), p. 699 | Limit `ρ → 1` and the log form | `aa_W_tendsto_rho_one`, `eq_20_16` |
| p. 699 | Hansen–Sargent multiplier with hidden states; footnote 2 | `aa_expUinv`, `aa_smoothM_exp`, `aa_smoothM_exp_equal` |
| (20.17), p. 700 | Limit `γ → 1` | `eq_20_17` |
| (20.18), p. 700 | Limit `η → ∞`: recursive multiple priors | `eq_20_18` |
| (20.19), p. 700 | Klibanoff et al. (2009) nested in (20.10) | `eq_20_19`, `aa_kmm09U` |
| p. 700 | (20.19) not well defined for `γ > 1` with power `φ` | `aa_juMiao_illDefined` |
| p. 700 | `γ = ρ ∈ (0, 1)`, `α = 1 − (1 − η)/(1 − γ)`: ordinal equivalence with (20.19) | `aa_juMiao_step`, `aa_juMiao_ordinal` |
| p. 700 | Exponential `φ` always well defined | `aa_smoothM_expPhi` |
| pp. 700–701 | Lack of homogeneity of the exponential specification | not formalised (remark, no statement) |

### §20.2.3 Temporal resolution of uncertainty (`AAResolution`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 701 | Time-additive EU indifferent between choices 1 and 2, and 3 and 4 | `aa_timeAdditive_indifferent`, `aa_timeAdditive_indifferent_34` |
| p. 702 | Lotteries `M(X)`, programs `δ[c₀, m]`, `U₀(d) = E_d[W(c₀, E_m U₁)]` | `aa_Lott`, `aa_mix`, `aa_mix_mem`, `aa_integrable`, `aa_integral_mix`, `aa_U0`, `aa_Y`, `aa_Y_convex` |
| Definition 20.2.4, p. 703 | Preference for earlier (later) resolution | `aa_PrefersEarly`, `aa_PrefersLate`, `definition_20_2_4` |
| Theorem 20.2.1, p. 704 | Earlier (later) iff `W(x, ·)` convex (concave) | `theorem_20_2_1`, `theorem_20_2_1_late` |
| p. 704, Exercise 20.3 | Epstein–Zin prefers earlier resolution iff `γ > ρ` | `aa_ezKP`, `aa_ezKP_eq`, `aa_powF_strictConvexOn`, `aa_powF_strictConcaveOn`, `aa_ezKP_eq_powF`, `aa_strictConvexOn_comp`, `aa_strictConcaveOn_comp`, `aa_ezKP_strict`, `aa_ezKP_diag`, `aa_powU_bound`, `aa_powU_measurable`, `aa_Y_subset`, `ex_20_3`, `aa_ez_strictEarly`, `aa_ez_indifferent` |

### §20.3 Properties of recursive utility

### §20.3.1 Concavity (`AAConcavity`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 704 | Recursive utility on the tree | `aa_recU`, `aa_posPlans`, `aa_posPlans_convex`, `aa_recU_congr` |
| p. 705 | Concave `W`, `M` give concave `U` by backward induction | `aa_recU_concaveOn` |
| p. 705 | "Strictly increasing concave `W`, strictly concave `M` ⇒ `U` strictly concave" | counterexample `aa_recU_not_strictConcave` |
| p. 705 | Epstein–Zin, `U_T = c_T`, `ρ, γ > 0`: `U_t` strictly concave | `aa_ezU_eq_recU`, `aa_KP_concaveOn`, `aa_W_concaveOn`, `aa_ezU_concaveOn`, `aa_ezU_smul`; counterexample `aa_ezU_not_strictConcave` |
| Lemma 20.3.1, p. 705 | (i) ⇔ (ii) ⇔ (iii) for homogeneous `f` | `aa_Homogeneous1`, `aa_LevelCond`, `aa_Superadd`, `lemma_20_3_1_i_iff_iii`, `lemma_20_3_1_i_ii`, `lemma_20_3_1`; counterexample `aa_skiadasCex`, `lemma_20_3_1_counterexample` |

### §20.3.2 Risk aversion (`AARiskAversion`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 705 | Deterministic plans; more risk averse | `aa_Deterministic`, `aa_MoreRiskAverse`, `aa_IsCE`, `aa_recU_deterministic`, `aa_recU_le` |
| p. 706 | Risk aversion; "risk averse if more risk averse than a risk-neutral `U²`" | `aa_RiskAverse`, `aa_riskAverse_never`, `aa_RiskAverse'`, `aa_coinE`, `aa_moreRiskAverse_not_riskAverse` |
| Proposition 20.3.1, p. 706 | More risk averse iff `M¹ ≤ M²` | `proposition_20_3_1` |
| Proposition 20.3.1, p. 706 | Epstein–Zin case: iff `u₁ = φ ∘ u₂`, `φ` increasing concave | `aa_CELe`, `aa_pratt_of_concave`, `aa_concave_of_pratt`, `proposition_20_3_1_pratt`, `aa_euCE`, `aa_euCE_isCE`, `aa_euCE_mono`, `proposition_20_3_1_ez` |
| p. 706 | Comparative ambiguity aversion | not formalised (discussion without statements) |

### §20.3.3 Utility gradients and pricing kernels (`AAGradients`, `AAPricing`)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 20.3.1, p. 707 | Gradient density | `aa_IsGradientDensity` |
| Definition 20.3.2, p. 707 | Derivative of the conditional CE | `aa_CEDerivPrinted`, `aa_HasCEDeriv`, `aa_cePrinted_apply`, `aa_CEDerivPrinted_not_unique`, `aa_HasCEDeriv_expectation`, `aa_not_HasCEDeriv_expectation_zero` |
| p. 707 | `M = u⁻¹E u` has `κ = u'(x)/u'(M)` | `aa_euCE_hasCEDeriv` |
| Proposition 20.3.2, p. 708 | Gradient `π = ℰλ`; the recursion for `φ'_t(0)` | `aa_gradV`, `aa_GradHyp`, `aa_gradV_hasDerivAt`, `aa_Ex_congr`, `aa_gradπ`, `proposition_20_3_2`, `proposition_20_3_2_gradient` |
| p. 708 | `λ₀ = J'(w₀)`, marginal value of wealth | `aa_marginal_value_wealth`, `aa_lambda0_eq_mu` |
| p. 709 | Pricing kernel `π_{t+1}/π_t = (λ_{t+1}/λ_t)W₂κ_{t+1}` | `aa_pricingKernel` |
| p. 709 | Utility supergradients | `aa_IsSupergradient` |
| Example 20.3.1, (20.20), p. 709 | Epstein–Zin pricing kernel; countercyclical for `γ > ρ` | `aa_W_hasFDerivAt`, `aa_KP_hasCEDeriv`, `eq_20_20`, `aa_ezMh`, `aa_ezW₁`, `aa_ezW₂`, `aa_ezκ`, `aa_M_pos`, `example_20_3_1`, `aa_ez_kernel_antitone` |
| Example 20.3.2, p. 710 | Generalized smooth ambiguity pricing kernel; `η > γ` | `aa_ju_hasFDerivAt`, `example_20_3_2`, `aa_smooth_kernel_antitone` |
| Example 20.3.3, p. 710 | Supergradients of recursive multiple-priors utility | `aa_Ex_smul`, `example_20_3_3`, `example_20_3_3_exists` (inclusion `⊇`; `⊆` not formalised) |

### Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 20.2, p. 735 | Pricing kernels: Epstein–Zin | `example_20_3_1` |
| Exercise 20.2, p. 735 | Pricing kernels: divergence (multiplier) utility | `aa_klDensity`, `aa_klDensity_attains`, `aa_riskSensitive_hasCEDeriv`, `ex_20_2_divergence`, `aa_divR_supergradient` |
| Exercise 20.2, p. 735 | Pricing kernels: generalized smooth ambiguity | `aa_ju_hasFDerivAt`, `example_20_3_2` |
| Exercise 20.3, p. 735 | Epstein–Zin prefers earlier resolution iff `γ > ρ` | `ex_20_3`, `aa_ez_strictEarly`, `aa_ez_indifferent` |

## §20.4–§20.5 and Exercises 20.4–20.7

### §20.4 and §20.4.1 Optimality and equilibrium (`PAEpsteinZin`, `PAPortfolio`)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.3), p. 686 | Epstein–Zin time aggregator and certainty equivalent | `pa_W`, `pa_CE`, `pa_E`, `pa_CE_eq_kpR` (the copied `SS.kpR`), `pa_CE_pos`, `pa_W_pos` |
| p. 686 | Scale invariance (homotheticity) of the aggregator and certainty equivalent | `pa_W_homog`, `pa_CE_homog` |
| (20.20), p. 710 | The pricing kernel `M = β(C'/C)^{−ρ}(U'/M_t(U'))^{ρ−γ}` | `pa_M` |
| (20.21), p. 711 | Budget constraint; the wealth (portfolio) return `R_w = ∑ψᵢRᵢ`, `∑ψᵢ = 1` | `pa_nextWealth`, `pa_wealthReturn`, `pa_wealthReturn_eq`, `pa_Rw`, `pa_Rw_update` |
| p. 711 | Bellman equation with `J_t = A_t X_t`, `C_t = a_t X_t`: the objective after substitution | `pa_bellmanInner`, `pa_bellmanInner_pos`, `pa_bellman_conjecture` |
| p. 711 | The conjecture `J_t(X) = A_t X` (the value is linear in wealth) | `pa_value_homogeneous` |
| (20.22), p. 712 | First-order condition for `a_t` | `pa_bellmanInner_hasDerivAt`, `pa_bellman_hasDerivAt`, `eq_20_22` |
| (20.23), p. 712 | `A_t = (1 − β)^{1/(1−ρ)} a_t^{−ρ/(1−ρ)}` | `eq_20_23`, `pa_Anext` |
| (20.24), p. 712 | Substituting (20.23) at `t + 1` into (20.22) | `eq_20_24` |
| (20.25), p. 712 | `X_{t+1} = R_{w,t+1} C_t (1 − a_t)/a_t` | `eq_20_25` |
| (20.26), p. 712 | `β^{(1−γ)/(1−ρ)} E_t[(C'/C)^{−ρ(1−γ)/(1−ρ)} R_w^{(1−γ)/(1−ρ)}] = 1` | `eq_20_26` |
| p. 712 | Portfolio first-order condition `E_t[A^{1−γ}R_w^{−γ}(R_i − R_f)] = 0` | `pa_portfolio_foc` |
| p. 712 | Substituting (20.23) | `pa_portfolio_foc_X` |
| (20.27), p. 712 | Substituting (20.25) | `eq_20_27` |
| p. 713 | Multiplying by `ψᵢ` and summing | `pa_sum_portfolio_foc` |
| (20.28), p. 713 | Euler equation for the riskless asset | `eq_20_28` |
| (20.29)–(20.30), p. 713 | Euler equation `E_t[M̄ R_i] = 1` with `M̄ = (β(C'/C)^{−ρ})^{(1−γ)/(1−ρ)} R_w^{(ρ−γ)/(1−ρ)}` | `eq_20_29`, `pa_Mbar`, `pa_Mbar_eq` |
| (20.31), p. 713 | `X_t/C_t = (1/(1 − β))(U_t/C_t)^{1−ρ}` | `eq_20_31` |
| pp. 713–714 | `M_{t+1} = M̄_{t+1}` | `pa_M_eq_Mbar` |
| p. 714 | `R_f = 1/E_t M` | `pa_riskfree_rate` |
| p. 714 | Conditional equity premium `E_t R_e − R_f = −Cov_t(R_e, M)/E_t M` | `pa_Cov`, `pa_equity_premium` |
| p. 714 | GMM tests of (20.29) (Epstein–Zin 1991) | Not formalised (empirical) |

### §20.4.2 Log-linear approximation (`PALogNormal`, `PACampbellShiller`, `PAVolatilityPuzzles`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 715 | Conditionally lognormal, homoskedastic joint distribution | `pa_JointGaussian`, `pa_lin`, `pa_quad`, instance `pa_jointGaussian_rank_one` |
| p. 715 | `ln E_t X = E_t ln X + ½ Var_t ln X` | `pa_log_integral_exp_gaussian`, `pa_integral_exp_lin`, `pa_lognormal_euler`, `pa_lin_three`, `pa_quad_three`, `pa_sum_three`, `pa_levels_eq_exp` |
| p. 715 | The log form of (20.26) | `pa_eq_20_26_log` |
| (20.32), p. 715 | Log form of (20.28) | `eq_20_32` |
| (20.33), p. 716 | The riskfree rate `r_f = −ln β + ρE_tΔc − ½(γ−ρ)/(1−ρ)σ_w² − ρ²(1−γ)/(2(1−ρ))σ_c²` | `eq_20_33` |
| (20.34), p. 716 | Log form of (20.29) for asset `i` | `eq_20_34` |
| (20.35), p. 716 | Risk premium `E r_i − r_f + ½σ_i² = ρ(1−γ)/(1−ρ)σ_ic + (γ−ρ)/(1−ρ)σ_iw` | `eq_20_35` |
| p. 716 | Signs of the two weights when `ρ < 1 < γ` | `pa_eq_20_35_weights` |
| (20.36), p. 717 | Campbell–Shiller approximation: exact identity, `ϱ`, `κ`, first-order error | `pa_varrho`, `pa_kappa`, `pa_varrho_pos`, `pa_varrho_lt_one`, `pa_cs_exact`, `pa_cs_hasDerivAt`, `pa_cs_kappa`, `eq_20_36` |
| (20.37), p. 717 | Solving forward (path by path, and in conditional expectation) | `pa_cs_iterate`, `eq_20_37`, `eq_20_37_cond` |
| (20.38), p. 717 | (20.36) rewritten | `eq_20_38` |
| (20.39), p. 717 | Unexpected returns = revisions of dividend and return expectations | `eq_20_39` |
| p. 718 | `d_e = λc`; `E_t r_{e,t+1} = μ_e + ρE_tΔc_{t+1}` from (20.33) and (20.35) | `pa_expected_equity_return` |
| (20.40), p. 719 | `pe − de = k_e/(1−ϱ) + (λ−ρ)E_t∑ϱⁱΔc_{t+1+i}` | `eq_20_40` |
| (20.41), p. 719 | Unexpected equity return | `eq_20_41` |
| p. 719 | Long-run risk process; forecasts and revisions | `pa_forecast`, `pa_forecast_zero`, `pa_forecast_succ`, `pa_forecast_revision`, `pa_sum_forecast`, `pa_sum_revision` |
| (20.42), p. 719 | `pe − de = k_e/(1−ϱ) + (λ−ρ)(g/(1−ϱ) + (z_t−g)/(1−ϱφ))` | `eq_20_42` |
| (20.43), p. 719 | `r_e − E r_e = λε_c + (λ−ρ)ϱ/(1−ϱφ)ε_z` | `eq_20_43` |
| p. 719 | The price–dividend ratio is procyclical if `λ > ρ` | `pa_pd_procyclical` |
| p. 720 | Real consol: log yield and unexpected return (`λ = 0`; printed `λ = 1`) | `pa_consol_yield`, `pa_consol_news`, `pa_consol_lambda_one_counterexample` |
| p. 720 | `σ_iw = σ_ic + (1 − ρ)σ_ig` | `pa_sigma_iw` |
| p. 721 | `E r_i − r_f + ½σ_i² = γσ_ic + (γ−ρ)σ_ig` | `pa_premium_gamma` |
| p. 721 | Equity premium under long-run risk | `pa_lrr_cov`, `pa_lrr_equity_premium` |
| (20.44), p. 721 | Real bond premium | `eq_20_44` |
| (20.45), p. 721 | Equity–bond premium | `eq_20_45` |
| p. 722 | Signs: power-utility bond premium; negative Epstein–Zin term premium for `γ > ρ` | `pa_term_premium_signs` |
| pp. 720, 722 | Verbal discussion (EIS estimates, intuition) | Not formalised (discussion) |

### §20.4.3 Long-run risk (`PAGaussianShocks`, `PALongRunRisk`, `PALongRunRiskPricing`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 723 | The Bansal–Yaron model with IID `N(0,1)` shocks | `PABansalYaron`, `pa_by_g`, `pa_by_x'`, `pa_by_v'`, `pa_by_gd`, `pa_by_θ`, `pa_by_θ_sub_one`, `pa_by_θ_mul`, `pa_stdNormal_pi` (instance) |
| p. 723 | Lognormal Euler equations with IID shocks | `pa_integral_exp_shocks`, `pa_euler_shocks_iff`, `pa_cov_shocks`, `pa_integral_affine_shocks`, `pa_sum_four` |
| (20.46), p. 723 | Campbell–Shiller for the consumption claim, `κ₀`, `κ₁ < 1` | `eq_20_46`, `pa_by_rw` |
| (20.47), p. 723 | Log pricing kernel | `eq_20_47`, `pa_by_m` |
| (20.48)–(20.49), p. 724 | Euler equations in exponential form | `eq_20_48` |
| p. 724 | Matching coefficients of `x_t` and `σ_t²` | `pa_match_coeffs`, `pa_by_matching_wealth` |
| p. 724 | `A₁ = (1 − ρ)/(1 − κ₁ρ_x)`; positive iff EIS > 1; negative for CRRA with `γ = ρ > 1` | `pa_by_A1`, `pa_by_A1_pos`, `pa_by_A1_neg` |
| pp. 724–725 | `A₂`; `A₂ < 0` if `γ > 1`, `ρ < 1`; effect of `ν₁` | `pa_by_A2formula`, `pa_by_A2`, `pa_by_A2_neg`, `pa_by_A2_magnified` |
| (20.50), p. 725 | Wealth-return news, `B = κ₁A₁φ_e`; `Var_t(r_w)` | `pa_by_B`, `eq_20_50`, `pa_by_rw_affine`, `pa_by_Erw`, `pa_by_var_rw` |
| (20.51), p. 725 | `E_t m`, kernel news, prices of risk `λ_{m,η}, λ_{m,e}, λ_{m,w}` | `pa_by_Em`, `eq_20_51`, `pa_by_m_affine`, `pa_by_Em_integral`, `pa_by_lam_eta`, `pa_by_lam_e`, `pa_by_lam_w`, `pa_by_gamma_rho` |
| pp. 725–726 | Signs of the prices of risk; power utility | `pa_by_lam_eta_neg`, `pa_by_lam_e_pos`, `pa_by_lam_w_neg`, `pa_by_lam_w_not_pos`, `pa_by_power_utility` |
| (20.52), p. 726 | `Var_t(m)` | `eq_20_52` |
| (20.53), p. 726 | Risk premium on the wealth portfolio | `pa_lognormal_premium`, `eq_20_53` |
| (20.54), p. 726 | `E_t(r_e − r_f) + ½Var_t r_e = −Cov_t(m, r_e)` | `eq_20_54` |
| (20.55), p. 727 | Equity return, news, `β_{e,e}`, `β_{e,w}`, `Var_t(r_e)` | `eq_20_55`, `pa_by_re`, `pa_by_bee`, `pa_by_bew`, `pa_by_re_news`, `pa_by_re_affine`, `pa_by_Ere`, `pa_by_var_re` |
| (20.56), p. 727 | Conditional equity premium | `eq_20_56` |
| (20.57), p. 728 | Matching coefficients for equity; `A₁ₑ`, `A₂ₑ`, `H_e` | `pa_by_matching_equity`, `pa_by_He`, `pa_by_A1e`, `pa_by_A1e_pos`, `pa_by_A2e` |
| p. 728 | Unconditional equity return; `Var(r_e)`, `Var(z_e)` | `pa_by_re_decomp`, `pa_cov_sum_uncorrelated`, `pa_cov_lin_uncorrelated`, `pa_by_uncond_var` |
| p. 729 | Riskfree rate from `E_t[M R_f] = 1`, and after subtracting `(ρ−γ)/(1−ρ) r_f` | `pa_by_riskfree`, `pa_by_riskfree_final` |
| p. 729 | Mean riskfree rate via (20.53) and (20.52); `Q₁`, `Q₂` | `pa_by_lam_e_B`, `pa_by_riskfree_state` |
| p. 729 | Riskfree rate volatility | `pa_by_var_riskfree` |
| pp. 723–729 | Numerical calibration | Not formalised (computational) |

### §20.5 Pareto optimality (`PAPareto`, `PALucasStokey`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 729–730 | Recursive utilities, endowments, `C(e)`, `U₀(e)` | `pa_feasible`, `pa_uvec`, `pa_U0`, `pa_U0bar`, `pa_feasible_isCompact`, `pa_feasible_convex`, `pa_zero_feasible`, `pa_U0bar_bdd` |
| Lemma 20.5.1, p. 730 | `U₀(e)` convex, closed, free disposal (corrected: the comprehensive hull) | `lemma_20_5_1`, `lemma_20_5_1_plain_closed`, `lemma_20_5_1_counterexample`, `pa_FreeDisposal` |
| Definition 20.5.1, p. 730 | Pareto optimal allocation | `definition_20_5_1`, `pa_ParetoOptimal` |
| (20.58)–(20.59), p. 730 | Negishi problem; `Δⁿ`; solutions with positive weights are Pareto optimal | `pa_simplex`, `pa_dot`, `pa_Vhat`, `pa_Vhat_U0bar`, `pa_negishi_pareto` |
| Lemma 20.5.2, p. 731 | `v ∈ U₀(e)` iff (20.62) (corrected: the comprehensive hull) | `lemma_20_5_2`, `pa_mem_iff_support`, `pa_clm_apply`, `lemma_20_5_2_counterexample` |
| pp. 731–732 | Proof of Lemma 20.5.2 by separation, free disposal (`w ≥ 0`), closedness | `pa_mem_iff_support` |
| (20.60)–(20.61), p. 731 | The Lucas–Stokey Bellman equation and promise-keeping constraint | `PARecEconomy`, `pa_rec_feasible`, `pa_rec_U`, `pa_rec_values`, `pa_promise_ok`, `pa_bellman_values` |
| Proposition 20.5.1, p. 732 | `V̂(e₀, θ)` satisfies (20.60) | `proposition_20_5_1`, `pa_bellman_le_rec` |
| (20.63)–(20.64), p. 733 | Allocations and weights generated by the policy correspondences | hypotheses `hopt`, `hdel` of `proposition_20_5_2` |
| Proposition 20.5.2, p. 733 | Generated allocations are Pareto optimal (corrected: positive weights) | `proposition_20_5_2`, `proposition_20_5_2_counterexample` |
| pp. 733–734 | Numerical algorithm, Steps 1–3 | Not formalised (computational; no convergence claim) |
| p. 734 | `F(c, ν) = max_u W(c, u) − (1 − ν)u`; duality | `pa_dwu_F`, `pa_dwu_duality` |
| p. 734 | Variational utility `U_t = min_ν F + (1 − ν)E_t U_{t+1}` | `pa_dwu_variational` |
| p. 734 | The Dumas–Wang–Uppal recursion with `λ_{t+1} = (1 − ν_t)λ_t` | `pa_dwu_planner` |

### Exercises 20.4–20.7 (`PAWeil`, `PAExercises`)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 20.4, p. 735 | Bansal–Yaron Matlab replication | Not formalised (computational); its formulas are the §20.4.3 theorems |
| Exercise 20.5, p. 735 | Exponential certainty equivalent of a Gaussian | `pa_expCE`, `pa_expCE_gaussian` |
| Exercise 20.5 | Certainty-equivalent step of the guess `V = A(a + By + D)` | `pa_weilK`, `ex_20_5_ce`, `ex_20_5_K` |
| Exercise 20.5 | Existence of `A`; FOC and verification of the guess; consumption rule | `ex_20_5_A`, `pa_weilObj`, `ex_20_5` |
| Exercise 20.5 | Effects of EIS (MPC) and risk aversion (precautionary saving) | `ex_20_5_mpc`, `ex_20_5_precautionary` |
| Exercise 20.6, pp. 735–736 | Production economy: planner's objective and its directional derivative | `pa_planner`, `pa_planner_hasDerivAt`, `pa_clm_pi_apply`, `pa_clm_prod_apply` |
| Exercise 20.6 | First-order conditions: risk sharing at dates 0 and 1, Euler equation | `ex_20_6_sharing0`, `ex_20_6_sharing1`, `ex_20_6_euler` |
| Exercise 20.7(a), p. 736 | Multiplier preferences: certainty equivalent, distortion, derivative | `pa_multCE`, `pa_distortion`, `pa_multiplier_hasDerivAt`, `pa_multPlanner` |
| Exercise 20.7(a) | First-order conditions for a Pareto optimum | `ex_20_7` |
| Exercise 20.7(b) | Matlab solution | Not formalised (computational) |
