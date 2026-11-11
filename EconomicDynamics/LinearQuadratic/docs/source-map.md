# Source map: Miao Chapter 9

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 9,
Linear-Quadratic Models, pp. 291–326. Lean names are relative to `Miao.LinearQuadratic`;
the LQ regulator of §9.2–9.3 is `LSProblem` (finite horizon `LSFinProblem`), the
discretion problem of §9.5 is `CPDisc`. Departures from the book are in
[corrections](corrections.md).

## §9.1–§9.3 and Exercises 9.1, 9.2, 9.4

### §9.1 Controlled linear state-space system (pp. 291–294)

| Source | Claim | Lean |
| --- | --- | --- |
| Assumption 9.1.1, p. 291 | `E[ε_{t+1}\|F_t] = 0`, `E[ε_{t+1}ε'_{t+1}\|F_t] = I` | `LSAssumption911` |
| Assumption 9.1.1, as used (p. 296) | The conditional law of `ε_{t+1}` given `F_t`: mean `0`, second moments `I` | `LSShockLaw` |
| (9.1), p. 292 | `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}` | `ls_state`, `ls_traj`, `ls_traj_eq` |
| (9.2), p. 292 | `y_t = Gx_t + Hu_{t−1} + Dε_t` | `ls_output` |
| "stable" (p. 292) | Every eigenvalue inside the unit circle (Definition 1.4.5); equivalent to `Mᵗv → 0` and to `ρ(M) < 1` | `ls_Stable`, `ls_stable_iff_tendsto`, `ls_stable_iff_specRad`, `ls_stable_of_specRad`, `ls_specRad_lt_of_stable`, `ls_stable_transpose` |
| Definition 9.1.1, p. 292 | Stabilizable: `A + BH` stable for some `H` | `ls_Stabilizable` |
| pp. 292–293 | Under `u_t = Hx_t`, `x_{t+1} = (A + BH)x_t + Cε_{t+1}`; the deterministic steady state `0` is stable iff `A + BH` is stable | `definition_9_1_1_closed_loop`, `definition_9_1_1_steady_state` |
| p. 293 | "This condition can be verified by choosing a trivial control law" | No formal content |
| Definition 9.1.2, p. 293 | Controllable: `∑_{j<nₓ} AʲBB'A'ʲ > 0` | `ls_Controllable`, `ls_gram`, `ls_gram_quad`, `ls_gram_posSemidef`, `ls_gram_posDef_iff`, `ls_dot_self_nonneg` |
| p. 293 (Whittle 4.3.1) | Equivalent to steering any `x₀` to any target in `r` steps (corrected: for `r ≥ nₓ`, not every `r > 0`) | `definition_9_1_2_iff`, `ls_reach_of_gram`; counterexample `ls_controllable_not_reach_one` |
| p. 293 | Controllability implies stabilizability | `controllable_stabilizable` |
| p. 293 | Not conversely: `A` stable, `B = 0` | `ls_stabilizable_not_controllable` |
| p. 293 | Controllability applies to endogenous states only | No formal content (illustrated by `ls_stabilizable_not_controllable`) |
| Definition 9.1.3, p. 293 | Observable: `∑_{j<nₓ} A'ʲG'GAʲ > 0` | `ls_Observable`, `ls_observable_gram` |
| p. 293 (Whittle 4.4.1) | Equivalent to determining `x₀` from `y₀, …, y_r` given inputs and shocks (corrected: for `r ≥ nₓ − 1`) | `definition_9_1_3_iff`, `ls_state_sub`; counterexample `ls_observable_not_two_outputs` |
| Definition 9.1.4, p. 294 | Detectable: `A − JG` stable for some `J` | `ls_Detectable` |
| (9.3), p. 294 | The estimation error `Δ_{t+1} = (A − AKG)Δ_t + Cε_{t+1} − AKDε_t` (corrected) | `eq_9_3_error`; misprint `eq_9_3_misprint` |
| p. 294 | `Δ_t` is stable if `A − AKG` is stable | `eq_9_3_tendsto` |
| p. 294 | Detectability gives an updating rule (9.3) with asymptotically correct estimates | `definition_9_1_4_rule` (for invertible `A`) |
| p. 294 | `x̂_{t+1\|t}` satisfies (9.3) (Section 10.1.1) | Not formalised (Chapter 10) |

### §9.2 Finite-horizon problems (pp. 294–297)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 294 | The non-stationary problem | `LSFinProblem`, `LSFinProblem.stage`, `LSProblem.loss` |
| p. 295 | Loewner order `M ≥ N`, `M > N` | Mathlib `Matrix.PosSemidef`/`PosDef`, `MatrixOrder` (`ls_quad_le`, `ls_posSemidef_of_le`) |
| Proposition 9.2.1, p. 295 | (i) `V_t(x) = −x'P_tx − d_t` (9.4), `P_t ≥ 0`, (9.5), (9.6); (ii) `u_t = −F_tx_t` (9.7)–(9.8) | `proposition_9_2_1`, `LSFinProblem.V`, `LSFinProblem.Vbk`, `LSFinProblem.V_succ`, `LSFinProblem.V_hor`, `LSFinProblem.P`, `LSFinProblem.Pbk`, `LSFinProblem.P_succ`, `LSFinProblem.P_hor`, `LSFinProblem.d`, `LSFinProblem.dbk`, `LSFinProblem.d_succ`, `LSFinProblem.d_hor`, `LSFinProblem.Fg` |
| (9.5), (9.11) | The Riccati operator `T` | `LSProblem.T`, `LSProblem.T_eq_sub`, `LSProblem.T_transpose`, `LSProblem.T_posSemidef` |
| (9.8), (9.17) | The gain `F` | `LSProblem.F`, `LSProblem.G_mul_F`, `LSProblem.N_transpose` |
| p. 296 | `E_tε_{t+1} = 0`, `E_tε'C'PCε = tr(PCC')`, the expected continuation | `ls_condExp_quad` (conditional, under Assumption 9.1.1), `ls_integral_quad`, `ls_quad_shock_expand` (under `LSShockLaw`) |
| pp. 295–296 | The Bellman step: substitute, take the first-order condition, match coefficients | `LSProblem.bellObj_quad`, `LSProblem.bellObj_isGreatest`, `LSProblem.loss_add_cont`, `LSProblem.ls_sq_complete`, `LSProblem.dot_S_comm` |
| p. 296 | FOC `(R + βB'PB)u = −(S' + βB'PA)x` | `LSProblem.ls_foc` |
| p. 296, footnote 1 | Differential rules for the first-order condition | `LSProblem.ls_first_variation` |
| p. 296 | `R + βB'PB > 0` | `LSProblem.G_posDef`, `LSProblem.G_transpose` |
| p. 296 | `P_t ≥ 0` (from `[[Q, S], [S', R]] ≥ 0`) | `LSProblem.T_posSemidef`, `LSProblem.JointPSD`, `LSProblem.quad_joint`, `LSProblem.loss_nonneg`, `LSProblem.Q_transpose_of_joint`, `LSProblem.Q_posSemidef_of_joint` |
| p. 296 | Feedback vs open-loop: optimality among all control sequences (deterministic problem) | `LSFinProblem.ls_finite_seq_identity`, `LSFinProblem.ls_finite_seq_optimal` |
| p. 296 | "These two forms may not be equivalent" | No formal content |
| (9.9), p. 297 | `P_t = min_F [Q − F'S' − SF + F'RF + β(A − BF)'P_{t+1}(A − BF)]`, minimiser `F_t` | `LSFinProblem.eq_9_9`, `LSProblem.TF`, `LSProblem.TF_expand`, `LSProblem.TF_F`, `LSProblem.TF_eq_T_add`, `LSProblem.TF_ge_T`, `LSProblem.TF_eq_T_iff` |
| p. 297 | Certainty equivalence principle | `LSFinProblem.certainty_equivalence`, `LSFinProblem.zeroC`, `LSFinProblem.zeroC_Pbk`, `LSFinProblem.zeroC_dbk` |
| p. 297 | The uncentered case via `[x', 1]'` or `x̃ = x − x*` | See Exercise 9.2 (`LSProblem.augment`, `ex_9_2_transition`, `ex_9_2_loss`, `ex_9_2`) |

### §9.3 Infinite-horizon limits (pp. 298–304)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 298 | The infinite-horizon stochastic regulator | `LSProblem` (stationary data) |
| (9.10), p. 298 | The side condition; `x_t`, `u_t` cannot grow faster than `1/√β` | `eq_9_10_growth` |
| (9.11), p. 298 | `P(s) = T(P(s − 1)) = Tˢ(P(0))`, `F(s) = F(P(s − 1))` | `LSProblem.eq_9_11`, `LSProblem.toFin`, `LSProblem.toFin_stage`, `LSProblem.toFin_Pbk`, `LSProblem.dIter`, `LSProblem.toFin_dbk` |
| p. 299 | `S` normalised to zero by a change of variables | `ex_9_1` (Exercise 9.1) |
| p. 299 | Deterministic case by certainty equivalence; `V_s(x) = −x'P(s)x` | `LSFinProblem.certainty_equivalence`, `LSProblem.toSS_riccati_iter` |
| pp. 299–301 | Discounting: `(√βA, √βB)`, `x̂_t = β^{t/2}x_t` | `LSProblem.toSS`, `LSProblem.toSS_riccati`, `LSProblem.toSS_gain`, `LSProblem.toSS_gainDen`, `LSProblem.toSS_closedLoop`, `LSProblem.toSS_costMat`, `LSProblem.loss_S_zero`, `LSProblem.ls_discount_rescale` |
| Proposition 9.3.1, p. 299 | `Q > 0`, `R > 0`, `(√βA, √βB)` controllable or stabilizable ⇒ (i) unique psd solution of (9.12); (ii) `P(s) → P` | `LSProblem.proposition_9_3_1`, `LSProblem.ls_discounted_main`, `ls_riccati_main` |
| p. 299 | `P(1) = Q`, `V₁ < V₀` | `LSProblem.ls_P_one`, `LSProblem.T_zero_S` |
| p. 299 | "`V_{s+1} < V_s`, `P(s + 1) > P(s)`" (corrected: `≤`) | `LSProblem.ls_P_mono`, `ls_iter_zero_mono`, `ls_iter_zero_mono_add`, `ls_riccati_mono`, `ls_riccati_le_TF`, `ls_iter_psd`, `ls_iter_mono_le`, `ls_zero_le_psd`; counterexample `LSProblem.ls_P_mono_not_strict` |
| p. 299 | `{P(s)}` bounded: a policy with finite value; controllable case (steer to zero) | `ls_iter_bdd_of_controllable`, `ls_finite_lower` |
| pp. 299–300 | Stabilizable case: `u = Kx` with `√β(A + BK)` stable gives a finite value | `ls_iter_le_PF` |
| p. 300 | The bounded increasing `P(s)` converge to a psd `P` solving (9.12) | `ls_iter_converges`, `ls_exists_tendsto_of_quad`, `ls_tendsto_of_quad`, `ls_entry_eq_polar`, `ls_tendsto_quad`, `ls_tendsto_riccati`, `ls_tendsto_mul`, `ls_tendsto_inv`, `ls_fixed_of_tendsto` |
| (9.13), p. 300 | `P = Q + F'RF + βΓ'PΓ` | `LSProblem.eq_9_13` |
| (9.14), p. 300 | `V(x_t)` increases and `x_t'(Q + F'RF)x_t → 0` along `x_t = (√βΓ)ᵗx₀` | `LSProblem.eq_9_14`, `ls_cost_tendsto_zero` |
| p. 300 | Hence `x_t → 0`, `√βΓ` stable | `ls_stable_of_fixed`, `ls_Detects`, `ls_detects_of_posDef`, `ls_tendsto_zero_of_quad_posDef`, `ls_posDef_coercive` |
| p. 300 | `P = ∑ⱼ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ` | `LSProblem.eq_9_13_series`, `LSProblem.ls_sqrt_sandwich` |
| p. 300 | `P(s) = Tˢ(P(0)) ≥ Tˢ(0) → P` | `ls_iter_mono_le` (in `ls_riccati_main`) |
| p. 300 | `P(s) ≤ ∑ βʲΓ'ʲ(Q + F'RF)Γʲ + Γ'ˢP(0)Γˢ → P` (corrected: `βˢΓ'ˢP(0)Γˢ`) | `LSProblem.ls_P_le_policy`; misprint `LSProblem.ls_P_le_policy_misprint` |
| p. 301 | `P(s) → P` for every psd `P(0)`; uniqueness | `ls_riccati_main` |
| Proposition 9.3.2, p. 301 | `Q = L'L`, `(√βA, L)` observable or detectable | `LSProblem.proposition_9_3_2`, `ls_detects_of_observable`, `ls_detects_of_detectable`, `ls_tendsto_L`, `ls_tendsto_mulVec_zero` |
| p. 301 | `F x_t → 0`, `L x_t → 0`; the system (9.15); detectability: `x_{t+1} = (√βA − HL)x_t + …` | `ls_detects_of_detectable`, `ls_tendsto_zero_of_stable_input`, `ls_tendsto_zero_of_le_rec`, `ls_detects_of_observable` |
| p. 301 | Observability or detectability can be replaced by (9.10) | `ls_stable_of_side_condition` |
| pp. 298–301 | The limits give the value function and policy of the infinite-horizon problem | `LSProblem.ls_infinite_value`, `LSProblem.ls_verification` |
| pp. 299, 302 | `F(s) → F`, `d(s) → d = (1 − β)⁻¹β tr(PCC')` | `LSProblem.ls_F_tendsto`, `LSProblem.ls_G_tendsto`, `LSProblem.ls_N_tendsto`, `LSProblem.ls_dIter_tendsto` |
| (9.16)–(9.17), pp. 301–302 | General case `S ≠ 0` with uncertainty: `V(x) = −x'Px − d`, `u = −Fx` | `LSProblem.eq_9_16_9_17` |
| p. 302 | Value function iteration: "Proposition 9.3.1 gives an algorithm" | `LSProblem.proposition_9_3_1` (ii) |
| p. 302 | Policy improvement: the rewritten Riccati equation | `LSProblem.ls_policy_riccati` |
| pp. 302–303 | The Lyapunov step is solvable when the eigenvalues of `A − BF_j` are below `1/√β` | `LSProblem.ls_policy_lyapunov` |
| p. 303 | Lagrange method: first-order conditions and the linear system | `LSProblem.ls_lagrange` |
| p. 303 | Klein's method for the system (§2.3.2) | `LQKlein` (copied Chapter 2 module) |
| pp. 303–304 | Envelope condition, `λ_t = Px_t` | `LSProblem.ls_envelope`, `LSProblem.ls_lagrange` |

### Exercises (p. 325)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 9.1 | `ũ = u + R⁻¹S'x` normalises `S = 0` | `LSProblem.normS`, `LSProblem.ex_9_1_loss`, `LSProblem.ex_9_1_transition`, `LSProblem.ex_9_1` |
| Exercise 9.2 | The uncentered problem | `LSProblem.augment`, `LSProblem.ls_aug`, `LSProblem.ex_9_2_transition`, `LSProblem.ex_9_2_loss`, `LSProblem.ex_9_2` |
| Exercise 9.4 (Hall) | Setup with `x = [1, a, y]'` | `hallProblem`, `ex_9_4_loss`, `ex_9_4_transition`, `ex_9_4_jointPSD`, `ls_jointPSD_of_loss` |
| Exercise 9.4 | The Riccati solution and the optimal consumption rule | `ex_9_4_riccati`, `hallP`, `hallF`, `hallq`, `hallW`, `hallP_quad`, `ex_9_4_rule`, `ex_9_4_martingale`, `ex_9_4_closed_loop` |
| Exercise 9.4 | Optimality (deterministic) and the stochastic Bellman equation | `ex_9_4_optimal`, `ex_9_4_bellman` |
| Exercise 9.4 | The second psd solution `P = 0` (rule `c = b`) | `ex_9_4_zero_solution`, `ex_9_4_two_solutions` |

## §9.4–§9.5

### §9.4 Optimal policy under commitment

### The Ramsey problem and its first-order conditions (`CPRamsey`)

| Source | Claim | Lean |
| --- | --- | --- |
| (9.18), p. 304 | State-space form `D[z_{t+1}; E_t y_{t+1}] = A[z_t; y_t] + Bu_t + [Cε_{t+1}; 0]`, `D = [I 0; D₂₁ D₂₂]` | represented with `Z ⊕ Y`-indexed vectors (`cp_augmented`, `eq_9_22`) |
| (9.19), pp. 304–305 | Period loss `L_t` | `cpLoss` |
| p. 306 | Augmented system `D̄x_{t+1} = Āx_t + …` with `D̄ = [D 0]`, `Ā = [A B]` | `cpDbar`, `cpAbar`, `cp_augmented` |
| p. 306 | `L_t = ½x_t'Wx_t`, `W = [Q S; S' R]` | `cpW`, `eq_9_19_W` |
| p. 306 | The Lagrangian with multipliers `β^{t+1}μ_{t+1}` and initial term in `μ_{z0}` | `cpLagrangian`, `cpPerturb` |
| p. 306 | First-order conditions w.r.t. `z_t, y_t, u_t`: `x_t'W + μ_t'D̄ − βE_tμ_{t+1}'Ā = 0` | `cp_lagr_term`, `cp_lagrangian_perturb`, `cp_hasDerivAt`, `eq_foc_9_4`, `cpGrad`, `cpInit` |
| pp. 306–307 | `μ_{y0} = 0` ("no past promises"); `μ_{z0}` endogenous; date-0 condition has the same form | `cp_init_eq_Dbar`, `cp_grad_eq` |
| (9.22), p. 307 | FOCs + (9.18) = stacked system `[D̄ 0; 0 βĀ'][x; μ]_{t+1} = [Ā 0; W D̄'][x; μ]_t + [c; 0]` | `cpLeft`, `cpRight`, `eq_9_22` |
| — | Auxiliary dot-product identities | `cp_sumElim_dotProduct`, `cp_dotProduct_mulVec_comm`, `cp_dotProduct_mulVec_symm` |

### Saddle path, recursive form, time inconsistency (`CPSaddlePath`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 307 | `k_t = (z_t, μ_{yt})` predetermined, `λ_t = (y_t, u_t, μ_{zt})` non-predetermined; reorder (9.22) as `J E_t[k; λ]_{t+1} = H[k; λ]_t` | `cpReorder`, `cpColEquiv`, `cpRowEquiv`, `cpJ`, `cpH`, `cpCfin`, `cp_reordered_iff`, `cp_submatrix_id_mulVec`, `cp_comp_equiv_iff`, `cp_norm_comp_equiv` |
| p. 307 | Unique saddle-path solution under the stability and rank conditions (Klein, Ch. 2) | `cp_saddle_path` (via `theorem_1_4_5_real`) |
| pp. 307–308 | Solution form `z_{t+1} = A_zz z_t + A_zμ μ_{yt} + Cε_{t+1}`, `μ_{y,t+1} = …`, `y_t = …`, `u_t = …`, `μ_{zt} = …`; `μ_y` is a state variable | `cp_recursive_form` (via `klein_simplified_form`) |
| p. 308 | Time inconsistency: reoptimising at `t` sets `μ_{yt} = 0`; the plan changes unless `μ_{yt} = 0` | `cp_time_inconsistency` |

### Examples 9.4.1 and 9.4.2 (`CPNKCommitment`)

| Source | Claim | Lean |
| --- | --- | --- |
| Example 9.4.1, p. 305 | NK model (9.20)–(9.21) in the form (9.18) with predetermined `(1, z, Ŷ^f, r^n)`, forward `(π, x)`, instrument `i` | `ex941D`, `ex941A`, `ex941B`, `ex941C`, `example_9_4_1` |
| Example 9.4.1, p. 305 | `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` as a predetermined variable | `example_9_4_1_rn` |
| Example 9.4.1, p. 305 | Loss `½(π − π*)² + ½λx²` with unity in the state is of the form (9.19) | `ex941Q`, `example_9_4_1_loss` |
| Example 9.4.2, p. 309 | The Lagrangian | `ex942Lagr`, `cpPert`, `cp_pert_zero`, `cp_sum_delta`, `cp_sum_delta_sq`, `cp_sum_delta_succ`, `cp_hasDerivAt_quad`, `cp_stationary_iff` |
| (9.25), p. 309 | FOC in `π_t` (with `μ_{x0} = 0`) | `eq_9_25` |
| (9.26), p. 309 | FOC in `x_t` | `eq_9_26` |
| (9.27), p. 309 | FOC in `z_t` | `eq_9_27` |
| p. 310 | The `5 × 5` linear RE system | `ex942L`, `ex942R`, `example_9_4_2_system`; printed row: `ex942Lprinted`, `example_9_4_2_printed_row_false` |
| (9.28), p. 310 | Second-order difference equation in `μ_x` | `eq_9_28` |
| (9.29), p. 310 | Characteristic equation, real roots `0 < a₁ < 1 < a₂` | `ex942b`, `ex942a`, `ex942_b_eq`, `eq_9_29`; `κ = 0`: `eq_9_29_kappa_zero` |
| pp. 310–311 | Lag-operator solution, forward sum `−(1/(β²a₂))∑ a₂⁻ʲ(κx* + E_t z_{t+j})` | `ex942_lag_sum` |
| p. 311 | `μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))` solves (9.28) | `ex942Rule`, `ex942_rule_solves`, `ex942_rule_expected` |
| p. 311 | It is the bounded solution (inverting `L⁻¹ − a₂` forward) | `ex942_unique_bounded` |
| p. 311 | (9.25)–(9.27) then determine `π_t`, `x_t`, `μ_{zt}` | `ex942_solution`, `ex942_muz` |
| pp. 308, 311 | Time inconsistency in the example | `ex942_time_inconsistent` |

### §9.5 Optimal discretional policy

### Markov perfect equilibrium in linear rules (`CPDiscretion`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 311–313 | Model data (blocks of (9.18), (9.19), `β`, `Σ`) | `CPDisc`, `CPDisc.loss`, `CPDisc.mean`, `cp_disc_loss_eq` |
| (9.30), Definition 9.5.1, p. 311 | Linear rules `y = Mz`, `u = −Fz`; Markov perfect equilibrium; Bellman equation (9.31) | `IsMPE`, `definition_9_5_1`, `CPDisc.total` |
| (9.32)–(9.34), p. 312 | Public's rule `y_{t+1} = M_{t+1}z_{t+1}`; quadratic value `½z'Vz + ½v`; `E_t J_{t+1}` | `cp_expected_quadratic` |
| (9.35)–(9.36), p. 312 | Lower block with `E_t y_{t+1} = M_{t+1}E_t z_{t+1}` | `CPDisc.G`, `CPDisc.Feasible`, `eq_9_35_36`; counterexample `cpDiscEx`, `eq_9_36_false` |
| (9.37), p. 313 | `y_t = H_zt z_t + H_ut u_t` | `CPDisc.K`, `CPDisc.Hz`, `CPDisc.Hu`, `eq_9_37`, `eq_9_37_book` |
| (9.38), p. 313 | `z_{t+1} = A*_t z_t + B*_t u_t + ε_{t+1}` | `CPDisc.Ast`, `CPDisc.Bst`, `eq_9_38` |
| Step 2, p. 313 | `L_t = ½z'Q*z + ½u'R*u + z'S*u` | `CPDisc.Qst`, `CPDisc.Rst`, `CPDisc.Sst`, `eq_step2`, `cp_dot_left`, `cp_quad_transpose`, `cp_dot_swap`; `CPDisc.Qbook`, `cp_Qbook_quad`; counterexamples `cpDiscEx2`, `step2_book_S_false`, `step2_book_R_false` |
| (9.39), p. 314 | The period control problem | `cpObj`, `cp_obj_expand`, `cp_total_eq` |
| (9.40), p. 314 | `u_t = −F_t z_t`, `F_t = (R* + βB*'VB*)⁻¹(S*' + βB*'VA*)` | `cpGain`, `cpF`, `cp_obj_complete_square`, `eq_9_40` |
| (9.41), p. 314 | `V_t = Q* + F'R*F − 2S*F + β(A* − B*F)'V_{t+1}(A* − B*F)`; `v_t = β tr(V_{t+1}Σ) + βv_{t+1}` | `cpVbook`, `eq_9_41`; symmetric form `cpVnext`, `cp_Vnext_quad`, `cp_Vnext_symm`, `cp_Qst_symm`, `cp_Rst_symm` |
| (9.42), p. 314 | `M_t = H_zt − H_ut F_t` | `eq_9_42` |
| (9.33), pp. 312–314 | One backward-induction step solves the period-`t` Bellman equation | `CPDisc.Fnext`, `CPDisc.Vnext`, `CPDisc.Mnext`, `CPDisc.Gain`, `cp_bellman_step` |
| pp. 314–315 | The limit of the iteration gives a Markov perfect equilibrium | `cp_mpe_of_fixed_point` (fixed point ⇒ MPE; convergence not formalised) |

### Example 9.5.1 and the comparison (`CPNKDiscretion`)

| Source | Claim | Lean |
| --- | --- | --- |
| (9.43), p. 315 | Static problem solved by `π = λ/(κ² + λ)(κx* + βπᵉ + z)` | `ex951θ`, `ex951θ_pos`, `ex951θ_le_one`, `eq_9_43` |
| p. 315 | MPE: `π(z)` from (9.43) at `πᵉ(z)`, `πᵉ(z) = E_tπ(z_{t+1})` | `IsMPE951`, `ex951pi`, `ex951_denoms`, `example_9_5_1`, `example_9_5_1_unique` |
| p. 315 | `π_t = λ/(κ² + λ)(κx* + βE_tπ_{t+1} + z_t)` solved forward: `π_t = θ∑ βʲθʲ[κx* + E_t z_{t+j}]` | `ex951_forward`, `ex951_series` |
| §§9.4–9.5 | Commitment vs discretion: commitment inflation `a^{t+1}κx*/(1 − βa) → 0`; discretionary inflation bias `λκx*/(κ² + (1 − β)λ)` | `cp_commitment_vs_discretion` |

## §9.6 (Robust Control) and Exercises 9.3, 9.5

### Standard form and belief distortions (pp. 315–318)

| Source | Claim | Lean |
| --- | --- | --- |
| (9.44), p. 316 | `max E∑βᵗr(x_t, u_t)` s.t. `x_{t+1} = f(x_t, u_t, ε_{t+1})` | No formal content (the data `r`, `f` of `eq_9_49`) |
| pp. 316–317 | One-step ratios `m_{t+1} = π̂(ε_{t+1}\|ε^t)/π(ε_{t+1})`; `E[m_{t+1}\|ε^t] = 1` | `rc_lr_mean_one`, `RCRatios` |
| p. 317 | `M_0 = 1`, `M_{t+1} = m_{t+1}M_t = ∏ m_j` | `rcM`, `rcM_zero`, `rcM_succ`, `rcM_measurable`, `rcM_nonneg`, `rcM_le` |
| p. 317 | `{M_t}` is a martingale | `rc_martingale`, `rc_one_step`, `rc_tower`, `rc_integral_M` |
| p. 317 | `{M_t}` induces a distorted measure `Q`; `E^Qφ(ε^t, x₀) = E[M_tφ(ε^t, x₀)]` | `rcQ`, `rc_distorted_integral`, `rcQ_isProbability`, `rc_distorted_consistent` |
| p. 317 | Relative entropy `E^Q[ln dQ/dP\|_{ε^t}] = E[M_t ln M_t]` | `rc_rnDeriv`, `rc_relEntropy`, `rc_MlogM_integrable` |
| p. 317 | Relative entropy is nonnegative, zero iff `M_t = 1` or `Q = P` | `rc_entropy_nonneg`, `rc_entropy_eq_zero_iff`, `rcQ_eq_iff` |
| p. 317 | `E[M_t ln M_t] = ∑_{j<t} E[M_jE(m_{j+1} ln m_{j+1}\|ε^j)]` | `rc_entropy_decomp`, `rcG`, `rc_increment_eq`, `rcG_measurable`, `rcG_abs_le`, `rcG_integrable`, `rc_abs_mul_log_le`, `rc_integrable_of_bound`, `rc_m_integrable`, `rcM_integrable`, `rcM_bound`, `RCRatios.K_nonneg` |
| p. 318 | `E(m_{t+1} ln m_{t+1}\|ε^t)` is a conditional relative entropy (nonnegative) | `rc_increment_nonneg` |
| p. 318 | `(1 − β)∑βʲE[M_j ln M_j] = β∑βʲE[M_jE(m_{j+1} ln m_{j+1}\|ε^j)]` | `rc_discounted_entropy`, `rc_discounted_sum` |
| (9.45), p. 318 | The entropy constraint `β∑βʲE[M_jE(m_{j+1} ln m_{j+1}\|ε^j)] ≤ η₀` | `rcDiscEntropy`, `rcEntropyConstraint`, `rc_discEntropy_nonneg` |

### Two robust control problems (pp. 318–319)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 318 | The constraint problem `max_u min_m E^Q∑βᵗr` s.t. (9.44), (9.45) | Abstract form in `rc_lagrange`, `rc_weak_duality` |
| p. 318 | The multiplier problem | `rcMultObj` |
| (9.46), p. 319 | The multiplier objective as `E∑βᵗM_t(r_t + βθE(m_{t+1} ln m_{t+1}\|ε^t))` | `eq_9_46` (finite horizon), `rc_tower_sum` |
| p. 319 | `θ` is the Lagrange multiplier of (9.45) | `rc_lagrange`, `rc_weak_duality` |
| p. 319 | As `θ → ∞` no distortion is optimal and the multiplier problem converges to the standard problem | `rc_mult_tendsto`, `rc_mult_lower`, `rc_sqrt_penalty`, `rc_mult_le_ref`; LQ case Exercise 9.3 (`ex_9_3`) |
| p. 319 | Smaller `θ`: more concern about misspecification | `rc_mult_mono` |
| p. 319 | `θ` as ambiguity aversion (Chapter 20) | Not formalised (Chapter 20) |
| p. 319 | The breakdown point: below it the minimising agent pushes the objective to `−∞` | `rc_breakdown` (LQ), `rc_nonsingular_not_enough`, `ex_9_5_breakdown` |

### Recursive formulation (pp. 319–321)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 320 | Conjecture `W(M, x) = MV(x)`; dividing the Bellman equation by `M` | `rc_bellman_scale`, `rc_bellman_divide`, `rc_min_add` |
| p. 320 | The inner problem `min_m ∫(mV(f) + θ m ln m)π` s.t. `E m = 1` | `rcAdm`, `rcObj` |
| p. 320 | First-order condition (corrected: `ln m*(ε) = −V(f)/θ + λ`) | `eq_9_47_foc`, `eq_9_47_log`; misprint `eq_9_47_misprint` |
| (9.47), p. 320 | `m*(ε) = exp(−V(f)/θ)/∫exp(−V(f)/θ)π` | `rcWorst`, `rcZ`, `eq_9_47_9_48`, `rcZ_pos`, `rcWorst_pos`, `rcWorst_log`, `rc_mul_log_sub` |
| (9.48), p. 320 | `R(V) = −θ ln ∫exp(−V(f)/θ)π` (the minimum, uniquely attained at `m*`) | `rcR`, `eq_9_47_9_48` |
| p. 320 | The risk-sensitive adjustment; `1/θ` enhances risk aversion | `rc_R_le_mean` |
| (9.49), p. 320 | `V(x) = max_u {r(x, u) + βR(V)(x, u)}` | `eq_9_49` |
| pp. 320–321 | Risk-sensitive control; recursive utility (Epstein–Zin; Hansen–Sargent 1995) | No formal content |

### Linear-quadratic model with Gaussian disturbances (pp. 321–323)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 321 | `r(x, u) = −½(x'Qx + u'Ru + 2x'Su)`, transition (9.1), IID Gaussian shocks | `rcRobObj`, `RCGaussian` |
| p. 321 | The IID standard normal shock satisfies the Gaussian integral identity used below | `rc_gaussian_std`, `rc_gauss_1d`, `rc_std_map_eigen` |
| (9.50), p. 321 | `V(x) = −½x'Px − d/2` | `rcV` |
| p. 321 | `m*(ε) ∝ exp(ε'C'PCε/(2θ) + ε'C'P'(Ax + Bu)/θ)` | `rc_worst_ratio`, `rc_exponent` |
| p. 321 | `π*(ε) ∝ exp(−½ε'(I − θ⁻¹C'PC)ε + ε'(I − θ⁻¹C'PC)(θI − C'PC)⁻¹C'P(Ax + Bu))` | `rc_worst_exponent` |
| p. 321 | `π*` is normal with mean `(θI − C'PC)⁻¹C'P(Ax + Bu)` and covariance `(I − θ⁻¹C'PC)⁻¹` | `rc_worst_density`, `rcWstar`, `rcK`, `rcGaussPdf`, `rcStdPdf`, `rcStdPdf_eq` |
| p. 321 | "We must assume `I − θ⁻¹C'PC` nonsingular" (corrected: positive definite) | `rc_nonsingular_not_enough`, `rcK_posDef_iff` |
| p. 322 | `R(V) = ∫Vπ* + θ∫π* ln(π*/π) = −½(Ax + Bu)'[P + PC(θI − C'PC)⁻¹C'P](Ax + Bu) − d/2 − (θ/2) ln det(I − θ⁻¹C'PC)⁻¹` | `rc_R_first_line` |
| p. 322 | Alternatively from the second line of (9.48) | `rc_R_quad`, `rc_R_quad_std`, `rc_R_lines_agree` |
| p. 322 | The operator `D(P) = P + PC(θI − C'PC)⁻¹C'P` | `rcD`, `rcH`, `rcD_transpose`, `rcD_quad`, `rcD_posSemidef`, `rcH_transpose`, `rcK_eq_smul`, `rcH_eq_smul`, `rcK_inv` |
| p. 322 | Substituting into (9.49): the Bellman equation with `D(P)` | `rc_robObj_eq`, `rc_outer_eq` |
| (9.51)–(9.52), p. 322 | First-order condition: `u = −Fx`, `F = (R + βB'D(P)B)⁻¹(S' + βB'D(P)A)` | `rc_robObj_max`, `eq_9_51_9_55`, `eq_9_51_9_55_std` |
| (9.53)–(9.55), pp. 322–323 | Matching coefficients: `P = T∘D(P)`, `T` as in (9.11), `d = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'PC)⁻¹` | `eq_9_51_9_55`, `rc_bellman_converse`, `rcd`, `LSProblem.T` |
| pp. 320–323 | The robust Bellman equation with the minimisation over all likelihood ratios | `rc_robust_bellman`, `rc_robust_bellman_std`, `rcV_comp_measurable` |
| p. 323 | "Note that `T` is identical to that in (9.11)" | By definition (`LSProblem.T`) |
| p. 323 | Summary of the algorithm (value iteration on `T∘D`) | No formal content |

### Relative entropy and normal distributions (pp. 323–324)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 323 | `ln(π̂/π) = ½(−(ε − w)'Σ⁻¹(ε − w) + ε'ε − ln det Σ)` | `rc_llr_normal` |
| p. 323 | `−∫½(ε − w)'Σ⁻¹(ε − w)π̂ = ½ tr(I)` (corrected: `−½ tr(I)`) | `rc_moment_half`, `rc_moment_trace_inv`, `rc_moment_quad`, `RCMoments`; misprint `rc_moment_sign_misprint` |
| p. 323 | `½ε'ε = ½w'w + ½(ε − w)'(ε − w) + w'(ε − w)` | `rc_half_sq_split` |
| p. 324 | `∫½ε'επ̂ = ½w'w + ½ tr(Σ)` | `rc_half_sq_moment` |
| (9.56), p. 324 | `∫π̂ ln(π̂/π) = ½w'w − ½ ln det Σ + ½ tr(Σ − I)` | `eq_9_56` |
| p. 324 | First term: mean distortion; last two: variance distortion | No formal content |

### Modified certainty equivalence principle (pp. 324–325)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 324 | The deterministic problem `x_{t+1} = Ax_t + Bu_t + Cw_t` | `rc_modified_ce` |
| p. 324 | `min_w −½(Ax + Bu + Cw)'P(Ax + Bu + Cw) + (θ/2)w'w`: `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` | `rc_mce`, `rc_mce_decomp`, `rc_mce_expand`, `rcWstar` |
| p. 324 | `w*` is the mean of the worst-case normal `π*` | `rcWstar` (same expression in `rc_mce` and `rc_worst_density`) |
| p. 324 | The minimised objective is `−½(Ax + Bu)'D(P)(Ax + Bu)`, the quadratic part of `R(V)` | `rc_mce`, `rc_R_quad` |
| p. 325 | The worst-case covariance and the constant do not affect `P` or the robust rule | `rc_modified_ce` |
| p. 325 | Unlike the standard problem, `C` affects both the decision rule and `P` | `rc_C_matters`, `rcScalarProblem`, `rc_inv_fin_one` |

### Exercises (pp. 325–326)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 9.3 | As `θ → ∞`, (9.52)–(9.55) converge to the standard solution | `ex_9_3`, `ex_9_3_unique`, `rc_D_tendsto`, `rc_d_tendsto`, `rc_T_F_tendsto`, `rc_log_det_bounds`, `rc_posSemidef_of_tendsto`, `rc_tendsto_mul`, `rc_tendsto_inv`, `rc_tendsto_smul`, `rc_inv_smul` |
| Exercise 9.5 | Hall's problem in the normalisation of §9.6 | `rcHallRobust`, `ex_9_5_loss`, `ex_9_5_data` |
| Exercise 9.5 | The robust Riccati solution `P = 2q_θww'` and gain | `ex_9_5`, `rcHallK`, `rcHallQθ`, `rcHallRank1`, `rcHallPθ`, `rcHallGain`, `rc_hall_rank1_T`, `rc_hall_rank1_D` |
| Exercise 9.5 | The robust consumption rule | `ex_9_5_rule`, `ex_9_5_hall_case` |
| Exercise 9.5 | The robust Bellman equation | `ex_9_5_bellman`, `ex_9_5_bellman_std` |
| Exercise 9.5 | Breakdown point `θ = 2k`; limit `q_θ → q`; `q_θ > q` | `ex_9_5_breakdown`, `ex_9_5_limit`, `ex_9_5_more_responsive` |
