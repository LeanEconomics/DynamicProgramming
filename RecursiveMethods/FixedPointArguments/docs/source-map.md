# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 17, pp. 501–541. Equation numbers restart in each section, as in the book. The
model-specific results are Propositions 1–8, without the chapter prefix, as in the book. Lean names
are relative to `StokeyLucasPrescott.FixedPointArguments`. Where the Lean statement departs from
the book, see [corrections](corrections.md). The proof of Theorem 17.3 follows C. A. Rogers, "A
less strange version of Milnor's proof of Brouwer's fixed-point theorem", *American Mathematical
Monthly* 87 (1980), which simplifies J. Milnor, *Topology from the Differentiable Viewpoint* (1965).

## Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 501–502 | Three kinds of recursive models; when the welfare theorems fail there is no general approach; four fixed-point tools; plan of the chapter | Not formalised (overview) |

## §17.1 An overlapping-generations model

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 502–503 | Two-period lives, `U(l, c) = −H(l) + V(c)`, output `x l`, fiat money `M`; the economy is not covered by Chapter 15 ("why not?") | The economy enters only through (1)–(2); the question is not formalised |
| p. 503 | `X = [a, b] ⊂ ℝ₊₊` with its Borel sets and a transition function `π` | `X = Icc a b`, `π : Kernel X X` (convention) |
| (1)–(2), p. 503 | Stationary competitive equilibrium with valued money `(p, n)` | `IsStationaryEqm` |
| Assumption 17.1, p. 503 | `H` on `[0, L)`: `C²`, strictly increasing, strictly convex, `H′(0) = 0`, `H′ → ∞` at `L`; `V` on `ℝ₊`: `C²`, strictly increasing, strictly concave | `Assumption17_1`, `Assumption17_1H`, `Assumption17_1V`; consequences `Assumption17_1H.H'_strictMonoOn`, `Assumption17_1H.H'_pos`, `Assumption17_1H.H''_nonneg`, `Assumption17_1H.exists_H'_gt`, `Assumption17_1V.V'_pos`, `Assumption17_1V.V'_strictAntiOn`, `Assumption17_1V.V'_le_V'_zero`. Copies: `FPAssumption17_1` (§§17.3–17.4), `MonoAssumption17_1` (§17.5) |
| Exercise 17.1, p. 504 | For `p` measurable and bounded away from zero, (1) has a unique solution `n(x) > 0`, characterised by the first-order condition | `ex_17_1`; abstract form `consumer_problem`, with `hasDerivAt_utility`, `margUtil`, `margUtil_strictAntiOn`, `exists_unique_foc` |
| (3), p. 504 | `n H′(n) = ∫ x′ n(x′) V′[x′ n(x′)] π(x, dx′)`; a strictly positive measurable solution of (3) gives an equilibrium with `p = M/(x n)` | `eq3_of_isStationaryEqm` (equilibrium ⇒ (3)), `isStationaryEqm_of_eq3` ((3) ⇒ equilibrium, for `n : X → (0, L)`) |
| (4), p. 504 | `ζ(l) = l H′(l)`, `φ(y) = y V′(y)`; (3) is `ζ[n(x)] = ∫ φ[x′ n(x′)] π(x, dx′)` | `olgZeta`, `olgPhi`, `eq3_iff_eq4` |
| (5), p. 504 | Serially independent shocks: `ζ(n) = ∫ φ(x′ n) π(dx′)` | The equation of `proposition_1` |
| Proposition 1, p. 505 | (5) has exactly one solution `n ∈ (0, L)` | `proposition_1`; under the repaired utility assumption, `proposition_1_repaired` |
| (6), p. 505 | `l ζ′(l)/ζ(l) ≥ 1`, "with equality only at `l = 0`" | `zeta_elasticity_ge_one`; the equality claim: `proposition_1_elasticity_counterexample`, with `olgExH`, `olgExH_assumption` |
| (7), p. 505 | `y φ′(y)/φ(y) ≤ 1`, "with equality only at `y = 0`" | Not used: the uniqueness step is proved without it (`proposition_1_logRatio_strictMonoOn`). Under Assumption 17.4 the two-sided bound is `ex_17_14c_phi` |
| Figure 17.1 and step 4, pp. 505–506 | Existence: the cases `φ(0) > 0` and `φ(0) = 0`; the intermediate value theorem | `exists_unique_foc`; the first case cannot occur: `proposition_1_phi_zero_counterexample` |
| Step 5, pp. 506–507 | Uniqueness: the `ζ` curve crosses `E φ(x′ l)` from below at every intersection | `proposition_1_logRatio_strictMonoOn` |
| p. 507 | `ζ : [0, L) → ℝ₊` is a continuous increasing bijection; `ζ⁻¹` is continuous and strictly increasing | `olgZetaInv`, `Assumption17_1H.zeta_strictMonoOn`, `Assumption17_1H.zeta_continuousOn`, `Assumption17_1H.zeta_surj`, `Assumption17_1H.zetaInv_mem`, `Assumption17_1H.zeta_zetaInv`, `Assumption17_1H.zetaInv_zeta`, `Assumption17_1H.zetaInv_strictMonoOn`, `Assumption17_1H.zetaInv_continuousOn`, `Assumption17_1H.zeta_hasDerivAt`, `Assumption17_1H.zetaInv_hasDerivAt` |
| (8)–(9), p. 507 | `f* = ζ ∘ n*` solves (8) iff `n*` solves (4); `f*` is a fixed point of `T` | `eq8_iff_eq4`; the operator (9): `olgOpT` with the kernel `olgG`, and `monoOLGOp` |
| (10), pp. 507–508 | Plan of §§17.2–17.6; the finite-state operator `T_i f = Σ_j φ[x_j ζ⁻¹(f_j)] π_ij` | The plan is not formalised; (10) is the system of `proposition_3` |

## §17.2 An application of the Contraction Mapping Theorem

| Source | Claim | Lean |
| --- | --- | --- |
| (1), p. 509 | `(Tf)(x) = ∫ G[x, x′, f(x′)] π(x, dx′)` on the bounded continuous `f : X → D` | `olgOpT`, `olgF`, `OLGOperatorHyp`, `IsFellerKernel`, `isFellerKernel_deterministic_id` |
| Exercise 17.2(a), p. 509 | `D` convex, `G` continuous, `π` Feller ⇒ `T : F → F` | `ex_17_2a_counterexample`, `ex_17_2a_counterexample_bounded`; corrected (compact `X`): `ex_17_2a`, `olgTF`, `olgTF_apply` |
| Exercise 17.2(b), p. 509 | `D` closed ⇒ `F` is complete | `isClosed_olgF`, `ex_17_2b` |
| Lemma 17.1, (2), pp. 509–510 | `\|G₃\| ≤ β < 1` ⇒ `T` is a contraction of modulus `β`, with a unique fixed point and `‖Tⁿf₀ − f*‖ ≤ βⁿ‖f₀ − f*‖` | `olgTF_lipschitz`, `lemma_17_1` |
| Exercise 17.3, p. 510 | The OLG kernel `G(x, x′, y) = φ[x′ ζ⁻¹(y)]` violates (2) | `ex_17_3` |
| (3), pp. 510–511 | `D̂ = ln D`, `F̂`, `(T̂g)(x) = ln ∫ G[x, x′, e^{g(x′)}] π(x, dx′)`; `D̂` closed and convex | `olgDhat`, `olgDhat_eq`, `exp_mem_of_mem_olgDhat`, `olgDhat_isClosed`, `olgDhat_convex`, `olgOpThat` |
| Exercise 17.4(a), p. 511 | `T̂ : F̂ → F̂` | `ex_17_4a_counterexample`; corrected (compact `X`): `ex_17_4a`, `olgThatF`, `olgThatF_apply` |
| Exercise 17.4(b), p. 511 | `F̂` is complete | `ex_17_4b` |
| Lemma 17.2, (4), pp. 511–512 | `\|y G₃/G\| ≤ β < 1` ⇒ `T̂` is a contraction of modulus `β` | `abs_log_G_sub_le`, `olgThatF_lipschitz`, `lemma_17_2`; for `T`: `lemma_17_2_fixedPoint` |
| p. 512 | `T̂[ln f] = ln(Tf)`; the two lemmas concern the same sequence in two metrics | `olgOpThat_log`; the comparison of metrics (pp. 512–513) is a remark, not formalised |
| Assumption 17.2, (5), p. 513 | `1 − β ≤ −yV″(y)/V′(y) ≤ 1 + β` on `ℝ₊` | `Assumption17_2`, `assumption17_2_counterexample`, `assumption17_2R_inconsistent`; `MonoAssumption17_2`, `not_monoAssumption17_2`. Repair: `Assumption17_2R`, `Assumption17_1VR`, `crra_assumption17_1VR`, `crra_assumption17_2R`, `repaired_assumptions_nonvacuous` |
| Proposition 2, (6), p. 513 | Feller `π`, Assumptions 17.1–17.2 ⇒ a unique bounded continuous strictly positive solution of (6) | `proposition_2` (repaired assumptions); `proposition_2_zero_fixedPoint`, `proposition_2_nonneg_counterexample` |
| Proof of Proposition 2, step 1 and Figure 17.2, p. 514 | `ε_k = min{ε > 0 : ζ⁻¹(ε) = kε}`, strictly decreasing | `epsK_exists`; `monoEpsK`, `MonoAssumption17_1H.epsK_spec`, `MonoAssumption17_1H.exists_lt_zetaInv` |
| (7), p. 514 | `φ[x′ ζ⁻¹(y)] > ε_K` for `y ≥ ε_K` | `olgG`, `olgG_ge`; also `fp_bounds` |
| Proof of Proposition 2, steps 3–5, pp. 514–515 | `D = [ε_K, ∞)`; the hypotheses of Exercise 17.4; condition (4) | `olgMargBCF`, `olgG_hyp`, `olgG_hasDerivAt`, `olgG_elasticity_le` |
| Proof of Proposition 2, step 6, p. 515 | "Any `K > 1/C` could have been used", so the solution is unique | `epsK_tendsto_zero`; `proposition_2` |
| pp. 515–516 | Assumption 17.2 as bounds `ε`, `2 − ε` on relative risk aversion; Assumption 17.1 makes it strictly positive; Figure 17.3 | `monoRRA`, `rra_pos_counterexample`, `monoRRA_zero`, `monoRRA_not_forall_pos`, `monoRRA_pos_counterexample`, `monoRRA_interior_zero_counterexample` (with `monoCexW`, `monoCexW_assumption17_1V`); corrected: `MonoAssumption17_1V.rra_nonneg`, `MonoAssumption17_1V.exists_rra_pos`. Figure 17.3 is not formalised |

## §17.3 The Brouwer Fixed-Point Theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Figure 17.4, p. 516 | A continuous self-map of `[0, 1]` has a fixed point | Special case of `theorem_17_3`; not stated separately |
| Theorem 17.3, p. 517 | A continuous self-map of a nonempty, closed, bounded, convex subset of a finite-dimensional normed space has a fixed point (stated without proof) | `theorem_17_3`. Proof: `exists_polynomial_det_id_add_smul`, `integral_eq_of_polynomial_of_eq_on_Ioc`, `isUnit_id_add_smul`, `no_C1_retraction` (module `BrouwerRetraction`); `C1Restrictions`, `exists_C1_approx_real`, `exists_C1_approx`, `brouwer_closedBall`, `brouwer_ball` (module `BrouwerBall`); `exists_lipschitz_retraction`, `brouwer_inner`, `brouwer`, `brouwer_subtype` (module `Brouwer`) |
| p. 517 | Finite `X`, stochastic matrix `Π`, compact interval `D`: `(Tf)_i = Σ_j G(x_i, x_j, f_j) π_ij` has a fixed point in `Dᵐ` | `brouwer_finite_state` |
| p. 518 | Logarithms do not help with Brouwer | `brouwer_log_transform_fixedPoint_iff`, `log_image_isCompact_convex`, `exp_image_log_image` |
| p. 518 | There may be an equilibrium with zero labour; `F` must bound labour away from zero and be bounded above | `proposition_3_zero_fixedPoint` |
| pp. 503–507, as used in §§17.3–17.4 | Assumption 17.1, `ζ`, `φ` and `ζ⁻¹` again | `FPAssumption17_1`, `fpZeta`, `fpPhi`, `fpZetaInv`, `fpA_H'_strictMonoOn`, `fpA_H'_pos`, `fpA_H'_nonneg`, `fpA_H'_continuousOn`, `fpA_V'_pos`, `fpA_V'_strictAntiOn`, `fpA_V'_continuousOn`, `fpZeta_zero`, `fpZeta_nonneg`, `fpZeta_strictMonoOn`, `fpZeta_continuousOn`, `fpZeta_exists_gt`, `fpZeta_surjOn`, `fpZetaInv_mem`, `fpZeta_zetaInv`, `fpZetaInv_zeta`, `fpZetaInv_zero`, `fpZetaInv_strictMonoOn`, `fpZetaInv_continuousOn`, `fpPhi_continuousOn`, `fpPhi_zero`, `fpPhi_nonneg`, `fpPhi_comp_continuousOn` |
| Proposition 3, (1)–(2), pp. 518–519 | Finitely many states in `ℝ₊₊`: a strictly positive solution of `f*_i = Σ_j φ[x_j ζ⁻¹(f*_j)] π_ij` exists | `proposition_3`, with `fp_bounds`, `fp_finite_states_bounds` |
| p. 519 | With endogenous states a finite state space is less tenable | Not formalised (remark) |

## §17.4 The Schauder Fixed-Point Theorem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 519 | `X ⊆ ℝˡ` bounded, `C(X)` the bounded continuous functions with the sup norm | `X →ᵇ ℝ` |
| Definition, p. 520 | An equicontinuous family in `C(X)` | The hypothesis of `theorem_17_4` (the book's `ε`–`δ` form); elsewhere Mathlib's `UniformEquicontinuous` |
| Theorem 17.4, p. 520 | Schauder: `F ⊆ C(X)` nonempty, closed, bounded, convex, `T : F → F` continuous, `T(F)` equicontinuous ⇒ a fixed point (stated without proof) | `theorem_17_4`. Proof: `exists_approx_fixed_point`, `schauder`, `schauder_subtype`, `schauder_closed`, `schauder_closed_subtype` (module `Schauder`); `totallyBounded_of_equicontinuous` (module `SchauderBoundedContinuous`) |
| Exercise 17.5(a), p. 520 | `x′ = f(x)`, `x(0) = c`, `f` continuous, has a solution on `[0, 1]` | `ex_17_5a_counterexample`, `ex_17_5a_false`, `ex_17_5a_blowup_solution`; corrected: `fpOdeOp`, `fp_ode_exists`, `ex_17_5a_local`, `ex_17_5a_of_bounded` |
| Exercise 17.5(b), p. 520 | Two solutions of `x′ = √x`, `x(0) = 0` | `ex_17_5b`, `ex_17_5b_family`, `ex_17_5b_manual_counterexample` |
| Exercise 17.5(c), p. 520 | Which condition of "Exercise 3.8" fails | `ex_17_5c` (the Lipschitz condition of Exercise 3.10) |
| Assumption 17.3, pp. 520–521 | `x ↦ π(x, ·)` is uniformly continuous in the total-variation norm | `FPAssumption17_3`, `FPIsFinPartition`, `fpTVNorm`, `fpIsFinPartition_univ`, `fpTVNorm_bddAbove`, `fpTVNorm_nonneg`, `fp_le_tvNorm_pair`, `fp_abs_integral_sub_le_of_le`, `fp_abs_integral_sub_le`, `fpAssumption17_3_const`. Copy for §17.5: `MonoAssumption17_3`, `IsFinMeasPartition`, `TVDistLE`, `isFinMeasPartition_pair`, `abs_integral_sub_le_of_le`, `abs_integral_sub_le_of_tvDistLE` |
| Lemma 17.5, (1)–(2), pp. 521–522 | Under Assumption 17.3, with `G` uniformly continuous in its first argument, `T(F)` is bounded and equicontinuous | `fpIntOp`, `fp_integrand_continuous`, `fp_G_bound`, `lemma_17_5`; copy: `uniformEquicontinuous_integral`, `continuous_integral_of_assumption17_3`, `measurable_kernelIntegrand`, `kernelIntegral_uniformEquicontinuous` |
| Exercise 17.6, p. 522 | `G` uniformly continuous in its third argument ⇒ `T` continuous | `ex_17_6`; copy: `kernelIntegral_dist_le` |
| p. 522, pp. 524–525 | Schauder applies to (1) once `T(F) ⊆ F`, equicontinuity and continuity hold | `fp_exists_fixedPoint_intOp` |
| Proposition 4, (3)–(5), pp. 522–524 | Assumptions 17.1 and 17.3 ⇒ a continuous strictly positive solution exists | `proposition_4`, with `fp_bounds`; `proposition_4_zero_fixedPoint` |
| pp. 524–525 | Schauder versus Brouwer and the contraction route; Proposition 2 "did not require any restrictions on `π`"; logarithms do not help | Not formalised (discussion); `proposition_2` assumes the Feller property |
| Exercise 17.7, p. 525 | `n* = ζ⁻¹[∫ φ(x′ n*(x′)) π(x, dx′)]` characterises an equilibrium ("Why?"); the operator has a fixed point | `fpLabourOp`, `ex_17_7_why_of_f`, `ex_17_7_why_of_n`, `ex_17_7_zero`; corrected: `ex_17_7` |

## §17.5 Fixed points of monotone operators

| Source | Claim | Lean |
| --- | --- | --- |
| p. 525 | Contractions give existence, uniqueness and an algorithm; Brouwer and Schauder give only existence | Not formalised (remark) |
| Lemma 17.6, (1)–(9), pp. 526–528 | `F` closed, `T : F → F` continuous, `T(F)` equicontinuous: a pointwise limit of `Tⁿf₀` is in `F` and is a fixed point | `cauchySeq_of_uniformEquicontinuous`, `lemma_17_6` |
| Definition, p. 528 | Monotone operator | `isMonotoneOperator`, `isMonotoneOperator_iff_monotoneOn`, `bcf_le_iff` |
| Theorem 17.7, p. 528 | `F` closed and bounded, `T` continuous and monotone, `T(F)` equicontinuous, `f₀ ≤ Tf₀` or `f₀ ≥ Tf₀` ⇒ `Tⁿf₀` converges to a fixed point in `F` | `monotone_iterate_of_le`, `antitone_iterate_of_ge`, `exists_abs_le_of_isBounded`, `theorem_17_7_of_le`, `theorem_17_7_of_ge`, `theorem_17_7`; for bounded `X ⊆ ℝˡ`: `totallyBounded_univ_of_isBounded`, `theorem_17_7_of_isBounded` |
| Corollary, p. 529 | Iteration from the least and greatest elements of `F` gives fixed points `f ≤ h ≤ g` for every fixed point `h ∈ F`; if `f = g` it is unique | `le_of_tendsto_bcf`, `ge_of_tendsto_bcf`, `corollary_17_7_least`, `corollary_17_7_greatest`, `corollary_17_7`, `corollary_17_7_unique` |
| p. 529 | General application: `D = [c, d]`, `G` continuous, uniformly continuous in its first and third arguments, nondecreasing in the third | `kernelOp`, `kernelOp_apply`, `kernelOp_apply_of_continuous`, `kernelOp_monotone_fixedPoints` |
| Assumption 17.4, p. 530 | `−yV″(y)/V′(y) ≤ 1` on `ℝ₊` | `MonoAssumption17_4`, `MonoAssumption17_1V.monotoneOn_phi`; on `ℝ₊₊`: `MonoAssumption17_4Pos` |
| p. 530 | Assumption 17.1 implies `0 < −yV″/V′`; Assumption 17.2 restated; 17.4 drops the lower bound and strengthens the upper one | `monoRRA_pos_counterexample`, `monoRRA_interior_zero_counterexample`, `MonoAssumption17_1V.rra_nonneg`, `MonoAssumption17_1V.exists_rra_pos`; comparison as for p. 541 |
| Proposition 5, p. 530 | `T` has at least one fixed point; the iterates from `ε_K` and `B` converge to fixed points; if they agree, that is "the unique fixed point of `T`" | `MonoAssumption17_1`, `monoZeta`, `monoPhi`, `monoZetaInv`, `monoEpsK`, `monoB`, `monoF`, `monoOLGKernel`, `monoOLGOp`, `monoOLGOp_apply`, `monoOLG_bounds`, `proposition_5`; `monoOLGOp_zero`, `proposition_5_literal_false`, `proposition_5_counterexample` (with `monoCex_assumption17_1`, `monoCexV_assumption17_4`, `monoCexπ_assumption17_3`, `monoCex_fixedPoint_unique_pos`); corrected: `monoOLG_fixedPoint_mem`, `proposition_5_corrected`, `proposition_5_corrected'` |
| p. 531 | Other applications of monotonicity are in Chapter 18 | Not formalised (remark) |

## §17.6 Partially observed shocks

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 531–532 | The islands economy: two islands, shares `θ/2` and `1 − θ/2` of the young, monetary transfers `x`, shocks `(x, θ)` i.i.d. with distributions `Ψ`, `G` | Not formalised as an economy |
| Assumption 17.5, p. 532 | `X = [x̲, x̄] ⊂ ℝ₊₊`, `Θ = [θ̲, θ̄] ⊂ (0, 2)`, continuous densities `ψ`, `g` | `ShocksAssumption17_5` |
| p. 532 | Shocks observed with a lag; `P_t = M_t p(x_t, θ_t)` | Not formalised |
| (1)–(2), pp. 532–533 | Stationary equilibrium `(p, n)` of the islands economy | Not formalised; (1) and (2) enter `p533_ratio_of_price` and `p533_counterexample` as premises (`n = N ∘ p`, `n p = x/θ`) |
| p. 533 | Equal prices give equal `x/θ`; "any equilibrium must be of the form" `p = ρ(x/θ)`, `n = η(x/θ)` | `p533_ratio_of_price`, `p533_counterexample` |
| pp. 533–534 | `Z = [x̲/θ̄, x̄/θ̲]`; the distribution `Π` and density `π(z) = ∫ g(θ) θ ψ(zθ) dθ` of `z = x/θ` | `shocksPi`, `ShocksAssumption17_5.mem_Z_of`, `ShocksAssumption17_5.joint`, `ShocksAssumption17_5.integral_pi`, `ShocksAssumption17_5.pi_nonneg` |
| Exercise 17.8(a), p. 534 | The conditional distribution `G(·\|z)`; for `z ∈ int Z` it has a continuous density | `shocksCondDens`, `ShocksAssumption17_5.ex_17_8a_disintegration`, `ShocksAssumption17_5.ex_17_8a`, `ShocksAssumption17_5.pi_pos`; `ex_17_8a_manual_counterexample`, `ex_17_8a_pi_zero_counterexample`, `ex_17_8a_continuity_counterexample` |
| Exercise 17.8(b), p. 534 | `z_n → z` ⇒ `G(·\|z_n) → G(·\|z)` weakly | `shocksCondLaw`, `ShocksAssumption17_5.isProbabilityMeasure_condLaw`, `ShocksAssumption17_5.integral_condLaw`, `ShocksAssumption17_5.ex_17_8b` |
| (3), p. 534 | The first-order condition of (1) with `ρ` eliminated by (2) | Not derived from (1); a solution of (3) is `η = ζ⁻¹ ∘ f` for a fixed point `f` of (4) (as in `proposition_8`) |
| (4), pp. 534–535 | `(Tf)(z) = ∫∫∫ φ[(θ′/θ̃) ζ⁻¹(f(z′))] G(dθ′\|z′) π(dz′) G(dθ̃\|z)` | `shocksOpT`, `shocksPhiF`, `shocksIntegrand`, `shocksClamp`, `shocksRatio`, `shocksRatio_mem`, `shocksIntegrand_eq_olgG`, `shocksJointLaw`, `isProbabilityMeasure_shocksJointLaw` |
| p. 535 | A fixed point corresponds to an equilibrium if its price function is invertible | Not formalised: the islands equilibrium (1)–(2) is not defined in Lean |
| Proposition 6, p. 535 | Assumptions 17.1, 17.2 and 17.5 ⇒ `T` has a unique fixed point in `C(Z)` | `proposition_6`, `proposition_6_islands` (repaired assumptions); `shocksOpT_zero`, `proposition_6_zero_fixedPoint`, `proposition_6_counterexample` |
| Exercise 17.9, p. 535 | Complete the proof of Proposition 6 | `ShocksBounds`, `shocksBounds_exists`, `ShocksBounds.ratio_bounds`, `ShocksBounds.integrand_ge` ((7) of the manual's proof), `ShocksBounds.exists_integrand_le`, `ShocksBounds.opT_mem`, `ShocksBounds.abs_log_integrand_sub_le`, `ShocksBounds.opT_exp_le`, `ShocksBounds.opThat`, `ShocksBounds.ex_17_9`, `ShocksBounds.unique_fixedPoint_ge` |
| pp. 535–536 | Brouwer or Schauder dispense with Assumption 17.2 but give no uniqueness; Assumption 17.5 does not give the analogue of Assumption 17.3 | Not formalised (remark); the second point is Exercise 17.10 |
| Exercise 17.10, p. 536 | `G(·\|z_n)` need not converge to `G(·\|z)` in total variation | `ex_17_10`, with `shocksExSeq`, `shocksExSeq_tendsto`, `shocksEx_condLaw_seq_eq_zero` |
| Assumption 17.6, p. 536 | `Ψ` and `G` uniform | `shocksUnif`, `shocksUnif_assumption17_5`, `shocksUnif_joint`, `shocksUnif_pi` |
| Proposition 7, p. 536 | Assumptions 17.1, 17.5 and 17.6 ⇒ `T` has a fixed point in `C(Z)` | `proposition_7`, `proposition_7_islands`, `shocks_assumption17_1VR_of_V` |
| Exercise 17.11, p. 536 | Steps 1–3 of the proof of Proposition 7 | Steps 1–2: `ShocksBounds.opT_mem`, `ShocksBounds.phiF_mem`, `ShocksBounds.continuous_phiF`; Step 3: `ShocksBounds.ex_17_11_step3` |
| Exercise 17.12, (5), p. 536 | `G(·\|z)` is uniform on `[a(z), b(z)]`, `a(z) = max{x̲/z, θ̲}`, `b(z) = min{x̄/z, θ̄}` | `shocksA`, `shocksB`, `mem_Icc_shocksA_shocksB_iff`, `shocksA_lt_shocksB`; `ex_17_12_counterexample` (with `shocksEx_assumption`, `shocksEx_ab`, `shocksEx_pi`); corrected: `ex_17_12` |
| (6a)–(6b), p. 537 | `Tf(z)` as an average of `φ_f` over `[a(z), b(z)]`; `Tf(z̲) = φ_f(θ̄)`, `Tf(z̄) = φ_f(θ̲)` | `shocksWAvg`, `shocksWAvg_of_lt`, `shocksUnif_integral_condLaw` (with the correct weights) |
| Exercise 17.13, p. 537 | A uniform bound on `\|φ_f′\|` | `ShocksBounds.exists_phi_lipschitz`, `ShocksBounds.ex_17_13` (Lipschitz form), `ShocksBounds.ex_17_13_deriv` (derivative form) |
| (7) and Figure 17.5, pp. 537–538 | `(Tf)′` on `Ẑ`; the three subintervals `I₁`, `I₂`, `I₃` | `shocksWAvg_hasDerivAt`, `shocksA_hasDerivAt`, `shocksB_hasDerivAt`, `eq7_corrected`. Figure 17.5 is not formalised |
| Step 4, pp. 537–539 | `(Tf)′` is bounded uniformly in `f`, so `T(F)` is equicontinuous | `abs_sub_shocksWAvg_le`, `shocksWAvg_lipschitz`, `shocksA_lipschitz`, `shocksB_lipschitz`, `shocksA_shocksB_mem`, `shocksUnif_opT_lipschitz` |
| p. 539 | Finite `Z`: Brouwer, using Steps 1–3 only | `shocks_finite_Z` |
| p. 539 | `T` is monotone under Assumption 17.4 | `shocks_phi_monotoneOn`, `ShocksBounds.opT_monotone` |
| p. 539 | A solution of (3) is an equilibrium only if `ρ(z) = z/η(z)` is strictly increasing; Assumption 17.4 ensures this | `proposition_8` (under Assumption 17.6) |
| Proposition 8, p. 540 | Assumptions 17.1, 17.4 and 17.5 ⇒ `ρ` is strictly increasing; `ξ` and `J` | `proposition_8`; under Assumption 17.5 alone: `proposition_8_general_counterexample` (with `shocksExBimodal`, `shocksExBimodal_assumption`, `shocksExBimodal_integral_inv`) |
| Exercise 17.14(a), p. 540 | `ρ` strictly increasing iff `zη′/η < 1` | `ex_17_14a_deriv`, `ex_17_14a`; `ex_17_14a_counterexample` (with `shocksEtaEx`) |
| Exercise 17.14(b), p. 540 | `zJ′/J < 1` ⇒ `zη′/η < 1` | `ex_17_14b_chain`, `ex_17_14b`; weak form `ex_17_14b_le` |
| Exercise 17.14(c), p. 540 | `0 ≤ yφ′/φ ≤ 1`, hence `−1 ≤ θξ′(θ)/ξ(θ) ≤ 0` | `shocks_V''_nonpos`, `ex_17_14c_phi`, `shocks_phi_elasticity`, `ShocksBounds.integrand_hasDerivAt`, `ShocksBounds.integrandDeriv_bound`, `ShocksBounds.ex_17_14c`; monotone forms `ShocksBounds.integrand_antitone`, `ShocksBounds.integrand_mul_monotoneOn`, `ShocksBounds.phiF_antitoneOn`, `ShocksBounds.phiF_mul_monotoneOn` |
| Exercise 17.14(d), p. 540 | `−1 ≤ θξ′/ξ ≤ 0` ⇒ `zJ′/J ≤ 1` | `shocksWAvg_le_of_le`, `le_shocksWAvg_of_le`, `shocksWAvg_mono`, `shocksWAvg_right_antitone`, `shocksWAvg_left_antitone`, `shocksWAvg_div`, `mul_shocksA`, `mul_shocksB`, `ex_17_14d` (monotone form), `ex_17_14d_deriv` (derivative form) |
| p. 541 | Assumption 17.4 is needed after all; Assumption 17.2 is "a very mild strengthening" of it, so Proposition 7 is of little interest | `monoAssumption17_2_imp_17_4`, `assumption17_4_not_imp_17_2_counterexample`, `MonoAssumption17_2Pos`, `assumption17_2Pos_not_imp_17_4Pos_counterexample` (with `monoArcV`, `monoArcV_repaired_utility`, `monoRRA_monoArcV`), `assumption17_4Pos_not_imp_17_2Pos_counterexample`; corrected: `monoAssumption17_2Pos_of_17_4Pos` |
| p. 541 | With accurate information about `x/θ`, any solution of (3) is an equilibrium | Not formalised (remark) |

## §17.7 Bibliographic notes

| Source | Claim | Lean |
| --- | --- | --- |
| p. 541 | Sources: Labadie (1984), Lucas (1972); proofs of Brouwer (Burger 1963, Border 1985, Milnor 1965) and Schauder (Hutson and Pym 1980, Istratescu 1981, Zeidler 1986); sequence versus recursive equilibria (Cass and Shell 1983, Kehoe and Levine 1985, Muller and Woodford 1988) | Not formalised. Theorem 17.3 is proved by Rogers's (1980) version of Milnor's argument |
