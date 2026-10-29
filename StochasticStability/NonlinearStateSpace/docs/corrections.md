# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Five of the claims below are
refuted in Lean by a counterexample, and for four of them a corrected statement or definition is
proved. For the other entries the table says why no counterexample is given. The last section
lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Definition of a minimal set, p. 155 | A set is minimal if it is closed, invariant, and does not contain any closed invariant set as a proper subset. | Read literally, the definition admits only `∅`: `∅` is closed and invariant, so it is a closed invariant proper subset of every non-empty set (`minimal_literal_eq_empty`). Proposition 7.2.3 already assumes `M` non-empty. `IsMinimal` requires `M` non-empty, closed and invariant, and every non-empty closed invariant subset of `M` to be `M`. |
| p. 156 | If CM(F) is M-irreducible then `M⁰ = ∅`: otherwise `M` and `M⁰` would be disjoint non-empty closed invariant sets. | The argument needs `M⁰` closed, and Proposition 7.2.1 (iii) gives this only for open `M`. The claim fails. For `xₖ₊₁ = xₖ/2` on `ℝ`, with any non-empty control set, `{0}` is minimal and the model is M-irreducible, but no trajectory from `1` reaches `0`, so `1 ∈ M⁰` (`halving_noReach_nonempty`). What is true is that `M` lies in every non-empty closed invariant set (`IsMIrreducible.minimal_subset`); in particular `M ⊆ closure A₊(x)` for every `x`. |
| p. 156 | Indecomposability (no two disjoint closed invariant sets) "is clearly necessary for CM(F) to possess a unique minimal set". | False. For `xₖ₊₁ = 2xₖ` on `ℝ`, with any non-empty control set, `{0}` is the only minimal set, yet `{0}` and `[1, ∞)` are disjoint non-empty closed invariant sets (`indecomposable_not_necessary`). No replacement statement is proved. |
| Proposition 7.1.3, p. 152 | Under (SBL1) and (SBL2) the bilinear model `Xₖ₊₁ = θXₖ + bWₖ₊₁Xₖ + Wₖ₊₁` is a T-chain. The proof: the second order controllability vector `[(θ + bu₂)(bx₀ + 1) \| bx₁ + 1]` is non-zero for almost every `(u₁, u₂)`, so the model is forward accessible. | For `θ = 1` and `b ≠ 0`, `−1/b` is a fixed point of every control (`bilinear_theta_one_fixed`): `F(−1/b, w) = −θ/b`. At `x₀ = −1/b` both entries of the vector vanish for every `(u₁, u₂)`, `A₊(−1/b) = {−1/b}`, and CM(F) is not forward accessible for any control set (`bilinear_theta_one_not_forwardAccessible`). The model is then not a T-chain, for every disturbance law without atoms, in particular under (SBL2): `−1/b` is absorbing and no other point ever reaches it (`proposition_7_1_3_counterexample`). For `b = 0` or `θ ≠ 1` the rank condition holds (`bilinear_rankCondition`) and the model is a T-chain (`proposition_7_1_3`). |
| The adaptive control model, p. 162 | The interior `(σ_z², σ_z²/(1 − α²)) × ℝ²` of the state space is absorbing and is reached in one step with probability one from each initial condition, so the chain may be restricted to the interior. | From `(σ_z²/(1 − α²), θ̃, 0)` the next value of `Σ` is `σ_z²/(1 − α²)` whatever the disturbance (`sac_upper_boundary`), so the chain enters the interior with probability zero in one step (`sacKernel_interior_eq_zero`, for `\|α\| < 1`, `σ_w ≠ 0`). For `α = 0` the interior is empty (`sac_interior_empty_of_alpha_zero`). Proposition 7.4.3 is proved for the chain restricted to the closed state space `sacSpace`, which is absorbing (`isAbsorbing_sacSpace`), with continuous components at every point of it, the boundary included (`sac_exists_component`). |
| Proposition 7.4.3, p. 162 | Under (SAC1), (SAC2) and `σ_z² < 1`, `Φ` is a ψ-irreducible aperiodic T-chain. | `proposition_7_4_3` assumes `\|α\| < 1`, `α ≠ 0`, `σ_z ≠ 0` and `σ_w ≠ 0`, and does not use `σ_z² < 1`. The zero-noise limit `Φₖ → (σ_z²/(1 − α²), 0, 0)` holds from every point of the state space for `\|α\| < 1` and `σ_w ≠ 0` alone (`sac_tendsto`). For `α = 0` or `σ_z = 0` the interval `[σ_z², σ_z²/(1 − α²)]` is a single point, the state space is a plane in `ℝ³`, and the three-dimensional rank condition fails, so the book's argument does not apply; for `α = 0` the entry `∂Σ₂/∂Y₁` of the controllability matrix vanishes (the formula of `sac_dxF_fst`). No counterexample is given for these cases; they are not formalised. |
| Proposition 7.4.2, p. 162 | The gumleaf model (2.12) is a T-chain under (NSS3), "applying Proposition 7.2.6". | The result applied is Proposition 7.1.5: the second order controllability matrix has full rank, and Proposition 7.1.5 turns this into continuous components. The step `F(x, w) = (1/xᵃ − 1/xᵇ + w, xᵃ)` is undefined where `xᵃ = 0` or `xᵇ = 0`; with Lean's `1/0 = 0` it is defined on all of `ℝ²` but not continuous there. `proposition_7_4_2` proves that `gumleafDomain = {xᵃ ≠ 0, xᵇ ≠ 0}` is absorbing, that each of its points has a continuous component of `P²` non-trivial at it, and that the model restricted to it is a T-chain. The book's statement on `ℝ²` is not well posed as written, so there is no counterexample. |
| Proof of Theorem 7.2.6, p. 157 | For `x* ∈ supp ψ` and every open `U ∋ x*`, `K_{a_ε}(x, U) > 0` for all `x`; "by Proposition 7.2.2 it follows that `x*` is globally attracting". | Proposition 7.2.2 gives only that `A₊(y)` meets every neighbourhood of `x*`, that is `x* ∈ closure A₊(y)` for every `y`, not `x* ∈ Ω₊(y)`. This suffices: if `x* ∈ closure A₊(y)` for every `y`, then `closure A₊(x*)` is minimal and CM(F) is M-irreducible (`isMinimal_closure_reach_of_forall_mem_closure`, `isMIrreducible_of_forall_mem_closure`), and then every point of the minimal set is globally attracting (`isGloballyAttracting_of_mem_minimal`). The theorem is true (`theorem_7_2_6`), so there is no counterexample. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| The whole chapter; (NSS1), p. 152 | `F` is smooth (`C^∞`) on `X × O_w`, with `X` an open subset of `ℝⁿ` and `O_w` an open subset of `ℝᵖ`. | `F : X × W → X` is `C¹` where derivatives are used (Mathlib's `ContDiff ℝ 1 F`). `X` and `W` are finite-dimensional real normed spaces, and NSS(F) is defined on all of `X`; the control set is an open subset `O` of `W`, under (NSS3) the set `controlSet γ = {γ > 0}`. Models whose natural state space is a proper subset are restricted to an absorbing set (`proposition_7_4_2`, `proposition_7_4_3`). Propositions 7.2.1, 7.2.3 and 7.2.5, and the lemmas on `OrbitData` behind Theorem 7.3.3, need only a topological state space and the continuity of each `F(·, w)`, `w ∈ O` (and of `F` jointly for the connectedness of Proposition 7.3.4). |
| Proposition 7.1.4, p. 153 | CM(F) is forward accessible if and only if (CM3) holds, a consequence of the implicit function theorem and Sard's theorem. | "If" is proved (`proposition_7_1_4_of_rank`). "Only if" needs Sard's theorem for `Fₖ(x, ·) : Oᵏ → X`, whose source dimension `kp` exceeds `n` for large `k`. Mathlib's Sard theorem covers only a source of equal dimension (Mathlib's `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) or of lower dimension, so `proposition_7_1_4_of_forwardAccessible` assumes its conclusion, `CriticalValuesNull`: for every `x` and `k` the critical values of `Fₖ(x, ·)` on `Oᵏ` are Lebesgue-null. In the scalar case no such hypothesis is needed (`theorem_7_1_1`). `proposition_7_1_5_of_forwardAccessible` carries the same hypothesis. |
| Theorems 7.2.4 (ii), 7.2.6, Proposition 7.3.1, Lemma 7.3.2, Theorem 7.3.3, Proposition 7.3.4, Theorem 7.3.5, pp. 156–160 | CM(F) is forward accessible. | Each takes the rank condition (CM3) (`RankCondition`), which is equivalent to forward accessibility by Proposition 7.1.4: it implies forward accessibility outright, and is implied by it under the Sard hypothesis. Proposition 7.1.5 is stated both ways (`proposition_7_1_5`, `proposition_7_1_5_of_forwardAccessible`), and Proposition 7.1.2, for `X = ℝ`, takes forward accessibility. |
| (CM2), (CM3), pp. 148, 153 | For each `x₀` there are `k ∈ ℤ₊` and `u⁰ ∈ O_wᵏ` with `rank C_{x₀}^k(u⁰) = n`. | `HasFullRankAt` asks for `k ≥ 1`. This loses nothing: on a non-trivial space `C⁰ = 0` is not onto, and on the trivial space every `Cᵏ` is onto. The rank is expressed as surjectivity of the linear map `genCtrb F k x u` (`surjective_iff_finrank_range`; in the scalar case, non-vanishing, `surjective_iff_ne_zero`). |
| Theorem 7.5.1 (i), (7.27), p. 164 | Under (NSS1)–(NSS3), if `E[sup_{Φ₀ ∈ N} ‖∇Φₖ‖] < ∞` on an open convex `N`, then `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]` on `N`. | The book implicitly assumes that `Eₓ[Φₖ]` exists. `theorem_7_5_1_i` assumes that `Φₖ` is integrable from one point of `N`. (7.27) is stated as an integrable `b` with `‖∇Φₖ(y, u)‖ ≤ b(u)` for all `y ∈ N`, for almost every `u`. The density condition (NSS3) is not used: the disturbance law is any probability measure, here and in Theorem 7.5.1 (ii), Propositions 7.5.2–7.5.3 and Duflo's condition. |
| Proposition 7.5.2, p. 164 | If `F` is a rational function and `E[exp(ε₀\|W₁\|)] < ∞`, then `E[sup_{Φ₀ ∈ C} ‖∇Φₖ‖] < ∞` for compact `C`; "the proof is straightforward". | `proposition_7_5_2` takes as hypothesis the polynomial bound `‖∇Φₖ(y, u)‖ ≤ c(1 + Σᵢ‖uᵢ‖)ᵐ` for `y` in an open convex `N`, and concludes that the bound is integrable and that `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]` on `N` (given integrability of `Φₖ` from one point). Deriving the bound from "`F` rational" needs a Łojasiewicz-type inequality for rational maps without real poles, which is not formalised. A rational `F` with real poles is not `C¹` on `X × W`, so `F` is assumed `C¹` throughout; no counterexample is formalised. |
| Duflo's condition, p. 166 | `\|F(x, w) − F(y, w)\| ≤ α(w)\|x − y\|` with `E[α(W)ᵐ] < 1` for some sufficiently large `m`. | `duflo_isEChain` assumes `E[α(W)ᵐ] ≤ 1` for some `m ≥ 1`, which is weaker. By Bernoulli's inequality it gives `E[α(W)] ≤ 1` (`lintegral_le_one_of_lintegral_pow_le_one`), and then `E‖Φₖ(x) − Φₖ(y)‖ ≤ ‖x − y‖` (`enorm_controlMap_sub_le_prod`). |
| Theorem 7.1.1, Proposition 7.1.2, pp. 148–149 | The scalar model has `F : ℝ × ℝ → ℝ`. | The state space is `ℝ`; the noise space `W` is any finite-dimensional real normed space (`theorem_7_1_1`, `proposition_7_1_2`). |
| Proposition 7.2.2, p. 155 | Part (ii) is stated for `k ≥ 1`; part (iii) uses `K_{a_ε}`. | `proposition_7_2_2_ii` holds for every `k ≥ 0`. `proposition_7_2_2_iii` uses the resolvent `K_{a_{1/2}}` (`resolventHalf`, carried). |
| Theorems 7.2.4, 7.2.6, pp. 156–157 | NSS(F) restricted to `M`, or NSS(F) itself, is ψ-irreducible. | The conclusion is ψ-irreducibility for some `ψ ≠ 0` (`IsPhiIrreducible`). Theorem 7.3.5 (ii) and Propositions 7.4.1 and 7.4.3 give a maximal irreducibility measure (`IsMaximalIrreducibility`). |
| Theorem 7.3.5 (i), p. 160 | The periodic orbit of Theorem 7.3.3 is ψ-a.e. equal to the `d`-cycle of Theorem 5.4.4. | `theorem_7_3_5_i` states this for every `ψ` with `ψ(Mᶜ) = 0` that charges every open set meeting `M`, and `exists_measure_minimal` shows that the maximal irreducibility measure of the restriction to `M`, carried to `X`, is one. The cycle is identified up to a relabelling `i ↦ c + i` of its classes. |
| Proposition 7.1.3, (SBL2), p. 151 | `Γ` has a finite second moment and a lower semicontinuous density. | Only the density is used (`proposition_7_1_3`). |
| Proposition 7.4.1, p. 161 | Under (DBL1)–(DBL2), with `\|α\| < 1`, the model is a T-chain. | The T-chain part holds for every `α` (`proposition_7_4_1_tChain`); `\|α\| < 1` is used for ψ-irreducibility and aperiodicity (`proposition_7_4_1`). |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 7.1.1, p. 148 | The proof is omitted; it is "similar to that of Proposition 7.1.2", with details in [271, 272], where the "only if" half rests on Sard's theorem. | No Sard hypothesis is needed for `X = ℝ`. If (CM2) fails at `x`, every controllability vector at `x` vanishes, so the derivative of each `Fₖ(x, ·)` is zero on the open set `Oᵏ`, the map is constant on balls, and its image is countable (`countable_image_of_hasFDerivAt_zero`). Then `A₊(x)` is countable and has empty interior in `ℝ` (`theorem_7_1_1`). |
| Theorem 7.5.1 (ii), p. 164 | (7.27) is assumed near every point; for `f ∈ C_c ∩ C^∞`, `Pᵏf` is differentiated and its derivative bounded, and `C^∞ ∩ C_c` is dense in `C_c`. | (7.27) is not needed, and `Pᵏf` is not differentiated. The mean value theorem in integral form (`enorm_controlMap_sub_le`) and Tonelli give `E‖Φₖ(x) − Φₖ(y)‖ ≤ sup_{z ∈ [x, y]} E_z‖∇Φₖ‖ · ‖x − y‖`. For a continuous compactly supported `f`, which is uniformly continuous, Markov's inequality turns this into equicontinuity of `{Pᵏf}` (`isEChain_of_meanLipschitz`, `theorem_7_5_1_ii`). No smooth approximation is used. |
| Proposition 7.2.2, p. 155 | Assumes that CM(F) is forward accessible. | Not needed: (NSS3) and the continuity of `F` suffice (`proposition_7_2_2_i`, `proposition_7_2_2_ii`, `proposition_7_2_2_iii`). If `A₊ᵏ(x)` meets the open set `U`, the controls `u` with `Fₖ(x, u) ∈ U` form an open set meeting `O_wᵏ`, which has positive `Γ^{⊗k}`-measure (`pi_measure_pos_of_isOpen`); conversely `Γ^{⊗k}` gives full measure to `O_wᵏ` (`pi_measure_compl_controlSet`). Theorem 7.2.4 (i) and the "only if" half of Theorem 7.2.6 then need no accessibility either (`theorem_7_2_4_i`, `theorem_7_2_6_only_if`). |
| Proposition 7.1.2, (7.7)–(7.8), pp. 149–151 | The change of variables (7.7) is an equality through the inverse function `Gₖ`, with the Jacobian `\|∂Gₖ/∂xₖ\|` in `qₖ`; `T₀f` is lower semicontinuous because continuous `rᵢ ↑ qₖγ_w ⋯ γ_w` and dominated convergence make `Tᵢf` continuous. | Only an inequality is needed. The map `(x, u) ↦ Fₖ(x, u)` is straightened near a point of full rank by a local homeomorphism whose Jacobian in `u` is at most `2` (`exists_straightening`), and the Jacobian factor is replaced by the constant `2⁻¹` (`exists_lsc_minorant`). Lower semicontinuity then needs only that of the density, and follows from Fatou's lemma (`lowerSemicontinuous_lintegral_of_lsc`). The construction works in every dimension, which gives Proposition 7.1.5, whose proof the book omits (`exists_continuousComponent`). |
| Theorem 7.2.6, "if", p. 157 | An open petite set containing the globally attracting state `x*`, with Propositions 7.2.2 and 5.5.4. | `x*` is reachable, by Proposition 7.2.2, and Proposition 6.2.1 for the T-chain of Proposition 7.1.5 gives ψ-irreducibility (`theorem_7_2_6`, `proposition_6_2_1`). |
| Theorem 7.3.5 (i), p. 161 | Shrink `E` to a small set, which then plays the role of the small set in the proof of Theorem 5.2.1. | The cycle property of the orbit comes from Proposition 7.2.2 (`isCycle_of_isPeriodicOrbit`). Divisibility `d′ \| d` comes from the small set: two points of the small set in classes `a` and `b` of a `d′`-cycle force the minorizing measure onto the classes `a + k` and `b + k`, so `a = b` (`cycle_class_eq_of_isSmallSet`, `dvd_of_isCycle`). |
| Proposition 7.4.3, p. 163 | Aperiodicity from Proposition 7.3.4, since every element of a cycle for the minimal set contains the limit point. | Aperiodicity is proved directly from the fixed point `x* = (σ_z²/(1 − α²), 0, 0)` of the zero control (`sac_fixed`): from near `x*` the chain is near `x*` at times `1` and `2` with positive probability, which no cycle of period `d ≥ 2` allows. ψ-irreducibility comes from the reachability of `x*` (`sac_pow_pos`) and Proposition 6.2.1. |
| Proposition 7.4.1, p. 161 | Aperiodicity "follows from the fact that any cycle must contain the state `x*`". | `x*` is a fixed point of the control `(z*, w*)`, so it lies in two consecutive classes of the periodic orbit of Theorem 7.3.3 unless the period is `1` (`isPeriodOf_one_of_fixedPoint`); Theorem 7.3.5 (ii) then gives an aperiodic chain (`proposition_7_4_1`). |

## Conventions

* Transition laws are Mathlib's kernels, and `Pᵏ` is the kernel power. NSS(F) is the carried
  `nssKernel Γ F`, the random recursion `recursionKernel Γ F`; the control maps `Fₖ` are the
  carried `controlMap F k`, with controls `u : Fin k → W`. `K_{a_{1/2}}` is `resolventHalf`, and
  the component of `Pᵏ` is a component of `K_{δₖ}`, `diracDist k`. Small sets, absorbing sets,
  restricted kernels, ψ-irreducibility, maximal irreducibility measures, cycles and periods are the
  carried `IsSmallSet`/`IsSmall`, `IsAbsorbing`, `restrictKernel`, `IsPhiIrreducible`,
  `IsMaximalIrreducibility`, `IsCycle`, `IsPeriod` and `IsAperiodic`. Continuous components,
  T-chains, reachability, open set irreducibility and e-chains are the carried
  `IsContinuousComponent`, `IsTChain`, `IsReachable`, `IsOpenSetIrreducible` and `IsEChain`.
* `reachK F O k x` is `A₊ᵏ(x)`, `reach F O x` is `A₊(x)`, `reachKSet` and `reachSet` are their
  unions over a set, `noReach F O E` is `E⁰`, and `omegaSet F O C` is `Ω₊(C)`. `A₊⁰(x) = {x}`, so
  `x ∈ A₊(x)`. Invariance (`IsInvariant`) is `A₊(E) ⊆ E`, equivalently one-step invariance
  (`isInvariant_iff_step`).
* `IsMinimal` requires non-emptiness (see "Claims corrected"). `IsIndecomposable` forbids two
  disjoint non-empty closed invariant sets. `IsMIrreducible` is indecomposability together with a
  minimal set. `IsGloballyAttracting F O x` asks `x ∈ Ω₊({y})` for every `y`.
* `dxF F x w` and `duF F x w` are the partial derivatives `Ξ` and `Λ`, taken from Mathlib's
  `fderiv`. The generalized controllability matrix `C_x^k(u)` is the continuous linear map
  `genCtrb F k x u` on `Wᵏ`, not a matrix, and the sensitivity `∇Φₖ` is the continuous linear map
  `sensitivity F k x u` on `X`. `Eₓ[Φₖ]` is the Bochner integral `∫ z ∂Pᵏ(x)`.
* (SNSS3) and (NSS3) are `IsLSCDensity Γ γ`: `γ` is lower semicontinuous and `Γ = γ · volume`,
  `volume` (Mathlib's) a Haar measure on `W`. The control set is `controlSet γ = {γ > 0}`.
* `IsKAccessible F O k B C` is `B →ᵏ C`. Periodic orbits (`IsPeriodicOrbit`) and the classes
  `orbitClass` of (7.18) are indexed by Mathlib's `ZMod d` instead of `1, …, d`; the book's `Gᵢ`,
  with `kd − i ≡ −i`, is `orbitClass … i`. `IsPeriodOf F O M d` says that `d ≥ 1` is the period of a
  periodic orbit with union `M` and that the period of every such orbit divides `d`; `M` is
  aperiodic when `IsPeriodOf F O M 1`. The return times (7.17) are `returnTimes`, with g.c.d.
  `setGcd` (carried).
* The linear model `F(x, u) = Fx + Gu` is written `A *ᵥ x + B *ᵥ u`, with matrices `A`, `B` for the
  book's `F`, `G`; LCM(F, G) with (LCM2) has control set `univ`. LSS(F, G) is the carried
  `lssMatrixKernel Γ A B`, and (LSS5) is `IsStableMatrix A`. On p. 155 the book first calls `X₀`
  "a unique minimal set" and then says it is the only one under (LSS5); the Lean statements follow
  the second sentence (`lcm_isMinimal_ctrbSubspace`, `lcm_minimal_unique`), and
  `lcm_minimal_not_unique` shows that uniqueness can fail without (LSS5).
* The models are the carried `bilinearStep θ b` and `bilinearKernel Γ θ b`; `dblStep α` and
  `dblKernel Γz Γw α`, on the state `(θ, Y)` with disturbance `(Z, W)`; `gumleafNoisyStep` and
  `gumleafKernel Γ`; and `sacStep α σz σw`, `sacKernel` and `sacGaussianKernel α σz σw`, on the
  state `(Σ, θ̃, Y)` with disturbance `(Z, W)` of law `N(0, σ_z²) ⊗ N(0, σ_w²)` (Mathlib's
  `gaussianReal`). Lean's `1/0 = 0` makes the gumleaf and adaptive control steps total.
* The gumleaf step follows the signs of (2.12), p. 31: `(1/xᵃ − 1/xᵇ + w, xᵃ)`. On p. 162 the book
  writes `−1/xᵃ + 1/xᵇ`, and its `∂F/∂x` has the corresponding signs. The rank of the
  controllability matrix is the same either way (`gumleaf_genCtrb_two`).
* The carried modules are copied from `TopologyContinuity` without change apart from the
  namespace. The corrections they contain belong to Chapters 1–6, are recorded in their module
  docstrings and in those projects, and are not repeated here.

## Not formalised

* **§7.6**, the commentary (pp. 165–167): semi-dynamical systems and topological dynamics, the
  sources of the chapter, the Lie algebra rank characterization of forward accessibility, Stroock
  and Varadhan's support theorem, invariant control sets, the stability of the sensitivity process,
  Lyapunov exponents, and hidden Markov models and filtering. Duflo's condition is formalised
  (`duflo_isEChain`).
* **Sard's theorem** for the control maps `Fₖ(x, ·) : Oᵏ → X`. Its conclusion is the hypothesis
  `CriticalValuesNull` of the "only if" half of Proposition 7.1.4 and of
  `proposition_7_1_5_of_forwardAccessible`.
* **The rational-function step of Proposition 7.5.2**: that a rational `F` without real poles has a
  sensitivity bounded polynomially in the disturbances. The bound is the hypothesis of
  `proposition_7_5_2`.
* **The gumleaf model on all of `ℝ²`.** Proposition 7.4.2 is proved on the absorbing set
  `{xᵃ ≠ 0, xᵇ ≠ 0}`.
* **The adaptive control model with `α = 0` or `σ_z = 0`**, where the state space is a plane in
  `ℝ³` and the book's argument does not apply.
* **The claim that the conditions of Proposition 7.5.2 hold for any i.i.d. Gaussian process**
  (p. 164).
* **Proof devices replaced by other arguments.** The equality form of the change of variables
  (7.7) and the continuous approximation `rᵢ ↑ qₖ` (p. 151); the smooth approximation and the
  derivative bound in Theorem 7.5.1 (ii); the open petite set in Theorem 7.2.6; the small-set
  argument of Theorem 5.2.1 in Theorem 7.3.5; see "Proofs that differ from the book" above.
* **Informal remarks.** The overview of the chapter (pp. 146–147); the dependence of forward
  accessibility on the control set (p. 148); the remark that forward accessibility guarantees only
  the T-chain property (p. 154); the remarks after Proposition 7.5.3 that (LSS5) is the condition
  of Proposition 4.4.3 and that bilinear models can be analysed similarly (p. 165).
