# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 7, pp. 146–168. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.NonlinearStateSpace`; names from Mathlib are marked as such.
Names marked "carried" are in the modules copied from the Chapter 1–6 projects (see the
[README](../README.md)). The state space `X` and the noise space `W` are finite-dimensional real
normed spaces wherever derivatives or densities are used, and `F` is `C¹` where the book takes it
smooth; these and every other place where the Lean statement departs from the book are listed in
[corrections](corrections.md).

## Chapter 7 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 146, (i) | If CM(F) is forward accessible and the noise has a suitable density, NSS(F) is a T-chain | Proposition 7.1.5 below |
| p. 146, (ii) | A globally attracting state for CM(F) is equivalent to NSS(F) being a ψ-irreducible T-chain | Proposition 7.2.5 and Theorem 7.2.6 below |
| p. 146, (iii) | Periodic classes of a forward accessible CM(F) coincide with those of NSS(F) | Theorem 7.3.5 below |
| pp. 146–147 | The adaptive control model is a ψ-irreducible aperiodic T-chain; without forward accessibility, e-chain properties can be established instead | Proposition 7.4.3 and §7.5 below; the overview is not formalised (informal) |

## §7.1.1 Scalar models and forward accessibility

| Source | Claim | Lean |
| --- | --- | --- |
| p. 147 | SNSS(F): `Xₙ = F(Xₙ₋₁, Wₙ)` with `F : ℝ × ℝ → ℝ` smooth; `Fₖ₊₁(x₀, w₁, …, wₖ₊₁) = F(Fₖ(x₀, w₁, …, wₖ), wₖ₊₁)` (2.5) | `nssKernel Γ F` and `controlMap F k x u` (carried), with controls `u : Fin k → W` |
| (7.1), p. 147 | The trajectories `xₖ = Fₖ(x₀, u₁, …, uₖ)` of CM(F), with `uₖ ∈ O_w` | `controlMap` (carried); `controlMap_continuous` (each `Fₖ(·, u)` is continuous if each `F(·, w)`, `w ∈ O`, is) |
| (7.2), p. 147 | `A₊⁰(x) = {x}` and `A₊ᵏ(x) = {Fₖ(x, u₁, …, uₖ) : uᵢ ∈ O_w}` | `reachK`, `reachK_zero`, `self_mem_reachK_zero`, `mem_reachK_succ`, `mem_reachK_succ'`, `step_mem_reachK`, `reachK_nonempty`, `reachK_eq_image` |
| (7.3), p. 148 | `A₊(x) = ⋃ₖ A₊ᵏ(x)` | `reach`, `mem_reach_iff`, `self_mem_reach`, `reachK_subset_reach`, `reach_trans` |
| p. 148 | CM(F) is forward accessible if `A₊(x₀)` has non-empty interior for every `x₀` | `IsForwardAccessible` |
| p. 148 | Forward accessibility depends critically on `O_w`, unlike controllability of the linear model | Not formalised (remark) |
| (CM2), (7.4), p. 148 | For each `x₀` there are `k` and `u⁰ ∈ O_wᵏ` with `[∂Fₖ/∂u₁ \| ⋯ \| ∂Fₖ/∂uₖ]` non-zero at `(x₀, u⁰)` | `RankCondition`, `HasFullRankAt` (`k ≥ 1`, `u ∈ Oᵏ`, `C_x^k(u)` onto); `surjective_iff_ne_zero` (a linear map to `ℝ` is onto iff it is non-zero) |
| p. 148 | In the scalar linear case the derivative is `[F^{k−1}G \| ⋯ \| FG \| G]`, the matrix of (LCM3) | `genCtrb_linear` (in every dimension) |
| Theorem 7.1.1, p. 148 | CM(F) is forward accessible iff (CM2) holds; the proof is omitted, with references to [271, 272] | `theorem_7_1_1` (`X = ℝ`; `F` `C¹`; `O` open; `W` any finite-dimensional space). The "only if" half needs no Sard theorem: if every controllability vector vanishes, `A₊(x)` is countable (`countable_image_of_hasFDerivAt_zero`) |

## §7.1.2 Continuous components for the scalar nonlinear model

| Source | Claim | Lean |
| --- | --- | --- |
| (SNSS3), p. 149 | `Γ` is absolutely continuous with a lower semicontinuous density `γ_w`; the control set is `O_w = {γ_w > 0}` | `IsLSCDensity Γ γ` (`γ` lower semicontinuous and `Γ = γ · volume`), `controlSet γ`, `isOpen_controlSet` |
| p. 149 | With probability one `Wₖ ∈ O_w` for all `k` | `measure_compl_controlSet`, `pi_measure_compl_controlSet` |
| p. 149 | Laws with a continuous density, such as the Gaussian, and uniform laws on bounded open intervals satisfy (SNSS3) | `isLSCDensity_uniform` (with control set the interval); `isLSCDensity_gaussianReal` (a non-degenerate centred Gaussian, Mathlib's `gaussianReal` with density Mathlib's `gaussianPDF`) |
| Proposition 7.1.2, p. 149 | Under (SNSS3), a forward accessible SNSS(F) model is a T-chain | `proposition_7_1_2` (`F` `C¹`; `W` any finite-dimensional space), from `theorem_7_1_1` and `proposition_7_1_5` |
| (7.5), p. 149 | Proof: assume `∂Fₖ/∂wₖ ≠ 0` at `(x⁰₀, w⁰)` with `w⁰ ∈ O_wᵏ` | In general: `∂Fₖ/∂u (x₀, u⁰)` onto (`HasFullRankAt`) |
| pp. 149–150 | `F^k(x₀, w) = (x₀, w₁, …, wₖ₋₁, xₖ)` has full-rank derivative; the inverse function theorem gives a smooth inverse `G^k` | `exists_straightening`: `Ψ(x, u) = (x, R G(x, u) + u − R L u)`, with `L = ∂G/∂u (x₀, u₀)` and `R` a right inverse of `L`, is a local homeomorphism with `G = L ∘ Ψ₂`, and the Jacobian of `u ↦ Ψ₂(x, u)` is at most `2`. This works in every dimension |
| (7.6), p. 150 | `Pᵏf(x₀) = ∫ f(Fₖ(x₀, w)) γ_w(w₁) ⋯ γ_w(wₖ) dw` | `nssKernel_pow_apply_density`; `prodDensity`, `lowerSemicontinuous_prodDensity`, `prodDensity_pos`, `pi_eq_withDensity_prodDensity`, `pi_withDensity_eq`, `lintegral_pi_prod` |
| (7.7), p. 150 | The change of variables `wₖ = Gₖ(x₀, w₁, …, wₖ₋₁, xₖ)`, with `qₖ = I{Gᵏ ∈ B} γ_w(Gₖ) \|∂Gₖ/∂xₖ\|` lower semicontinuous | Replaced by an inequality: `exists_lsc_minorant` gives a jointly lower semicontinuous `K` with `∫ 1_A(Ly) K(x, y) dy ≤ ∫_V 1_A(G(x, u)) ρ(u) du`; the Jacobian factor is replaced by the constant `2⁻¹`. `lowerSemicontinuous_mul_ennreal`, `lowerSemicontinuous_finset_prod`, `indicator_preimage_eq_mul` |
| (7.8), pp. 150–151 | The kernel `T₀` is non-trivial at `x⁰₀` | `exists_continuousComponent` (`T(x₀, X) > 0`; for `k ≥ 1` also an open small neighbourhood of `x₀`) |
| p. 151 | `T₀f` is lower semicontinuous: continuous `rᵢ ↑ qₖ γ_w ⋯ γ_w` and dominated convergence | Replaced by Fatou's lemma: `lowerSemicontinuous_lintegral_of_lsc` |
| p. 151 | `T₀` is a continuous component of `Pᵏ`, so "from Theorem 6.2.4" the model is a T-chain | The component is for `K_{δₖ} = Pᵏ` (`diracDist k`, carried); `proposition_7_1_5` then applies `proposition_6_2_4` (carried). The book's reference is to Proposition 6.2.4 |

## §7.1.3 Simple bilinear model

| Source | Claim | Lean |
| --- | --- | --- |
| (SBL1), p. 151 | `Xₖ₊₁ = θXₖ + bWₖ₊₁Xₖ + Wₖ₊₁`, an SNSS(F) model with `F` as in (2.7) | `bilinearStep θ b`, `bilinearKernel Γ θ b` (carried); `contDiff_one_bilinearStep` |
| (SBL2), p. 151 | `Γ` has a finite second moment and a lower semicontinuous density | `IsLSCDensity Γ γ`; the second moment is not used |
| pp. 151–152 | `P(−1/b, {−θ/b}) = 1` and `P(x, {−θ/b}) = 0` for `x ≠ −1/b`, so every continuous component `T` of `P` has `T(−1/b, ℝ) = 0` | `bilinear_component_trivial` (`b ≠ 0`; `Γ` without atoms), from `continuousComponent_trivial_of_dirac` and `setOf_affine_mem_singleton`; a law with a density has no atoms (`IsLSCDensity.nullSingletonClass`) |
| p. 152 | The first order controllability vector `∂F/∂u (x₀, u₁) = bx₀ + 1` vanishes at `x₀ = −1/b` | `bilinear_duF`; `bilinear_dxF` (`∂F/∂x = θ + bw`) |
| p. 152 | The second order vector `[(θ + bu₂)(bx₀ + 1) \| bx₁ + 1]` is non-zero for almost every `(u₁, u₂)`, so CM(F) is forward accessible | `bilinear_genCtrb_two`; `bilinear_rankCondition` (for `b = 0` or `θ ≠ 1`). False for `θ = 1`, `b ≠ 0` at `x₀ = −1/b`, a fixed point of every control: `bilinear_theta_one_fixed`, `bilinear_theta_one_not_forwardAccessible` |
| Proposition 7.1.3, p. 152 | Under (SBL1)–(SBL2) the bilinear model is a T-chain | False for `θ = 1`, `b ≠ 0`: `proposition_7_1_3_counterexample` (for every law without atoms). Corrected: `proposition_7_1_3` (`b = 0` or `θ ≠ 1`) |

## §7.1.4 Multidimensional models

| Source | Claim | Lean |
| --- | --- | --- |
| (NSS1), (7.9), p. 152 | NSS(F) and the trajectories of CM(F) | `nssKernel Γ F`, `controlMap` (carried) |
| (7.10), p. 152 | `A₊(x)`; CM(F) is forward accessible if `A₊(x)` has non-empty interior for every `x` | `reach`, `IsForwardAccessible` |
| p. 152 | `Ξₖ₊₁ = ∂F/∂x` and `Λₖ₊₁ = ∂F/∂u` at `(xₖ, uₖ₊₁)` | `dxF`, `duF`, `fderiv_apply_eq_dxF_add_duF`, `dxF_eq_of_hasFDerivAt`, `duF_eq_of_hasFDerivAt` |
| (7.11), p. 153 | `C_{x₀}^k = [Ξₖ ⋯ Ξ₂Λ₁ \| Ξₖ ⋯ Ξ₃Λ₂ \| ⋯ \| ΞₖΛₖ₋₁ \| Λₖ]` | `genCtrb`, the linear map `(v₁, …, vₖ) ↦ Σᵢ Ξₖ ⋯ Ξᵢ₊₁Λᵢvᵢ`; `genCtrb_succ_apply`, `genCtrb_one_apply`, `initCLM`, `initCLM_apply` |
| (7.12), p. 153 | For `F(x, u) = Fx + Gu`, `C_{x₀}^k = [F^{k−1}G \| ⋯ \| G]` | `genCtrb_linear` (`ctrbMap`, carried), `dxF_duF_linear` |
| (CM3), (7.13), p. 153 | For each `x₀` there are `k ∈ ℤ₊` and `u⁰ ∈ O_wᵏ` with `rank C_{x₀}^k(u⁰) = n` | `RankCondition`, `HasFullRankAt` (`k ≥ 1`); `surjective_iff_finrank_range` (onto iff rank `n`). For the linear model (CM3) is controllability (LCM3): `linear_rankCondition_iff` (`IsControllable`, carried) |
| p. 153 | `C_y^k` is the derivative of `xₖ` with respect to the inputs | `hasFDerivAt_controlMap`, `contDiff_controlMap`, `fderiv_controlMap_comp_inr`; at a single point, `hasFDerivAt_controlMap_succ_of` |
| Proposition 7.1.4, p. 153 | CM(F) is forward accessible iff (CM3) holds, by the implicit function theorem and Sard's theorem; the proof is omitted | "If": `proposition_7_1_4_of_rank` (`F` `C¹`, `O` open), via `image_mem_nhds_of_hasFullRankAt`. "Only if": `proposition_7_1_4_of_forwardAccessible`, under `CriticalValuesNull` (the critical values of each `Fₖ(x, ·)` on `Oᵏ` are Lebesgue-null), the conclusion of Sard's theorem taken as a hypothesis |
| (NSS3), p. 153 | `Γ` has a lower semicontinuous density `γ_w` on `ℝᵖ`, and `O_w = {γ_w > 0}` | `IsLSCDensity`, `controlSet`; `controlSet_nonempty` |
| Proposition 7.1.5, p. 154 | Under (NSS3), if CM(F) is forward accessible, `X` is a union of open small sets and NSS(F) is a T-chain; the proof is "similar to, but more complicated than" that of Proposition 7.1.2 | `proposition_7_1_5` (under (CM3), `F` `C¹`), via `exists_continuousComponent_of_hasFullRankAt`; from forward accessibility under `CriticalValuesNull`: `proposition_7_1_5_of_forwardAccessible`. `IsSmall`, `IsTChain` (carried) |
| p. 154 | This guarantees only the T-chain property | Not formalised (remark) |

## §7.2.1 Minimality for the deterministic control model

| Source | Claim | Lean |
| --- | --- | --- |
| p. 154 | `A₊(E) = ⋃_{x ∈ E} A₊(x)` and `E⁰ = {x : A₊(x) ∩ E = ∅}` | `reachSet`, `reachKSet`, `noReach`; `reachSet_singleton`, `reachKSet_singleton`, `subset_reachSet` |
| p. 154 | The semigroup property `A₊^{k+j}(E) = A₊ᵏ(A₊ʲ(E))` | `reachK_add`, `reachKSet_add`, `reachK_trans`, `reachSet_reachKSet` |
| p. 154 | `E` is invariant if `A₊(E) ⊆ E` | `IsInvariant`, `isInvariant_iff_step` (one-step invariance), `IsInvariant.reachK_subset`, `IsInvariant.reach_subset`, `reachSet_subset_of_isInvariant`, `isInvariant_empty`, `isInvariant_univ` |
| p. 154 | `A₊(C)` and `C⁰` are invariant; closures, unions and intersections of invariant sets are invariant | `isInvariant_reachSet`, `isInvariant_reach`, `isInvariant_iUnion`, `isInvariant_iInter`, `IsInvariant.inter`, `IsInvariant.closure` (each `F(·, w)`, `w ∈ O`, continuous) |
| (7.14), p. 154 | `Ω₊(C) = ⋂_{N ≥ 1} closure ⋃_{k ≥ N} A₊ᵏ(C)` is invariant | `omegaSet`, `isClosed_omegaSet` |
| Proposition 7.2.1, p. 155 | (i) `A₊(C)` and its closure are invariant; (ii) `Ω₊(C)` is invariant; (iii) `C⁰` is invariant, and closed if `C` is open | `proposition_7_2_1_i`, `proposition_7_2_1_ii`, `proposition_7_2_1_iii` (each `F(·, w)`, `w ∈ O`, continuous); `isOpen_setOf_reachK_inter`, `isOpen_setOf_reach_inter` |
| Proposition 7.2.2, p. 155 | If CM(F) is forward accessible: (i) a closed `A` is absorbing iff it is invariant; (ii) for open `U`, `k ≥ 1` and every `x`, `A₊ᵏ(x) ∩ U ≠ ∅` iff `Pᵏ(x, U) > 0`; (iii) `A₊(x) ∩ U ≠ ∅` iff `K_{a_ε}(x, U) > 0` | `proposition_7_2_2_i` (`IsAbsorbing`, carried), `proposition_7_2_2_ii` (every `k ≥ 0`), `proposition_7_2_2_iii` (with `K_{a_{1/2}}`, `resolventHalf`, carried); under (NSS3) for continuous `F`, without forward accessibility. `continuous_controlMap_right`, `measure_pos_of_isOpen_inter`, `pi_measure_pos_of_isOpen` |
| p. 155 | A set is minimal if it is closed, invariant, and contains no closed invariant set as a proper subset | Read literally only `∅` qualifies: `minimal_literal_eq_empty`. `IsMinimal`: non-empty, closed and invariant, and every non-empty closed invariant subset is the whole set |
| p. 155 | For LCM(F, G) with `O_w = ℝᵖ`, the range `X₀` of the controllability matrix is the minimal set; under (LSS5) it is the only one | `lcm_isMinimal_ctrbSubspace` (`X₀` is minimal), `lcm_minimal_unique` (the only minimal set under (LSS5), `IsStableMatrix`, carried). Without (LSS5) the minimal set need not be unique: `lcm_minimal_not_unique` (`xₖ₊₁ = xₖ`, every point is minimal) |
| Proposition 7.2.3, p. 155 | For non-empty `M`, equivalent: (i) `M` is minimal; (ii) `closure A₊(x) = M` for all `x ∈ M`; (iii) `Ω₊(x) = M` for all `x ∈ M` | `proposition_7_2_3` (each `F(·, w)` continuous, `O` non-empty); `IsInvariant.closure_reach_subset`, `isInvariant_closure_reach`, `omegaSet_subset_closure_reach`, `tail_closure_props`, `tail_closure_subset` |

## §7.2.2 M-irreducibility and ψ-irreducibility

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 7.2.4, p. 156 | If CM(F) is forward accessible and (NSS3) holds, a minimal `M` is (i) absorbing, and (ii) NSS(F) restricted to `M` is an open set irreducible, and so ψ-irreducible, T-chain | `theorem_7_2_4_i` (`F` continuous; no accessibility), `theorem_7_2_4_ii` (rank condition (CM3), `F` `C¹`; `ψ ≠ 0`); `restrictKernel`, `isMarkovKernel_restrictKernel`, `IsOpenSetIrreducible`, `IsPhiIrreducible` (carried) |
| p. 156 | Proof: Propositions 7.2.3, 7.2.1 and 7.2.2, then Propositions 6.2.2 and 7.1.5 | In the proof of `theorem_7_2_4_ii`, with `proposition_6_2_2` (carried) and `isTChain_restrictKernel` (the restriction of a T-chain to an absorbing set is a T-chain) |
| p. 156 | If `X` itself is minimal, NSS(F) is ψ-irreducible and open set irreducible | `isOpenSetIrreducible_of_isMinimal_univ` |
| p. 156 | CM(F) is indecomposable if `X` contains no two disjoint closed invariant sets | `IsIndecomposable` (no two disjoint non-empty closed invariant sets) |
| p. 156 | Indecomposability is clearly necessary for a unique minimal set | False: `indecomposable_not_necessary` (`xₖ₊₁ = 2xₖ`; `controlMap_double`) |
| p. 156 | For `X = ℝ`, `O_w = (0, 1)` and `xₖ₊₁ = xₖ + uₖ₊₁` the system is indecomposable but has no minimal set | `translation_indecomposable_no_minimal`, `controlMap_translate_const` |
| p. 156 | CM(F) is M-irreducible if it is indecomposable and has a minimal set `M` | `IsMIrreducible` |
| p. 156 | If CM(F) is M-irreducible then `M⁰ = ∅` | False: `halving_noReach_nonempty` (`xₖ₊₁ = xₖ/2`, `M = {0}`, `1 ∈ M⁰`; `controlMap_halve`). What holds: `IsMIrreducible.minimal_subset` (`M` lies in every non-empty closed invariant set) |
| p. 157 | `x*` is globally attracting if `x* ∈ Ω₊(y)` for all `y` | `IsGloballyAttracting` |
| Proposition 7.2.5, p. 157 | (i) CM(F) is M-irreducible iff a globally attracting state exists; (ii) if `x*` is globally attracting, the unique minimal set is `closure A₊(x*) = Ω₊(x*)` | `proposition_7_2_5_i`, `proposition_7_2_5_ii` (each `F(·, w)` continuous, `O` non-empty); `isMinimal_closure_reach_of_forall_mem_closure`. Every point of the minimal set is globally attracting: `isGloballyAttracting_of_mem_minimal` |
| Theorem 7.2.6, p. 157 | If CM(F) is forward accessible and (NSS3) holds, NSS(F) is ψ-irreducible iff CM(F) is M-irreducible | `theorem_7_2_6` (rank condition (CM3), `F` `C¹`, `ψ ≠ 0`). The "only if" half for every continuous `F`: `theorem_7_2_6_only_if` |
| p. 157 | Proof, "only if": for `x* ∈ supp ψ` and open `U ∋ x*`, `K_{a_ε}(x, U) > 0` for all `x`, so `x*` is globally attracting by Proposition 7.2.2 | This gives only `x* ∈ closure A₊(y)` for every `y`, which suffices: `isMIrreducible_of_forall_mem_closure`. A point of `supp ψ`: `exists_forall_isOpen_measure_pos` |
| p. 157 | Proof, "if": an open petite set containing `x*`, Propositions 7.2.2 and 5.5.4 | Replaced: `x*` is reachable, and Proposition 6.2.1 (`proposition_6_2_1`, carried) applies to the T-chain of Proposition 7.1.5. The reachability of a globally attracting state is also stated separately: `isReachable_of_isGloballyAttracting` (`IsReachable`, carried) |

## §7.3.1 Periodicity for control models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 157 | `C` is `k`-accessible from `B`, `B →ᵏ C`, if `C ⊆ A₊ᵏ(y)` for every `y ∈ B` | `IsKAccessible`, `IsKAccessible.mono` |
| Proposition 7.3.1, p. 158 | If CM(F) is forward accessible, each `x` lies in an open `Bₓ` with `Bₓ →^{kₓ} Cₓ` for an open `Cₓ` | `proposition_7_3_1` (rank condition, `F` `C¹`, `O` open; `Cₓ` non-empty and `kₓ ≥ 1`), from `exists_uniform_reach`; `isOpen_controls` |
| Lemma 7.3.2, p. 158 | A minimal `M` contains an open `E` with `E →ⁿ E` for some `n` | `lemma_7_3_2` (`E` non-empty, `n ≥ 1`) |
| (7.15)–(7.16), p. 158 | `C ⊆ A₊(B ∩ M) ⊆ M` and `A₊(x) ∩ B ≠ ∅` for `x ∈ M` | In the proof of `lemma_7_3_2` |
| p. 158 | A periodic orbit of period `d`: disjoint closed sets `G₁, …, G_d` with `A₊¹(Gᵢ) ⊆ Gᵢ₊₁` (mod `d`) | `IsPeriodicOrbit` (indexed by Mathlib's `ZMod d`), `IsPeriodicOrbit.reachK_subset`, `IsPeriodicOrbit.nonempty` |
| Theorem 7.3.3, p. 158 | For smooth `F` and forward accessible CM(F), a minimal `M` is the union of a periodic orbit `G` of period `d ≥ 1`; a periodic orbit `H` with union `M` has period dividing `d`, and each `Hᵢ` is a union of sets `Gⱼ` | `theorem_7_3_3` (rank condition, `F` `C¹`, `O` open). From a set `E` as in Lemma 7.3.2: `OrbitData`, `exists_orbitData`, `theorem_7_3_3_of_orbitData` (`Gⱼ ⊆ H_{a+j}`), `theorem_7_3_3_union` |
| (7.17), p. 159 | `I = {n ≥ 1 : E →ⁿ E}` is closed under addition | `returnTimes`, `returnTimes_isAddClosed` (`IsAddClosed`, carried), `mem_returnTimes_chain` |
| p. 159 | `d = g.c.d.(I)` is the period of `M`; `M` is aperiodic when `d = 1` | `IsPeriodOf` (`d` is the period of a periodic orbit with union `M`, and the period of every such orbit divides `d`), `IsPeriodOf.unique`, `exists_isPeriodOf`; `setGcd` (carried), `OrbitData.d_pos`, `OrbitData.dvd` |
| (7.18), p. 159 | `Gᵢ = {x ∈ M : ⋃_{k ≥ 1} A₊^{kd−i}(x) ∩ E ≠ ∅}`, and `M = ⋃ Gᵢ` by Proposition 7.2.1 | `orbitClass` (`A₊ⁿ(x)` meets `E` for some `n` with `n + i ≡ 0` mod `d`), `OrbitData.iUnion_eq`, `OrbitData.subset_zero`, `OrbitData.closure_reach`, `OrbitData.exists_meets` |
| (7.19)–(7.20), p. 159 | The `Gᵢ` are relatively open in `M` and disjoint, hence closed | `OrbitData.disjoint`, `OrbitData.isClosed`, `OrbitData.meetSet`, `OrbitData.isOpen_meetSet`, `OrbitData.orbitClass_eq`, `OrbitData.isOpen_meets` |
| p. 159 | `G` is a periodic orbit, unique by (7.18) | `OrbitData.step`, `OrbitData.isPeriodicOrbit`, `OrbitData.unique` |
| Proposition 7.3.4, p. 160 | If `O_w` is connected, the sets of the periodic orbit of Theorem 7.3.3 are the connected components of `M`; `M` is aperiodic iff it is connected | `proposition_7_3_4` (`O` preconnected); `OrbitData.isConnected_class`, `OrbitData.connectedComponentIn_eq` (Mathlib's `connectedComponentIn`), `OrbitData.isConnected_of_isPeriodOf_one`. A connected minimal set is aperiodic without connectedness of the control set: `isPeriodOf_one_of_isConnected` |
| (7.21)–(7.22), p. 160 | Proof: `A₊ᵏ(v)` is connected as the continuous image of `v × O_wᵏ`; `G_d` is the closure of `⋃_{k ≥ N₀} A₊^{kd}(v)` and `G₁` the closure of `A₊¹(G_d)` | As in the book, `Gⱼ` is the closure of `A₊ʲ(⋃_{q ≥ N₀} A₊^{qd}(v))` (in the proof of `OrbitData.isConnected_class`); `continuous_controlMap_joint`, `reachKSet_eq_image`, `isPreconnected_controls`, `subset_of_isPreconnected_of_closed_partition` |

## §7.3.2 Periodicity

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 7.3.5 (i), p. 160 | Under (NSS1)–(NSS3) and forward accessibility, for a minimal `M`, NSS(F) restricted to `M` is a ψ-irreducible T-chain, and the periodic orbit of Theorem 7.3.3 is ψ-a.e. equal to the `d`-cycle of Theorem 5.4.4 | The restriction: `theorem_7_2_4_ii`. The orbit: `theorem_7_3_5_i` (rank condition, `F` `C¹`): for every `ψ` carried by `M` that charges every open set meeting `M`, the orbit is a `d`-cycle (`IsCycle`, carried), `d` is the period (`IsPeriod`, carried), and every `d`-cycle agrees with the orbit up to `ψ`-null sets after a relabelling. `exists_measure_minimal`: the maximal irreducibility measure of the restriction to `M`, carried to `X`, is such a `ψ` |
| p. 161 | Proof: shrink `E` to a small set, which plays the role of the small set in the proof of Theorem 5.2.1 | `OrbitData.shrink` and the open small sets of Proposition 7.1.5. The cycle property comes from Proposition 7.2.2 (`isCycle_of_isPeriodicOrbit`, `nssKernel_apply_eq_one`), divisibility of the periods from the small set (`dvd_of_isCycle`, `cycle_class_eq_of_isSmallSet`; `IsSmallSet`, carried), and uniqueness up to null sets from `orbitClass_ae_eq_of_isCycle` |
| Theorem 7.3.5 (ii), p. 160 | If CM(F) is M-irreducible with an aperiodic minimal set, NSS(F) is a ψ-irreducible aperiodic T-chain | `theorem_7_3_5_ii` (rank condition, `F` `C¹`; `ψ` maximal, `IsMaximalIrreducibility`, `IsAperiodic`, carried); `isGloballyAttracting_of_mem_minimal`, `isReachable_of_isGloballyAttracting` |

## §7.4.1 The dependent parameter bilinear model

| Source | Claim | Lean |
| --- | --- | --- |
| (7.23), p. 161 | `F((θ, Y), (Z, W)) = (αθ + Z, θY + W)` | `dblStep α`, `dblKernel Γz Γw α` (carried); `contDiff_one_dblStep` |
| (DBL2), p. 32 | `Z` and `W` are independent with lower semicontinuous densities | `isLSCDensity_prod` (the product law satisfies (NSS3)), `controlSet_prod` (`O = O_z × O_w`) |
| p. 161 | The first order controllability matrix is the identity, so CM(F) is forward accessible | `dbl_duF`, `dbl_rankCondition` |
| Proposition 7.4.1, p. 161 | Under (DBL1)–(DBL2) the model is a T-chain; if some `z* ∈ O_z` has `\|z*/(1 − α)\| < 1` (7.24), it is ψ-irreducible and aperiodic | `proposition_7_4_1_tChain` (for every `α`), `proposition_7_4_1` (`\|α\| < 1`; `ψ` maximal) |
| p. 161 | With `Zₖ = z*`, `Wₖ = w*`, `(θₖ, Yₖ) → x* = (z*(1 − α)⁻¹, w*(1 − α)(1 − α − z*)⁻¹)`, which is globally attracting; aperiodicity because any cycle must contain `x*` | `dbl_tendsto` (`x* = (z*/(1 − α), w*/(1 − θ*))`, `θ* = z*/(1 − α)`), `tendsto_zero_of_affine_recursion`; aperiodicity from `x*` being a fixed point of the control `(z*, w*)`: `isPeriodOf_one_of_fixedPoint` and `theorem_7_3_5_ii` |

## §7.4.2 The gumleaf attractor

| Source | Claim | Lean |
| --- | --- | --- |
| (2.12), (7.25), p. 162 | `Xₙ = (−1/Xᵃₙ₋₁ + 1/Xᵇₙ₋₁, Xᵃₙ₋₁) + (Wₙ, 0)` | `gumleafNoisyStep`, `gumleafKernel` (carried), with the signs of (2.12) on p. 31: `(1/xᵃ − 1/xᵇ + w, xᵃ)`. `gumleafDomain = {xᵃ ≠ 0, xᵇ ≠ 0}`, `isOpen_gumleafDomain`, `gumleaf_contDiffAt` |
| p. 162 | `∂F/∂x` and `∂F/∂u = (1, 0)` | `gumleaf_dxF_fst` (the first column), `gumleaf_duF` |
| p. 162 | `C_{x₀}^2(u₁, u₂)` has full rank for all `x₀`, `u₁`, `u₂`, so CM(F) is forward accessible | `gumleaf_genCtrb_two` (full rank wherever the step is smooth at `x₀` and at `x₁`); `exists_mem_ne_of_isOpen` |
| Proposition 7.4.2, p. 162 | Under (NSS3) the model is a T-chain, "applying Proposition 7.2.6" | `proposition_7_4_2`: the domain is absorbing, each of its points has a continuous component of `P²` non-trivial at it (`exists_continuousComponent`), and the model restricted to the domain is a T-chain (`isTChain_restrictKernel_of_local`, `continuousComponent_restrict`). The book's reference should be to Proposition 7.1.5 |

## §7.4.3 The adaptive control model

| Source | Claim | Lean |
| --- | --- | --- |
| (2.22)–(2.24), (SAC1)–(SAC2), p. 162 | The closed loop adaptive control model on `Φₖ = (Σₖ, θ̃ₖ, Yₖ)`, with Gaussian disturbances `(Z, W)` | `sacStep α σz σw`, `sacKernel`, `sacGaussianKernel` (carried; Mathlib's `gaussianReal`) |
| p. 162 | The state space `[σ_z², σ_z²/(1 − α²)] × ℝ²` is not open | `sacSpace`, `isClosed_sacSpace`, `sac_isInvariant`, `isAbsorbing_sacSpace`, `sac_den_pos` |
| p. 162 | The interior `(σ_z², σ_z²/(1 − α²)) × ℝ²` is absorbing and is reached in one step with probability one from each initial condition, so `Φ` may be restricted to it | Not reached in one step: `sac_upper_boundary`, `sacKernel_interior_eq_zero`. Empty for `α = 0`: `sac_interior_empty_of_alpha_zero`. The chain is restricted to `sacSpace` instead |
| Proposition 7.4.3, p. 162 | Under (SAC1)–(SAC2) and `σ_z² < 1`, `Φ` is a ψ-irreducible aperiodic T-chain | `proposition_7_4_3`: restricted to `sacSpace`, for `\|α\| < 1`, `α ≠ 0`, `σ_z ≠ 0` and `σ_w ≠ 0`; `σ_z² < 1` is not used; `ψ` maximal |
| p. 163 | The second order controllability matrix has full rank whenever `Y₁ = θ̃₀Y₀ + W₁ ≠ 0`, so CM(F) is forward accessible and `Φ` is a T-chain by Proposition 7.1.5 | `sac_genCtrb_surjective` (`α ≠ 0`, `σ_w ≠ 0`, `Σ₁ ≠ 0`), `sac_duF`, `sac_dxF_fst`, `sac_contDiffAt`, `sac_isLSCDensity`; continuous components at every point of `sacSpace`, boundary included: `sac_exists_component`, `continuousAt_controlMap_succ_of` |
| p. 163 | With zero disturbances, since `α < 1` and `σ_z² < 1`, `Φₖ → (σ_z²/(1 − α²), 0, 0)` | `sac_tendsto` (`\|α\| < 1`, `σ_w ≠ 0`, from every state with `Σ₀ ∈ [σ_z², σ_z²/(1 − α²)]`; `σ_z² < 1` is not needed), `sac_fixed`, `sac_controlMap_fixed` |
| p. 163 | Hence CM(F) is M-irreducible and `Φ` is ψ-irreducible "by Proposition 7.2.6"; every cycle class contains the limit, so `Φ` is aperiodic by Proposition 7.3.4 | ψ-irreducibility: the limit `x*` is reachable (`sac_pow_pos`, `sac_continuousAt_zero`, `sac_continuousAt_joint`) and `proposition_6_2_1` (carried) applies. Aperiodicity directly from the fixed point `x*`: from near `x*` the chain is near `x*` at times `1` and `2` with positive probability, which no cycle of period `d ≥ 2` allows |

## §7.5.1 e-Chain properties of nonlinear state space models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 163 | NSS(F) is always Feller, by Proposition 6.1.2 | `proposition_6_1_2` (carried) |
| (7.26), p. 163 | The sensitivity process `∇Φ₀ = I`, `∇Φₖ₊₁ = DF(Φₖ, wₖ₊₁)∇Φₖ` | `sensitivity`, `continuous_sensitivity` |
| p. 163 | `∇Φₖ = dΦₖ/dΦ₀` by the chain rule | `hasFDerivAt_controlMap_left` |
| Theorem 7.5.1 (i), (7.27), p. 164 | Under (NSS1)–(NSS3), if `E[sup_{Φ₀ ∈ N} ‖∇Φₖ‖] < ∞` on an open convex `N`, then `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]` on `N`; "a consequence of the Dominated Convergence Theorem" | `theorem_7_5_1_i` (any disturbance law; (7.27) as an integrable `b` with `‖∇Φₖ‖ ≤ b` on `N` almost surely; `Φₖ` integrable from one point of `N`); `integral_nssKernel_pow` |
| Theorem 7.5.1 (ii), p. 164 | If (7.27) holds near every point and `sup_{y ∈ C} sup_k E_y[‖∇Φₖ‖] < ∞` for every compact `C`, `Φ` is an e-chain | `theorem_7_5_1_ii` (any disturbance law; (7.27) is not needed); `IsEChain` (carried) |
| p. 164 | Proof: for `f ∈ C_c ∩ C^∞`, `\|d/dx Pᵏf(x)\| ≤ ‖f′‖∞ Eₓ[‖∇Φₖ‖]`, and `C^∞ ∩ C_c` is dense in `C_c` | Replaced: `enorm_controlMap_sub_le` (the mean value theorem in integral form) and Tonelli give `E‖Φₖ(x) − Φₖ(y)‖ ≤ sup_{z ∈ [x, y]} E_z‖∇Φₖ‖ · ‖x − y‖`, and `isEChain_of_meanLipschitz` gives equicontinuity of `Pᵏf` for every continuous compactly supported `f`, by uniform continuity and Markov's inequality |
| p. 164 | If `W` is uniformly bounded, (7.27) holds trivially on compact sets | `theorem_7_5_1_i_of_bounded` (`Γ` carried by a compact set; `N` open convex with compact closure) |
| Proposition 7.5.2, p. 164 | If `F` is rational and `E[exp(ε₀\|W₁\|)] < ∞`, then `E[sup_{Φ₀ ∈ C} ‖∇Φₖ‖] < ∞` for compact `C`, and the derivative formula holds; "the proof is straightforward" | `proposition_7_5_2`, with the polynomial bound `‖∇Φₖ(y, u)‖ ≤ c(1 + Σᵢ‖uᵢ‖)ᵐ` for `y` in an open convex `N` as a hypothesis in place of "F rational"; `one_add_pow_le_exp` |
| p. 164 | The conditions on `W` hold for any i.i.d. Gaussian process | Not formalised |

## §7.5.2 Linear state space models

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 7.5.3, p. 165 | LSS(F, G) satisfying (LSS1), (LSS2) and (LSS5) is an e-chain | `proposition_7_5_3` (`lssMatrixKernel`, `IsStableMatrix`, carried; any disturbance law) |
| p. 165 | Proof: `∇Φₖ = Fᵏ` (printed `Fᵐ`), which tends to zero exponentially fast by Lemma 6.3.4, so Theorem 7.5.1 applies | `sensitivity_linear` (`∇Φₖ = Aᵏ`), `isStableMatrix_geometric` (carried), then `theorem_7_5_1_ii` |
| p. 165 | Controllability is not required; (LSS5) is the condition of Proposition 4.4.3; bilinear models can be analysed similarly | `proposition_7_5_3` has no controllability hypothesis; the other remarks are not formalised |

## §7.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 165–166 | Semi-dynamical systems and topological dynamics; the sources of the chapter; the Lie algebra rank characterization of forward accessibility; Stroock and Varadhan; invariant control sets | Not formalised (commentary) |
| p. 166 | Duflo: if `\|F(x, w) − F(y, w)\| ≤ α(w)\|x − y\|` with `E[α(W)ᵐ] < 1` for some sufficiently large `m`, the model is an e-chain | `duflo_isEChain` (`E[α(W)ᵐ] ≤ 1` for some `m ≥ 1`); `enorm_controlMap_sub_le_prod`, `lintegral_le_one_of_lintegral_pow_le_one`, `ennreal_bernoulli` |
| pp. 166–167 | Stability of `∇Φ`, the Lyapunov exponents `Λₓ` and `Λₓ(p)`, hidden Markov models and the filtering process | Not formalised (survey) |
