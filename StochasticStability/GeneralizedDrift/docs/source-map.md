# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University Press,
2009): Chapter 19, pp. 482–509, and Appendix B, pp. 538–542. Equation numbers are the book's. Lean
names are relative to `MeynTweedie.GeneralizedDrift`; names from Mathlib are marked as such. Names
marked "carried" are in the modules carried or copied from the earlier projects (see the
[README](../README.md)). `P_x` is `pathKernel P x` (carried), the law of the chain on the path
space `ℕ → X`, and `𝓕ₖ^Φ` is `natFilt k`. `σ_C` and `τ_C` are `firstHit C` and `firstReturn C`,
and `E_x[τ_C]` is `meanReturnTime P C x` (carried). `ψ` is a maximal irreducibility measure
(`IsMaximalIrreducibility P ψ`, carried) and `B⁺(X)` is `{B : ψ(B) > 0}`. Harris, positive Harris
and positive chains are `IsHarris P ψ`, `IsPositiveHarris P ψ` and `IsPositive P ψ`
(`ψ`-irreducible with an invariant probability), aperiodicity is `IsAperiodic P ψ`, petite and
small sets are `IsPetite P C` and `IsSmall P C`, and an invariant measure is `IsInvariant P π` (all
carried). `ΔV = driftR P V` (carried) is the real drift `∫ P(x, dy) V(y) − V(x)`. A conditional
drift `E[V_{k+1} | 𝓕ₖ^Φ] ≤ Vₖ` on `{σ_C > k}` is stated in integrated form, over the sets
`G ∈ 𝓕ₖ^Φ` with `G ⊆ avoidSet C (k + 1)` (carried). `‖μ − ν‖_f` is `fNorm f μ ν` (carried), and
`‖μ − ν‖` is `fNorm (fun _ => 1) μ ν`, the total variation norm. Every place where the Lean
statement departs from the book is listed in [corrections](corrections.md).

## Chapter 19 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 482 | The one-step drift `ΔV` may be hard to make negative even when the converse theory says a suitable `V` exists | Not formalised (informal) |
| p. 482 | Three generalisations: state-dependent, history-dependent and mixed drift conditions | §§19.1–19.3 below |
| pp. 482–483 | The applications: the walk on `ℝ²₊`, an invasion model, bilinear models, ladder processes and the GI/G/1 queue | `OrthantWalk`, `InvasionModel`, `BilinearDrift`, `LadderDrift`, `GIG1Drift` |

## §19.1.1 The state-dependent drift criteria

| Source | Claim | Lean |
| --- | --- | --- |
| (19.1), p. 483 | The general form `∫ P^{n(x)}(x, dy) V(y) ≤ g[V(x), n(x)]` off a petite set | Not formalised in this generality; its three instances (19.6), (19.10) and (19.15) are |
| (19.2), p. 483 | `P̂(x, A) = P^{n(x)}(x, A)` | `stateKernel P hn` (`stateKernel_apply`, `isMarkovKernel_stateKernel`), through `powKernel` (`powKernel_apply`); `n` is measurable |
| p. 483 | The iterates `s(0) = 0`, `s(k + 1) = s(k) + n(Φ_{s(k)})` are stopping times | `embTime`, `embTime_zero`, `embTime_succ`, `embTime_mono`, `le_embTime` (`s(k) ≥ k` when `n ≥ 1`), `measurableSet_embTime_eq`, `isStoppingTime_embTime` |
| (19.3), p. 483 | `Φ̂ₖ = Φ_{s(k)}` is a Markov chain with kernel `P̂`, by the strong Markov property | `embPath`, `embPath_zero`, `measurable_embPath`, `lintegral_pathKernel_stateTime`, `embPath_isMarkovChain`, `pathKernel_map_embPath` (under `P_x`, `Φ̂` has law `P̂_x`) |
| p. 483 | The σ-fields `𝓕̂ₖ = 𝓕_{s(k)}`; the hitting indices `τ̂_A`, `σ̂_A` of `Φ̂` | `embFilt`, `measurable_embPath_embFilt`; `τ̂_C` is `firstReturn C (embPath n ω)`, `embPath_mem_of_firstReturn_eq` |
| (19.4), p. 483 | `s(τ̂_C) = Σ_{k<τ̂_C} n(Φ̂ₖ)` | `embTime_eq_sum` (`s(k) = Σ_{j<k} n(Φ̂ⱼ)` for every `k`), `partialN` |
| (19.5), p. 484 | `s(τ̂_C) ≥ τ_C` and `s(σ̂_C) ≥ σ_C` | `firstReturn_le_embTime`, `toENNReal_firstReturn_le_sumBefore`, `tpow_firstReturn_le` (the `τ` form, with `n ≥ 1`; see corrections); `firstHit_le_firstReturn'` |
| Theorem 19.1.1, (19.6), p. 484 | For a `ψ`-irreducible chain, `n : X → ℤ₊`, `V ≥ 0` unbounded off petite sets and `C` petite with `∫ P^{n(x)}(x, dy) V(y) ≤ V(x)` off `C`, the chain is Harris recurrent | `theorem_19_1_1` (`n ≥ 1`; "unbounded off petite sets" as every `{V ≤ m}` petite); see corrections |
| (19.7)–(19.9), pp. 484–485 | Proof: if the chain is not Harris, by Theorems 8.0.1, 8.3.5, 9.0.1 and 9.1.3 some initial law gives `σ_C = ∞` and `V(Φₖ) → ∞` with positive probability | Not formalised; replaced by Theorem 9.1.3 and Proposition 9.1.7 (`theorem_9_1_3_ae`, `proposition_9_1_7_ii`, carried) in the proof of `theorem_19_1_1`; see corrections |
| p. 485 | `V(Φ̂ᵢ) 1{σ̂_C ≥ i}` is a positive supermartingale, so either `σ̂_C < ∞` or `V(Φ̂ₖ)` stays bounded | `ae_hit_or_bdd`, through `ae_bddAbove_of_avoid` (carried) for `P̂` |
| Theorem 19.1.2, (19.10)–(19.11), p. 485 | For a `ψ`-irreducible chain, `C` petite, `V ≥ 0` bounded on `C` and `b > 0` with `∫ P^{n(x)}(x, dy) V(y) ≤ V(x) − n(x) + b 1_C(x)`, the chain is positive Harris and `E_x[τ_C] ≤ V(x) + b` | `theorem_19_1_2` (`n ≥ 1`, `V` finite; the bound `V(x) + b 1_C(x)`); `theorem_19_1_2_counterexample` for `n = 0`; see corrections |
| (19.12)–(19.14), p. 485 | The bound `E_x[Σ_{k<τ_C} f(Φₖ)] ≤ V(x) + b` under (19.12) (Theorem 14.2.2), applied to `Φ̂` with `f = n` | `meanReturnTime_le_stateDrift` ((19.11) without irreducibility), through `proposition_11_3_3` (carried) for `P̂` |
| p. 486 | (19.14) with `V` bounded on the petite `C` gives positive Harris recurrence (Theorem 13.0.1) | In the proof of `theorem_19_1_2`, through Theorem 10.4.10 (`theorem_10_4_10_ii`, carried) |
| Theorem 19.1.3, (19.15)–(19.16), p. 486 | For a `ψ`-irreducible aperiodic chain, `C` petite, `V ≥ 1` bounded on `C`, `λ < 1`, `b < ∞` with `∫ P^{n(x)}(x, dy) V(y) ≤ λ^{n(x)}[V(x) + b 1_C(x)]`, the chain is geometrically ergodic with `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ ≤ R V(x)` | `theorem_19_1_3` (positivity, and (19.16) for every invariant probability `π`; `n ≥ 1`, `V` finite at some point) |
| (19.17)–(19.18), p. 486 | `V′ = 2V − 1 ≥ 1` turns (19.15) into (19.18) | In the proof of `kendallMoment_le_stateDrift` |
| p. 486 | `Zₖ = κ^{s(k)} V(Φ̂ₖ)` and Proposition 11.3.2 | `lintegral_sumBefore_geoIncr_le`, with `geoIncr`, `measurable_geoIncr`, `one_add_sum_geoIncr`, `measurable_pow_partialN`, `measurable_pow_partialN'` |
| (19.19), p. 487 | `E_x[κ^{s(τ̂_C)} − 1] ≤ V(x) + b 1_C(x)`, `κ = λ⁻¹` | `kendallMoment_le_stateDrift` (`E_x[κ^{τ_C}] ≤ 2V(x) + 2b 1_C(x)`), with `tpow_firstReturn_le` |
| p. 487 | Geometric ergodicity by Theorem 15.0.1 (ii); `R(x) = E_x[κ^{τ_C}] ≤ (2 + b)V(x)` by Theorem 15.4.1 | `geomG_one_le_kendallMoment` and `theorem_15_4_1` (carried) in the proof of `theorem_19_1_3`, with the constant `c(2 + 2b)` |

## §19.1.2 Models on `ℝ²₊`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 487 | State-dependent criteria suit models on the orthant, where the drift on the faces need not be negative | Not formalised (informal) |
| (19.20), p. 487 | The walk `Φₙ = ([Φₙ₋₁(1) + Zₙ(1)]⁺, [Φₙ₋₁(2) + Zₙ(2)]⁺)` with i.i.d. `Zₙ` | `orthantStep`, `measurable_orthantStep`, `orthantKernel Γ`, `isMarkovKernel_orthantKernel`, `orthantKernel_apply'` |
| p. 487 | Negative mean increments make the chain `δ_{(0,0)}`-irreducible: there is `h > 0` with `P(Z(1) < −h) > h`, `P(Z(2) < −h) > h`, and `Pᵐ((x, y), (0, 0)) > h^{2m}` on a square; squares are small | Under the joint condition `Γ{Z(1) < −h, Z(2) < −h} > 0`: `orthant_pow_zero_ge`, `orthant_exists_side`, `orthant_isPhiIrreducible`, `orthant_isSmall`. For independent coordinates the joint condition holds (`exists_joint_neg_of_prod`); in general the claim fails (`orthant_not_irreducible_counterexample`, `orthantCounterLaw`); see corrections |
| (19.21), p. 487 | By Proposition 14.4.1 the marginal walks are positive Harris with invariant laws of finite mean | Not formalised for this model (the Lean proof does not use the marginal walks) |
| p. 488 | `π₁ × π₂` is invariant | Not formalised (it uses independent coordinates) |
| (19.22)–(19.24), p. 488 | With `V(x, y) = x + y`, one-step drift on `A(M)` and `n`-step drift on the strips `A₁(M, m)`, `A₂(m, M)`, through the `f`-norm ergodic theorem and stochastic monotonicity | Not formalised; replaced by Kingman's quadratic test function `orthantV` (`one_le_orthantV`, `measurable_orthantV`, `max_add_sq_le`, `orthant_drift_real`); see corrections |
| Theorem 19.1.4, (19.25), p. 488 | With negative mean increments and finite second moments the walk is positive Harris, and `E_{(x,y)}[τ_{A(m)}] ≤ c(x + y)` for `A(m) = {x ≥ m, y ≥ m}`, `m` large | `theorem_19_1_4` (positive Harris, `E[τ_C] ≤ 1 + (x⁺)² + (y⁺)² + b` for a square `C`, under the joint condition); (19.25) corrected: `theorem_19_1_4_linear` (`E[τ_C] ≤ c(1 + x⁺ + y⁺)` for a square `C`, with `sq_integral_le_integral_sq`); (19.25) as printed: `theorem_19_1_4_counterexample`; see corrections |
| p. 489 | Only three values of `n` are used; the whole chain could be treated through an `n`-skeleton; boundaries can be analysed separately | Not formalised (remarks) |

## §19.1.3 An invasion/antibody model

| Source | Claim | Lean |
| --- | --- | --- |
| p. 489 | A chain on `ℤ²₊` of invaders and defenders; the total population `S(i, j) = i + j` | `P : Kernel (ℕ × ℕ) (ℕ × ℕ)`, `invS` |
| (A1), (19.26), p. 489 | `E_{i,j}[S(Φ₁)] ≤ i + j − 2ε` in the interior `I = {i, j ≥ 1}`, `ε > ½` | Hypothesis `hA1` of `invasion_stateDrift`, `invasion_meanReturnTime`, `invasion_positiveHarris` (on all of `I`); see corrections |
| (A2), (19.27), p. 489 | `P((i, 0), (0, 0)) = 1` for `i > d`; otherwise a new population of finite mean | Hypothesis `hA2`; the finite mean at `(i, 0)`, `i ≤ d`, is `hfin` of `invasion_positiveHarris` |
| (A3), (19.28), p. 489 | From `(0, j)`, `j > 0`, the chain moves to `(j + k, j)` with `1 ≤ k ≤ d` | Hypothesis `hA3` |
| p. 490 | The chain is `δ_{(0,0)}`-irreducible under (A1)–(A3), whatever happens at zero; the increments from `(0, 0)` have finite mean | Not formalised: irreducibility is a hypothesis of `invasion_positiveHarris`; see corrections. The finite mean at `(0, 0)` is the case `i = 0` of `hfin` |
| (19.29), p. 490 | Left continuity (bounded negative increments) | Hypothesis `hLC`: in `I` neither coordinate decreases by more than one in a step; see corrections |
| p. 490 | `V(i, j) = (i + j)/β`; by (V2) in the interior, `E_{i,j}[τ_{Iᶜ}] < (i + j)/β` | `invV`, `invasion_pow_le` (the `m`-step drift `E_x[S(Φₘ)] ≤ S(x) − 2εm` while both coordinates are at least `m`). The interior bound is not stated separately; it is implied by `invasion_meanReturnTime`, since `C ⊆ Iᶜ` |
| p. 490 | On `B₁(c)`, (19.10) with `n = 1` for `c > max(d, β⁻¹)`; on `B₂(c)`, the `(j + 1)`-step drift is at most `[j + d − 2jε]/β`, so (19.10) holds with `n(0, j) = j + 1` when `β < 2ε − 1` and `c > (d + β)/(2ε − 1 − β)` | `invasion_stateDrift`, with `n = invN c`, the test set `invC c` and `b = invB P β c`; the constants are `0 < β < 2ε − 1`, `d < c`, `β ≤ c` and `d + β ≤ (2ε − 1 − β)c`; see corrections |
| p. 490 | `E_{(i,j)}[τ_C] ≤ (i + j)/β` regardless of `d`, so the invasion succeeds | `invasion_meanReturnTime` (off the finite set `C`); positive Harris recurrence by Theorem 19.1.2: `invasion_positiveHarris` |
| p. 490 | No fixed number of steps gives a negative drift on all of `B₂(c)` | Not formalised (remark) |
| (19.30)–(19.31), pp. 490–491 | Geometric ergodicity with `V(i, j) = e^{αi} + e^{αj}` under geometric tails and bounded second moments | Not formalised (a sketch); see corrections |

## §19.2.1 Generalized criteria for positivity and nullity

| Source | Claim | Lean |
| --- | --- | --- |
| p. 491 | Test functions `Vₖ = Vₖ(Φ₀, …, Φₖ)`, non-negative and measurable | `Vs : ℕ → (ℕ → X) → ℝ≥0∞` (or `ℝ≥0`, `ℝ`) on path space |
| p. 492 | Adapted sequences; `σ_C > k` means `Φᵢ ∈ Cᶜ` for `0 ≤ i ≤ k` | `Measurable[natFilt k] (Vs k)` where used; `lt_firstHit_iff_mem_avoidSet`, `coe_lt_iff_succ_le`, `firstHit_eq_top_iff` |
| (19.32), p. 492 | The generalized negative drift: `E[V_{k+1} \| 𝓕ₖ^Φ] ≤ Vₖ − ε` on `{σ_C > k}` | Hypothesis `hdrift` of `theorem_19_2_1` |
| Theorem 19.2.1, p. 492 | Under (19.32), `E_x[τ_C] ≤ ε⁻¹V₀(x)` off `C` and `≤ 1 + ε⁻¹PV₀(x)` on `C`; if `C` is petite and `sup_C E_x[V₀(Φ₁)] < ∞`, the chain is regular | `theorem_19_2_1`, `meanHitTime_le_of_genNegDrift`; `theorem_19_2_1_regular` (Theorem 11.3.15, `theorem_11_3_15`, carried) |
| p. 492 | Proof: Proposition 11.3.3 with `Zₖ = Vₖ`, `εₖ = ε` | In the proof of `meanHitTime_le_of_genNegDrift` |
| (19.33), p. 492 | The generalized positive drift; `Vₖ ≡ 1` satisfies it | Hypothesis `hdrift` of `theorem_19_2_2`; the remark is not formalised |
| Theorem 19.2.2, (19.34)–(19.35), p. 493 | Under (19.33), `V₀(x₀) > Vₖ(x₀, …, xₖ)` for `xₖ ∈ C`, and conditional increments bounded in mean, `E_{x₀}[τ_C] = ∞` | `theorem_19_2_2` ((19.34) almost surely under `P_{x₀}`); see corrections |
| p. 493 | Proof: that of Theorem 11.5.1 | In the proof of `theorem_19_2_2` |

## §19.2.2 Generalized criteria for geometric ergodicity

| Source | Claim | Lean |
| --- | --- | --- |
| (19.36), p. 493 | A coercive sequence: `Vₖ(x₀, …, xₖ) ≥ V(xₖ)` for a coercive `V` | Hypotheses `hV : IsCoercive V` (carried) and `hVV` of `theorem_19_2_3`, `theorem_19_2_4` |
| (19.37), p. 493 | The generalized geometric drift `E[V_{k+1} \| 𝓕ₖ^Φ] ≤ λVₖ + L` | Hypothesis `hdrift` of `theorem_19_2_3` |
| Theorem 19.2.3, p. 493 | For an irreducible aperiodic T-chain with (19.37) and `V₀` bounded on compacta, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R(V₀(x) + 1)` with `f = V + 1`; the chain is `f`-geometrically ergodic | `theorem_19_2_3` (positivity, `π(f) < ∞` and the bound for every invariant probability); `theorem_19_2_3_driftV4` (positive Harris, and a (V4) function `W ≥ f` for a petite set) |
| p. 494 | Proof: `C = {V ≤ 2L/(ρ − λ) + 1}`, `ε = (ρ − λ)/2`, the drift `ρVₖ − εf(Φₖ)` off `C`, and Dynkin's formula for `Zₖ = rᵏVₖ` | `geomDrift_arith`, `setLIntegral_geomDrift_le`, `sumBefore_eq_zero_add`, `geomSum_le_of_genGeomDrift`; then `theorem_15_4_1` (carried) |

## §19.2.3 Generalized criteria for non-evanescence and transience

| Source | Claim | Lean |
| --- | --- | --- |
| (19.38), p. 494 | The generalized non-positive drift for a coercive sequence and a compact `C` | Hypothesis `hdrift` of `theorem_19_2_4` |
| Theorem 19.2.4, p. 494 | Under (19.38) the chain is non-evanescent; a `ψ`-irreducible T-chain is then Harris recurrent | `theorem_19_2_4`, `theorem_19_2_4_harris` (Theorem 9.2.2, `theorem_9_2_2_ii`, carried) |
| (19.39), p. 495 | Proof: the killed sequence `Mᵢ = Vᵢ 1{σ_C ≥ i}` is a positive supermartingale | `killedSeq`, `killedSeqE`, `killedSeq_nonneg`, `ofReal_killedSeq`, `measurable_natFilt_killedSeq`, `setLIntegral_killedSeqE_succ_le`, `lintegral_killedSeqE_le`, `ae_bdd_of_avoid_seq` |
| (19.40), p. 495 | The generalized non-negative drift for a uniformly bounded sequence | Hypothesis `hdrift` of `theorem_19_2_5` |
| Theorem 19.2.5, p. 495 | If `Vₖ ≤ L` and `Vₖ ≤ M` at `σ_A = k`, `L > M`, then `P_x{σ_A = ∞} ≥ (V₀(x) − M)/(L − M)`; if `A` and `{V₀ > M}` are in `B⁺(X)` the chain is transient | `theorem_19_2_5`, `theorem_19_2_5_transient` |
| pp. 495–496 | Proof: `Mₖ` is a submartingale; Kolmogorov's inequality for `L − Mₖ` | In the proof of `theorem_19_2_5`, without Kolmogorov's inequality; see corrections |

## §19.2.4 The dependent parameter bilinear model

| Source | Claim | Lean |
| --- | --- | --- |
| p. 496 | `θₖ₊₁ = αθₖ + Zₖ₊₁`, `Yₖ₊₁ = θₖYₖ + Wₖ₊₁`, `\|α\| < 1` | `dblKernel Γz Γw α` (carried); the innovations read off the path, `dblZ`, `dblW`; `s = dblS α`, `dblS_pos` |
| p. 496 | No (V4) test function has been computed for this model; a history-dependent one can be | Not formalised (remark); `theorem_19_2_3_driftV4` does produce a (V4) function, not explicitly |
| (19.41), p. 496 | `ζ_z² = E exp(2\|Z₁\|/(1 − \|α\|) − 2) < 1` | Hypothesis `hζ` of `theorem_19_2_6` |
| Theorem 19.2.6, p. 496 | Under (DBL1)–(DBL2) and (19.41), the chain is geometrically ergodic with a unique invariant probability `π`; the CLT and LIL hold for `Y` and `θ`; `N⁻¹ Σ Yₖ² → ∫ y² dπ < ∞` a.s.; `\|E_x[Yₖ²] − ∫ y² dπ\| ≤ M(x)ρᵏ` with `M` continuous | `theorem_19_2_6` (positivity, uniqueness of `π`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ < ∞`, `∫ y² dπ < ∞`, the moment bound), `theorem_19_2_6_limits` (positive Harris, the LLN for `Yₖ²`, the CLT and LIL for every `g` with `g² ≤ K(θ² + y²)`), with `sq_le_exp_div`, `DriftV4.const_mul` |
| p. 497 | The joint process is an aperiodic `ψ`-irreducible T-chain, as in Proposition 17.3.5 | Hypotheses `hψ`, `hap`, `hT`; see corrections |
| (19.42), p. 497 | `\|Π θᵢ\| ≤ e^{−(k−j+1)} exp(Σ \|θᵢ\|)` | `abs_prod_le_prod_exp` |
| (19.43), p. 497 | `Σ \|θᵢ\| ≤ (1 − \|α\|)⁻¹(\|α\|\|θ_{j−1}\| + Σ \|Zᵢ\|)` | `sum_le_of_ar_bound`, `abs_prod_theta_le` |
| (19.44), p. 497 | The bound on `\|Π_{i=j}^k θᵢ\|` | `abs_prod_Ico_theta_le` |
| (19.45), p. 497 | `Y²ₖ₊₁ ≤ 3Aₖ + 3Bₖ + 3W²ₖ₊₁`, from (17.28) | `dbl_Y_sq_le`, `dbl_Y_expand` ((17.28) along the path), `sq_add_le_eps`; `dblA`, `dblSqrtA`, `dblB`, `dblE`, `dblE_sq` |
| p. 497 | `Cₖ = exp(2\|α\|s\|θₖ\|)` and the three conditional bounds, from [275] | Proved: `dbl_condA`, `dbl_condB`, `dbl_condC` (for `exp(c\|θₖ\|)`, any `c ≥ 0`; `dblC`), and `dbl_condY`; tools `dblSqrtA_succ`, `dblB_succ`, `dblA_succ_le`, `lintegral_pathKernel_two`, `setLIntegral_mul_step`, `lintegral_dblKernel`, `lintegral_prod_mul_dbl`, `rpow_mul_le_amgm`, and the measurability lemmas `measurable_coord_natFilt_le`, `measurable_dblZ_natFilt`, `measurable_dblW_natFilt`, `measurable_dblA_natFilt`, `measurable_dblB_natFilt`, `measurable_dblCoord_natFilt` |
| p. 498 | `Vₖ = ε³Yₖ² + ε²Aₖ + Bₖ + Cₖ` dominates a coercive `V(y, θ)`, so `{Vₖ}` is coercive | `dblVs` (with `Cₖ = exp(2s\|θₖ\|)`), `isCoercive_dblV`, `measurable_dblVs_natFilt`, `dblV0`, `continuous_dblV0`, `dblVs_zero`; the book's `V`: `dbl_bookV_not_coercive`; see corrections |
| p. 498 | The bound on `E[Vₖ₊₁ \| 𝓕ₖ^Φ]`, its rearrangement, `λ = max(…)` and `λ < 1` for small `ε` | `dbl_drift`, `dblLam`, `exists_dblLam_lt_one`; see corrections for `3ε³Aₖ²` |

## §19.3.1 The limiting-average drift

| Source | Claim | Lean |
| --- | --- | --- |
| p. 498 | Mixed drifts: inward on average for positive chains, outward for null ones | Not formalised (informal) |
| (19.46), p. 499 | `∫ P(x, dy) \|V(y) − V(x)\| ≤ d < ∞` | Hypothesis `hinc` (constant `B`, extended norm); `driftR_eq_integral`, `integral_abs_sub_le`, `abs_driftR_le`, `measurable_driftR`, `integrable_driftR` |
| p. 499 | `∫ Pⁿ(x, dy) \|ΔV(y)\| ≤ d`, so the averages (19.47) are finite | `lintegral_enorm_pow_le` (`∫ Pᵏ(x, dy) \|V(y)\| ≤ \|V(x)\| + kB`), `integrable_pow_of_increments`, `abs_driftR_le` |
| Theorem 19.3.1, (19.48), p. 499 | For a `ψ`-irreducible chain and `V ≥ 0` with (19.46), a negative `lim inf` of `n⁻¹ Σ_{k=1}^n ∫_{Cᶜ} Pᵏ(x, dy) ΔV(y)` at one `x`, for a petite `C`, gives positivity | `theorem_19_3_1` ((19.48) as "`≤ −η` infinitely often"), `not_tendsto_pow_of_mixedDrift` |
| (19.49), p. 499 | `∫ Pⁿ⁺¹(x, dy) V(y) = ∫ Pⁿ(x, dy) ΔV(y) + ∫ Pⁿ(x, dy) V(y)` | `integral_pow_driftR`, `sum_integral_pow_driftR` |
| (19.50), p. 499 | `lim inf n⁻¹ Σ_{k=1}^n ∫ Pᵏ(x, dy) ΔV(y) ≥ 0` | `eventually_cesaro_drift_ge`; see corrections |
| p. 499 | A null chain has `Pⁿ(x, C) → 0` for petite `C` (Theorem 18.2.2) | `IsNull.tendsto_pow_of_isPetite` (copied, `PositivityPn`), in the proof of `theorem_19_3_1` |
| Theorem 19.3.2, (19.51), p. 500 | For a positive chain with invariant `π` and `V` with (19.46), `∫ π(dy) ΔV(y) = 0` | `theorem_19_3_2` (an invariant probability suffices) |
| (19.52)–(19.55), p. 500 | `M_z`, the mean value bound, `\|M_z\| ≤ d/z`, `M_z → ΔV` and dominated convergence | `abs_exp_sub_exp_le`, `abs_rpow_sub_rpow_le` (19.52), `abs_log_le_two_mul` (from (19.53)), `zSeq`, `zSeq_mem`, `tendsto_zSeq`, `tendsto_rpow_slope` (19.54); (19.55) in the proof of `theorem_19_3_2` |
| p. 500 | Without (19.46) the balance (19.51) fails: a positive chain with strictly positive drift (§11.5.1) | `theorem_11_5_2_counterexample` (copied, `NonPositivity`) |
| Theorem 19.3.3, (19.56)–(19.57), p. 501 | For a `ψ`-irreducible chain, `V ≥ 0` with (19.46) and a sublevel set `C` with `C, Cᶜ ∈ B⁺(X)`, positivity requires `∫_{Cᶜ} π ΔV < 0`, and then the averages of (19.48) converge to it for almost all `x`; so (19.48) is necessary and sufficient | `theorem_19_3_3` (19.56), `tendsto_cesaro_setIntegral_driftR` (19.57), `theorem_19_3_3_iff` (with `C` petite) |
| (19.58)–(19.62), p. 501 | `V > sup_C V` off `C`; `\|ΔV\|` bounded on `C`; the expansion of `∫_C π ΔV` by invariance; the flow out of `C` is positive | In the proof of `setIntegral_driftR_pos`; `lintegral_kernel_of_invariant`, `flow_pos` |
| (19.63), p. 502 | The balanced flow `∫_C π(dx) P(x, Cᶜ) = ∫_{Cᶜ} π(dx) P(x, C)` | `flow_balance` |
| (19.64), p. 502 | `∫_C π ΔV > 0` | `setIntegral_driftR_pos` |
| p. 502 | (19.56) from (19.51) and (19.64); (19.57) "identical" to (19.56) | `theorem_19_3_3`; (19.57) through the Cesàro ergodic theorem `tendsto_cesaro_integral_of_isPositive` (from Theorem 13.3.4 (ii), `theorem_13_3_4_ii`, carried), `tendsto_cesaro_of_phase`, `tendsto_cesaro_shift`; see corrections |
| p. 502 | The criteria of §11.3 and §11.5.1 are the extreme cases | Not formalised (remark) |

## §19.3.2 A mixed drift criterion for stability of the ladder chain

| Source | Claim | Lean |
| --- | --- | --- |
| p. 502 | The ladder chain (10.37) | `ladderChainKernel Λ Λs` (carried, `LadderChains`), on `ℤ₊ × ℝ` |
| (19.65), p. 502 | Homogeneous zero-level transitions `Λ*ᵢ = Σ_{j>i} Λⱼ` | `ladderStar`, `avgLadderKernel Λ`, `isMarkovKernel_avgLadderKernel` |
| p. 502 | `Λ = Σⱼ Λⱼ` is stochastic and defines the marginal chain `Φ^Λ` | `ladderMarg Λ` (Markov by hypothesis), `tsum_ladder_univ` |
| (19.66), p. 502 | `Pⁿ(i, x; ℤ₊ × B) = Λⁿ(x, B)` | `avgLadderKernel_snd_preimage`, `avgLadderKernel_pow_map_snd`, `avgLadderKernel_pow_snd_preimage` |
| p. 502 | `Φ^Λ` is `ψ*`-irreducible, `ψ*(B) = ψ(ℤ₊ × B)` | `ladderMarg_isPhiIrreducible` |
| (19.67), p. 503 | The expected change in ladder height `β(w) = Σⱼ jΛⱼ(w, X)` | `ladderBeta`; the truncations `truncBeta`, `measurable_truncBeta`, `truncBeta_le` |
| p. 503 | If `β > 1 + δ` everywhere, the bottom of the ladder is reached in finite mean time | Not formalised (remark) |
| Theorem 19.3.4, (19.68), p. 503 | For a `ψ`-irreducible chain with (19.65), if `Φ^Λ` has an invariant probability `ν` with `∫ ν β > 1`, the chain has an invariant probability | `theorem_19_3_4` |
| (19.69), p. 503 | `ΔV(i, w)` for `V(i, w) = i`, and its monotonicity in `i` | `lintegral_fst_ladderKernel`, `meanRung_add_truncBeta_le` |
| (19.70), (19.74), pp. 503–504 | The averaged drift has `lim inf ≥ 0`; its decomposition at level `d` | `cesaro_truncBeta_bound` (the summed drift) |
| (19.71)–(19.73), pp. 503–504 | The choice of `d` and of the sets `D_v` | Replaced by the truncated heights in the proof of `theorem_19_3_4`; see corrections |
| (19.75), p. 504 | Every rung of a null chain is null in the Cesàro sense | `tendsto_cesaro_low_of_isNull` (Theorem 18.2.2 for a petite cover) |
| (19.76), p. 505 | `ν` is the limit of the averages over the rungs `j ≥ d` | Not stated separately: the proof of `theorem_19_3_4` applies the Cesàro ergodic theorem for `Φ^Λ` (`tendsto_cesaro_integral_of_isPositive`) to `h_d` directly |
| p. 505 | Whether (19.68) suffices without (19.65) | Not formalised (informal) |
| (19.77), p. 505 | Under (19.68), `E_{0,y}[τ_{[0]}] < ∞` for `ν`-a.e. `y`, since the quantity does not depend on the hitting distribution on `[0]` | Not formalised; see corrections. For the GI/G/1 queue the needed (19.82) is proved directly (`theorem_19_3_5_ii`) |
| (19.78)–(19.79), p. 505 | The up-or-down ladder on `X = ℤ₊` | `exLam p q`, `twoPoint`, `twoPoint_apply`, `exDown`, `exUp`, `measurable_exDown`, `measurable_exUp`, `exDown_natCast`, `exUp_natCast`, `tsum_exLam` |
| p. 505 | `Φ^Λ` is a random walk on the half line with an invariant probability iff `p > ½` | `exMarg_apply`, `isMarkovKernel_exMarg`, `exMarg_hasInvariant_iff`, with `exNu`, `exWeight`, `lintegral_exNu`, `exRatio_mem`, `exWeight_nonneg`, `isProbabilityMeasure_exNu`, `exWeight_balance`, `isInvariant_exNu`, `indicator_natCast_singleton`, `exMarg_not_invariant` |
| p. 505 | `β(x) > 1` iff `q < ½`; (19.68) holds if `q < ½ < p` | `exBeta` (`β = 2(1 − q)`), `one_lt_exBeta_iff`, `exLadder_isPositive` |
| p. 506 | This chain falls under Theorem 19.3.4 | `exLadder_isPositive`, with `exLadder_step_ge`, `exLadder_pow_ge`, `exLadder_isPhiIrreducible` |
| (19.80), p. 506 | The bottom rung `Λ*₀(x, x ∓ 1) = r(1 − q), (1 − r)(1 − q)`, `Λ*₁` as in (19.65) | `ex80Star p q r`, `isMarkovKernel_ex80`, `twoPoint_univ`, `ofReal_split` |
| (19.81), p. 506 | A lower bound for the mean increment of the process `Φ^{[0]}` on `[0]`, through a mean return time `(1 − q)/(1 − 2q)` from rung `1` | Not formalised as printed; see corrections |
| p. 506 | `Φ^{[0]}` is transient if `r` and `q` are small and `p − ½` is not too large | `eq_19_81_transient` (for `q < ½` and `(1 − q)(1 − 2r) − q(2p − 1)(1 + 1/(1 − 2q)) > 0`), with `ex80_exists_test`, `ex80_superharmonic`, `four_exp_le`, `mul_exp_le`, `exp_le_quad`, `ex80W`, `ex80V`, `lintegral_ladderChainKernel`, `lintegral_twoPoint`, `lintegral_twoPoint_ex80V` and Proposition 8.4.1 (`proposition_8_4_1`, carried) |
| p. 506 | `[0]` is not petite here, although it behaves much like a petite set | `ex80_rung_zero_not_petite`; for (19.79) as well, `exLadder_rung_zero_not_petite`; through `not_isPetite_of_bounded_steps`, `ladderChainKernel_step_ge`, `ladderChainKernel_snd_preimage`, `twoPoint_Iio`, `exLam_Iio`; see corrections |
| p. 506 | (19.77) holds, yet the chain need not be recurrent | Not formalised (remark) |

## §19.3.3 Stability of the GI/G/1 queue

| Source | Claim | Lean |
| --- | --- | --- |
| p. 506 | The ladder chain models the GI/G/1 queue (§3.5); (19.65) fails | `gig1Ladder H G`, `gig1Lambda H G` (carried, `LadderChains`) |
| p. 506 | `[0]` is petite (§10.5.3), and the process on `[0]`, if honest, has invariant measure `H` | Not formalised as stated (the carried `proposition_5_3_2_gig1` makes `{0} × (−∞, β]` small when `G(β, ∞) > 0`) |
| (19.82), p. 506 | It remains to check `∫ H(dy) E_{0,y}[τ_{[0]}] < ∞` | `theorem_19_3_5_ii`, with `lintegral_meanReturnTime_gig1` (the mean number of customers in a busy period) and `gig1Tilde_univ_le` |
| Theorem 19.3.5, p. 506 | The GI/G/1 queue satisfies (19.68) iff `λ > µ`, and then has the invariant measure (10.52) | `theorem_19_3_5` (first part), `theorem_19_3_5_ii` (second part, through Theorem 10.5.4, `theorem_10_5_4_invariant`, carried) |
| p. 507 | `Λ(x, [0, y]) = ∫ G(dt) Pᵗ(x, y)`; the stationary forward recurrence law `ν` of (10.36) is invariant for every `Pᵗ`, hence for `Λ` | `isInvariant_eqLaw_gig1`, `eqLaw` (copied, `RenewalEquilibrium`) |
| p. 507 | `β(x) = ∫ G(dt) E[N(t) \| R₀ = x]` | `ladderBeta_gig1`, with `tsum_mul_straddle`, `tsum_straddle_mem`, `tsum_mul_prod_apply`, `resEpoch_mono'`, `ae_nonneg_of_Iio`, `renMean_ne_zero` and `renMeas` (copied) |
| (19.83), p. 507 | `∫ ν(dx) E[N(t) \| R₀ = x] = t/µ`, so `∫ ν β = λ/µ` | `lintegral_ladderBeta_gig1`, through `renMeas_eqLaw` (copied) |
| (19.84), p. 507 | `E_{0,y}[τ_{[0]}] = 1 + η Σ_{n≥0} G^{n∗}[0, y]` by rearranging the order of service | False: `eq_19_84_counterexample` (with `ddArr`, `ddServ`, `ddServ_pos`, `queueN_ne_zero_iff`, `arrT_lt_sum_of_busy`); see corrections |
| (19.85), p. 508 | `Σ_{n≥0} G^{n∗}[0, y] ≤ y(λ⁻¹ + ε)` for large `y` (Blackwell's renewal theorem) | Not formalised; replaced by Wald's bound: `wU`, `wE`, `measurable_wU`, `measurableSet_wE`, `wE_anti`, `wE_zero`, `wald_pathwise`, `mem_wE_truncSeq_iff`, `lintegral_wE_indicator`, `tsum_wE_le`, `lintegral_coord_zero_prod`, `exists_wald_trunc`, `ofReal_sum_range_le`, `mem_wE_of_le_firstReturn` |
| p. 506 | The result complements Proposition 11.4.4 | Not formalised (remark) |

## §19.4 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 508–509 | History and literature: state-dependent drift, random `n(x)`, the orthant, the antibody model, history-dependent drift, the bilinear model, mixed drifts and Kaplan's condition, ladder processes, the GI/G/1 queue, Dai's fluid models, the second edition | Not formalised (commentary) |
| p. 508 | With a quadratic test function one can take `n = 1` under second moments (Kingman) | `orthant_drift_real`, `theorem_19_1_4` |
| p. 508 | The linear bound (19.25) appears to be new | `theorem_19_1_4_linear` (corrected form) |

## Appendix B.1 Glossary of drift conditions

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 538–540 | The test function `V` and test set `C`; (V1), (V2), (V3), (V4), the form (15.35) of (V4), and the transience/nullity criterion (8.41), with the theorems that use them | Not formalised as a unit (a summary of earlier chapters). The carried modules contain, among others, (V1) in `theorem_8_4_3` and `theorem_9_4_1`; (V2) as `DriftV2` with `theorem_11_3_4`, `theorem_11_3_15`, `theorem_13_0_1`; (V3) as `DriftV3` with `theorem_14_2_2` and `theorem_17_5_3` (copied); (V4) as `DriftV4` with `lemma_15_2_8` and `theorem_15_0_1`; (8.41) in `theorem_8_4_2` and `theorem_11_5_1`. The results of Chapters 12 and 16 and of §20.1 cited there are not carried |
| p. 540 | Quadratic forms are the most useful test functions on `ℝᵏ`; Chapter 19 offers alternatives | Not formalised (remark) |

## Appendix B.2 The scalar SETAR model: a complete classification

| Source | Claim | Lean |
| --- | --- | --- |
| p. 540 | `Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)` for `Xₙ₋₁ ∈ Rⱼ`, with independent zero-mean noises | `setarKernel Γ φ θ r` (carried); regime `1` is `0 : Fin (m + 1)` and regime `M` is `Fin.last m` |
| p. 540 | (i) noise densities positive on `ℝ`; (ii) finite variances in the end regimes | Hypotheses `h1`, `h2` (`Γⱼ` and Lebesgue measure mutually absolutely continuous), `hW`, `hW0`, `hW2₀`, `hW2M` of `setar_classification` |
| Figures B.1–B.3, pp. 540–542 | The `(θ(1), θ(M), φ(1), φ(M))` space splits into a regular interior (11.36)–(11.40), null margins (11.45)–(11.49) and a transient exterior (9.46)–(9.51) | `SetarInterior`, `SetarMargin`, `SetarExterior`; `setar_regions_cover`, `setar_regions_disjoint` |
| p. 541 | Harris recurrent in the interior and on the margins, transient in the exterior; null on the margins; regular and geometrically ergodic in the interior | `setar_classification` (regular, positive Harris and compact sets regular in the interior; Harris and null on the margins; transient in the exterior); geometric ergodicity on (11.36): `setar_geometric_36`; see corrections |
| STEP 1, p. 541 | A `μ_Leb`-irreducible T-chain (cited as Theorem 6.3.6), so compact sets are test sets | `setar_classification` (first conjunct, with compact sets small), from `proposition_6_3_6` (carried); aperiodicity: `setar_isAperiodic` |
| STEP 2, p. 541 | Geometric ergodicity in the interior by (V4) with linear test functions (Proposition 11.4.5) | Regularity in the interior from `proposition_11_4_5` (copied, `DriftExamples`); (V4) with a linear `V` on (11.36): `setar_real_driftV4_36`, `setar_geometric_36`; its failure at a unit-slope end: `setar_not_linear_driftV4_top`, `setar_not_linear_driftV4_bot`; see corrections |
| STEP 3, pp. 541–542 | Transience in the exterior by Proposition 9.5.4 with a bounded test function and Theorem 8.4.2 | `proposition_9_5_4` (copied, `SETAR`), in `setar_classification` |
| STEP 4, p. 542 | Recurrence on the margins by Proposition 11.5.4 with logarithmic test functions; nullity by Proposition 11.5.5 | `proposition_11_5_4` (copied, `SetarMarginRecurrence`), `proposition_11_5_5_all` (copied, `SetarNullMargins`), in `setar_classification` |
| p. 542 | The model reduces to the two linear end regimes; more detail in Tong, multidimensional versions in Brockwell, Liu and Tweedie | Not formalised (remarks) |
