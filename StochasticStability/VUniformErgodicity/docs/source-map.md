# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University Press,
2009): Chapter 16, pp. 392–420. Equation numbers are the book's. Lean names are relative to
`MeynTweedie.VUniformErgodicity`; names from Mathlib are marked as such. Names marked "carried" are
in the modules copied from the earlier projects (see the [README](../README.md)). `ψ` is a maximal
irreducibility measure (`IsMaximalIrreducibility P ψ`, carried), `B⁺(X)` is `{B : ψ(B) > 0}`, and
"positive" is `IsPositive P ψ` (carried): `ψ`-irreducible with an invariant probability.
`|||P₁ − P₂|||_V` is `vOpNorm V P₁ P₂`, the outer product `1 ⊗ μ` is `Kernel.const X μ` (Mathlib),
and `|||Pⁿ − 1 ⊗ μ|||_V` is `vErgDist V P μ n`. `‖μ − ν‖_f` is `fNorm f μ ν` and `‖μ − ν‖` is
`tvNorm μ ν` (carried). (V4) is `DriftV4 P V ρ b C` (carried), `PV ≤ ρV + b 1_C` with `ρ = 1 − β`.
`E_x[τ_C]` is `meanReturnTime P C x`, `E_x[σ_C]` is `meanHitTime P C x` and `E_x[κ^{τ_C}]` is
`kendallMoment P C κ x` (carried). `Γ ∈ G⁺(γ)` is `IsLaplaceFinite Γ γ`. The chain restricted to an
absorbing set `A` is `restrictKernel P hA` (carried). Every place where the Lean statement departs
from the book is listed in [corrections](corrections.md).

## Chapter 16 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 392 | The chapter's aims: geometric ergodicity as convergence in an operator norm, with uniform ergodicity as the special case `V ≡ 1`; many verifications of (V2) or (V3) in earlier chapters in fact gave (V4) | Not formalised (informal) |
| (16.1), p. 392 | For `∞ > V ≥ 1`, `|||P₁ − P₂|||_V = sup_x ‖P₁(x, ·) − P₂(x, ·)‖_V / V(x)` | `vOpNorm` (valued in `[0, ∞]`); `fNorm_le_vOpNorm_mul`, `vOpNorm_le` |
| p. 392 | The outer product `[1 ⊗ π](x, A) = π(A)`, and the distances `|||Pᵏ − 1 ⊗ π|||_V` | `Kernel.const X π` (Mathlib); `vErgDist`, `fNorm_pow_le_vErgDist_mul` |
| (16.2), p. 392 | An ergodic chain is `V`-uniformly ergodic if `|||Pⁿ − 1 ⊗ π|||_V → 0` | `IsVUniformlyErgodic V P μ` (`μ` invariant and the distances tend to `0`; the theorems add `ψ`-irreducibility and aperiodicity) |
| p. 393 | Three consequences of Theorem 15.0.1 are developed | Not formalised (informal) |
| Theorem 16.0.1, (16.3)–(16.5), p. 393 | For a `ψ`-irreducible aperiodic chain and `V ≥ 1`: (i) `V`-uniform ergodicity, (ii) `|||Pⁿ − 1 ⊗ π|||_V ≤ R r⁻ⁿ`, (iii) finite distances up to some `n` with `|||Pⁿ − 1 ⊗ π|||_V < 1`, and (iv) (V4) for a petite set and some `V₀` with `c⁻¹V ≤ V₀ ≤ cV`, are equivalent | False as printed: `theorem_16_0_1_counterexample` ((i) does not give (ii); `twoStep`, `twoStepKernel`, `twoStepWeight`, `isMarkovKernel_twoStepKernel`, `twoStep_twoStep`, `twoStepKernel_pow_add_two`, `twoStepWeight_mem`, `isInvariant_twoStepKernel`, `twoStep_vErgDist_add_two`, `twoStep_vErgDist_one`). Corrected: `theorem_16_0_1` (a `List.TFAE`, Mathlib; (i) with every distance finite; `V` measurable and finite, `μ` an invariant probability); see corrections |
| p. 393 | Proof: (i)–(iii) by Proposition 16.1.3; (iv) ⇒ (ii) by Theorem 16.1.2; (ii) ⇒ (iv) by Theorem 16.1.4 | In the proof of `theorem_16_0_1`: `proposition_16_1_3`, `vErgDist_le_geometric`, `vErgDist_le_of_driftV4` with `vErgDist_le_of_equiv`, `theorem_16_1_4` |
| p. 393 | Preview of Theorem 16.1.5 | `theorem_16_1_5` |
| (16.6), p. 393 | Uniform ergodicity: `V`-uniform ergodicity for `V ≡ 1`, `sup_x ‖Pⁿ(x, ·) − π‖ → 0` | `IsUniformlyErgodic P μ`; `vErgDist_one_eq`, `isUniformlyErgodic_iff` |
| Theorem 16.0.2, (16.7)–(16.10), p. 394 | For any chain the following are equivalent: (i) uniform ergodicity; (ii) a uniform geometric rate (16.7); (iii) `sup_x ‖Pⁿ(x, ·) − π‖ < 1` for some `n` (16.8); (iv) aperiodicity and Doeblin's condition (16.9); (v) `X` is `νₘ`-small; (vi) aperiodicity and a petite `C` with `sup_x E_x[τ_C] < ∞`; (vii) the same with `E_x[κ^{τ_C}]`; (viii) aperiodicity and a bounded solution of (16.10) for a petite set | `theorem_16_0_2` (a `List.TFAE`, Mathlib, for a `ψ`-irreducible chain; `IsDoeblin`; `IsSmallSet`, `IsPetite`, carried); the "in which case" parts of (vi)–(vii) are `theorem_16_2_2_hitting`; see corrections |
| (16.11), p. 394 | Under (v), `‖Pⁿ(x, ·) − π‖ ≤ 2ρ^{n/m}` with `ρ = 1 − νₘ(X)` | False with the real exponent: `theorem_16_2_4_counterexample`. Corrected: `theorem_16_2_4`, with `⌊n/m⌋` |
| p. 395 | Proof: Theorems 16.2.1–16.2.4 | `theorem_16_2_1`, `theorem_16_2_2`, `theorem_16_2_3`, `theorem_16_2_4`, with `isAperiodic_of_isSmallSet_univ` and `isSmallSet_univ_of_isUniformlyErgodic` in the proof of `theorem_16_0_2` |
| p. 395 | Uniform convergence is `V`-geometric ergodicity with bounded `V`; moving from a test function `V` to `e^{sV}` | Not formalised (informal); the method is Theorem 16.3.1 |

## §16.1.1 The operator norm `||| · |||_V`

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 16.1.1, p. 395 | `L∞_V` is the vector space of functions with `|f|_V = sup_x |f(x)|/V(x) < ∞`; if `|||P₁ − P₂|||_V < ∞`, then `P₁ − P₂` is a bounded operator on `L∞_V` with operator norm `|||P₁ − P₂|||_V` | `lemma_16_1_1` (`|||P₁ − P₂|||_V = sup_{|g|_V ≤ 1} |P₁g − P₂g|_V` when `P₁(x, V)`, `P₂(x, V)` are finite), `lemma_16_1_1_bounded` (`|P₁g − P₂g|_V ≤ |||P₁ − P₂|||_V |g|_V`); `vNormFn` (real functions), `vNormFn_add_le`, `vNormFn_smul`, `vNormFn_le`, `vNormFn_le_one_iff`, `ofReal_abs_le_vNormFn_mul`, `ofReal_abs_integral_sub_le_mul_fNorm` |
| p. 395 | Proof: rewrite the supremum over `|g| ≤ V` | In the proof of `lemma_16_1_1` |
| Theorem 16.1.2, (16.12), p. 395 | For a `ψ`-irreducible aperiodic chain with (V4) for a petite `C` and `V` everywhere finite, `Σₙ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞` for some `r > 1`, so `Φ` is `V`-uniformly ergodic | `theorem_16_1_2` (`V ≥ 1` measurable, `ρ < 1`, `b ≠ ∞`; for every invariant probability `μ`); `vErgDist_le_of_driftV4` (`μ(V) < ∞` and `|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ`) |
| p. 396 | Proof: a restatement of Theorem 15.4.1 | `geometric_ergodic_of_driftV4` (carried) in the proof of `vErgDist_le_of_driftV4` |
| p. 396 | `V`-uniformly ergodic chains are `V`-geometrically ergodic | `tsum_fNorm_le_of_tsum_vErgDist` (`Σₙ rⁿ ‖Pⁿ(x, ·) − μ‖_V ≤ S V(x)`) |
| Proposition 16.1.3, p. 396 | If `|||P − 1 ⊗ π|||_V < ∞` and `|||P^{n₀} − 1 ⊗ π|||_V < 1`, then `Σₙ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞` for some `r > 1` | `proposition_16_1_3` (`μ(V) < ∞`, `n₀ ≥ 1`); `vErgDist_le_geometric`, `vErgDist_mul_add_le`, `exists_tsum_mul_pow_ne_top` |
| p. 396 | Proof: `|||P^{n+m} − 1 ⊗ π|||_V ≤ |||Pⁿ − 1 ⊗ π|||_V |||Pᵐ − 1 ⊗ π|||_V` by invariance, then `n = kn₀ + i` | `vOpNorm_comp_le`, `vErgDist_add_le`, `vErgDist_ne_top`; `lintegral_le_fNorm_add` (truncation), `vErgDist_zero_le`, `lintegral_ne_top_of_vErgDist_zero` |
| Theorem 16.1.4, (16.13)–(16.14), p. 396 | For a `ψ`-irreducible chain with `|||Pⁿ − 1 ⊗ π|||_V ≤ R r⁻ⁿ`, (V4) holds for some `V₀` with `c⁻¹V ≤ V₀ ≤ cV` | `theorem_16_1_4` (`V ≥ 1` measurable and finite; `V ≤ V₀ ≤ cV`, a petite set, `ρ < 1`, `b ≠ ∞`) |
| p. 397 | Proof: `Pⁿ(x, C) ≥ π(C) − RρⁿV(x)` for petite `C ∈ B⁺(X)`, so the sublevel sets of `V` are petite by Proposition 5.5.4 (i) | `measure_le_add_fNorm`, `isUnboundedOffPetite_of_tendsto` (`proposition_5_5_4_i`, carried) |
| (16.15), p. 397 | `PⁿV ≤ RρⁿV + π(V)` | `lintegral_pow_le_vErgDist` |
| p. 397 | `V₀ = Σ_{i<n} e^{i/n} PⁱV` satisfies (15.35), so (V4) by Lemma 15.2.8 | In the proof of `theorem_16_1_4`, with weights `sⁱ` for any `s > 1` with `R(s/r)ⁿ ≤ 1`, and `lemma_15_2_8` (carried); see corrections |
| p. 397 | This proves (ii) ⇔ (iv) of Theorem 16.0.1 | `fNorm_le_const_mul`, `vErgDist_le_of_equiv` (`|||Pⁿ − 1 ⊗ μ|||_V ≤ c² |||Pⁿ − 1 ⊗ μ|||_{V₀}`) in the proof of `theorem_16_0_1` |

## §16.1.2 `V`-geometric mixing and `V`-uniform ergodicity

| Source | Claim | Lean |
| --- | --- | --- |
| p. 397 | The limit theorems of Chapter 17 for `V`-uniformly ergodic chains | Not formalised (forward reference) |
| p. 397 | Strong mixing: some `δ(n) → 0` bounds the covariances of `g(X_k)` and `h(X_{n+k})` uniformly in `k` and in `|g|, |h| ≤ 1` | `IsStrongMixing P μ` (the chain started from `μ`) |
| p. 398 | `V`-geometric mixing: the bound `R V(x) ρⁿ` for all `k` and all `g², h² ≤ V` | `IsVGeomMixing` |
| Theorem 16.1.5, p. 398 | A `V`-uniformly ergodic chain has `|E_x[g(Φₖ)h(Φₙ₊ₖ)] − E_x[g(Φₖ)] E_x[h(Φₙ₊ₖ)]| ≤ Rρⁿ[1 + ρᵏV(x)]` for `g², h² ≤ V`, and is `V`-geometrically mixing | `theorem_16_1_5` (`ψ`-irreducible, aperiodic, every distance finite; measurable `g`, `h`), `theorem_16_1_5_mixing` |
| p. 398 | Proof: centre `g` and `h`; pass to `√V` as in Lemma 15.2.9; bound `E_x[V(Φₖ)]` by (15.35) | `exists_vErgDist_sqrt_le` (by `theorem_16_0_1` and `lemma_15_2_9`, carried), `pathKernel_map_pair`, `integral_coord_eq`, `integral_pair_eq`, `rpow_half_mul_self`; the covariance is split without centring both functions (see corrections) |
| (16.16), p. 398 | The centred bound `|E_x[h̄(Φₖ)ḡ(Φₖ₊ₙ)]| ≤ R₁ρⁿ[1 + ρᵏV(x)]` with `h̄ = h − π(h)`, `ḡ = g − π(g)` | Not formalised in this centred form; `theorem_16_1_5` is the uncentred covariance bound |
| p. 398 | Integrating (16.16) over an initial law `μ` with `μ(V) < ∞` gives a mixing condition from `μ` | Not formalised (remark), except for `μ = π` |
| (16.17), p. 398 | `|E_π[h̄(Φₖ)ḡ(Φₖ₊ₙ)]| ≤ R₂ρⁿ`: the stationary version is geometrically mixing | `eq_16_17` (as `|E_π[g(Φₖ)h(Φₖ₊ₙ)] − π(g)π(h)| ≤ Rρⁿ`), `integral_coord_pathMeasure`; `isStrongMixing_of_vUniformlyErgodic` (strong mixing with `δ(n) = Rρⁿ`) |

## §16.1.3 `V`-uniform ergodicity for regenerative models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 399 | Exponential bounds on increments are the key for spatially homogeneous models | Not formalised (informal) |
| (16.18), p. 399 | `G ∈ G⁺(γ)`: `∫ e^{st} G(dt) < ∞` for `0 < s ≤ γ` | `IsLaplaceFinite Γ γ`; `integrable_exp_mul_of_le` |
| p. 399 | The forward recurrence time `δ`-skeleton `V⁺_δ` of (RT3) with spread-out `Γ ∈ G⁺(γ)`: `V(x) = e^{γx}` gives (V4) on `C = [0, δ]`, and `PV(x)/V(x) = e^{−γδ}` for `x > δ` | `fwdChain_driftV4` (on the restarted chain `fwdChain Γ δ`, carried, with `V(x) = e^{γx⁺}`, `fwdExpV`, and `C = (−∞, δ]`); `measurable_fwdExpV`, `one_le_fwdExpV`, `fwdExpV_ne_top`, `ofReal_exp_fwdTimeCts_le`, `lintegral_exp_fwdSkelKernel_le`, `fwdChain_isPetite_Iic`; see corrections |
| p. 399 | The chain is `e^{γx}`-uniformly ergodic, and `∫ |Pⁿ(x, dy) e^{γy} − π(dy) e^{γy}| < e^{γx} r⁻ⁿ`: the moment generating function and all polynomial moments converge geometrically | `fwdChain_vUniformlyErgodic` (for small `δ`; positive and aperiodic; `‖Pⁿ(x, ·) − π‖_V ≤ R r⁻ⁿ V(x)` with a constant `R`), `fwd_moments_ne_top`; see corrections |
| p. 399 | The same result as §15.1.4, by drift conditions instead of hitting times | Not formalised (remark) |
| p. 399 | `Γ ∈ G⁺(γ)` is also necessary for geometric ergodicity | Not formalised |
| p. 399 | Uniform ergodicity holds only if `Γ` has bounded range, `Γ[0, c] = 1`, and then the state space may be taken to be `[0, c]` | The "only if": `fwdChain_unbounded_not_uniformlyErgodic` (no restriction to an absorbing set that carries the stationary law is uniformly ergodic when `Γ(c, ∞) > 0` for every `c`), `fwdSkelInv_Ioi_pos`, `exists_mem_gt_of_unbounded` (`fwdSkelInv`, carried); also `fwdChain_not_uniformlyErgodic`, `restrict_fwdChain_not_uniformlyErgodic`, `fwdSkelKernel_pow_of_lt`, `half_le_tvNorm_dirac`, `exists_le_half_of_ne`. The converse, uniform ergodicity on `[0, c]` for bounded range: not formalised |
| p. 399 | Compact absorbing sets are typical of uniformly ergodic chains | Not formalised (informal) |
| pp. 399–400 | Random walk on `[0, ∞)` (RWHL1) with (a) mean increment `β < 0` and (b) `Γ ∈ G⁺(γ)` | `halfLineWalkKernel Γ` (carried); the hypotheses of `halfLine_vUniformlyErgodic` |
| (16.19), p. 400 | For `V(x) = e^{sx}`, `∫ P(x, dy) ΔV(y)/V(x)` is at most `∫ Γ(dw)[e^{sw} − 1] + ∫_{(−∞, −x]} Γ(dw)[1 − e^{sw}]` | `lintegral_halfLine_exp_le` (`PV(x) ≤ e^{sx} (∫ e^{sw} Γ(dw) + Γ(−∞, −x])`) |
| p. 400 | `s⁻¹ ∫ Γ(dw)[e^{sw} − 1] → β` as `s ↓ 0`; choose `s₀` and `c`; (V4) with `C = [0, c]`, which is petite; the walk is `e^{s₀x}`-uniformly ergodic | `exists_mgf_lt_one`, `halfLine_driftV4_exp`, `halfLine_vUniformlyErgodic` (`ψ`-irreducible, aperiodic, positive; for every invariant probability; `halfLine_isPetite_Iic`, carried) |
| p. 400 | All moments converge geometrically; the Bernoulli walk of §15.5 behaves so because its increments are bounded; Section 16.3 generalises | Not formalised (informal); the moment bounds follow from `tsum_fNorm_le_of_tsum_vErgDist` |

## §16.2.1 Equivalent conditions for uniform ergodicity

| Source | Claim | Lean |
| --- | --- | --- |
| p. 400 | Uniform ergodicity is `|||Pⁿ − 1 ⊗ π|||_V → 0` for `V ≡ 1` | `isUniformlyErgodic_iff`, `vErgDist_one_eq` |
| Theorem 16.2.1, pp. 400–401 | With no irreducibility or aperiodicity: (i) uniform ergodicity, (ii) `‖Pⁿ(x, ·) − π‖ ≤ Rρⁿ`, (iii) `sup_x ‖Pⁿ(x, ·) − π‖ < 1` for some `n`, are equivalent | `theorem_16_2_1` (for an invariant probability `μ`); `vErgDist_one_le_two`, `vErgDist_one_succ_le` (`proposition_13_3_2`, carried) |
| p. 401 | Proof: (iii) ⇒ (ii) by Proposition 16.1.3 | `proposition_16_1_3` in the proof of `theorem_16_2_1` |
| p. 401 | A uniformly ergodic chain is `π`-irreducible and aperiodic | `isPhiIrreducible_of_isUniformlyErgodic`, `isAperiodic_of_isUniformlyErgodic` (for a `ψ`-irreducible chain), `isAperiodic_of_isSmallSet_univ` |
| Theorem 16.2.2, p. 401 | For a `ψ`-irreducible aperiodic chain: (i) uniform ergodicity; (ii) `X` petite; (iii) a petite `C` with `sup_x E_x[τ_C] < ∞`, and then `sup_x E_x[τ_A] < ∞` for `A ∈ B⁺(X)`; (iv) the same with `E_x[κ^{τ_C}]`; (v) a bounded solution of (16.10) for a petite set | `theorem_16_2_2` (a `List.TFAE`, Mathlib; in (v) `V ≥ 1`), `theorem_16_2_2_hitting` (the "in which case" parts) |
| p. 401 | Proof: (iii) ⇔ (v) by Theorem 11.3.11; (iv) ⇒ (iii); (v) ⇒ (iv) by Theorem 15.2.6; (i) ⇒ (ii) through a small set and Theorem 5.2.4; (ii) ⇒ (v) with `V ≡ 1`; (v) ⇒ (i) by Theorem 16.1.2 | `driftV4_of_driftV2_bounded`, `meanReturnTime_le_kendallMoment`, `sub_one_mul_le_pow`, `theorem_15_2_6` (carried), `isSmallSet_univ_of_isUniformlyErgodic` (`proposition_5_2_4_i`, carried), `firstReturn_univ`, `meanReturnTime_univ`, `kendallMoment_univ`, `isUniformlyErgodic_of_bounded_driftV4` |
| p. 402 | Doeblin's condition: a probability `φ`, `m`, `ε < 1`, `δ > 0` with `Pᵐ(x, A) ≥ δ` for all `x` when `φ(A) > ε` | `IsDoeblin P` |
| Theorem 16.2.3, p. 402 | An aperiodic `ψ`-irreducible chain satisfies Doeblin's condition iff it is uniformly ergodic | `theorem_16_2_3` |
| p. 402 | Proof: `V = 1 + 1_{Cᶜ}` is a bounded solution of (16.10) for the `m`-skeleton; conversely `φ = π` | Replaced: Doeblin's condition makes `X` petite (see corrections); the converse with `φ = μ` |
| Theorem 16.2.4, (16.20)–(16.21), p. 402 | If `Pᵐ(x, A) ≥ νₘ(A)` for all `x`, `A`, then `‖Pⁿ(x, ·) − π‖ ≤ 2ρ^{n/m}` with `ρ = 1 − νₘ(X)` | False with the real exponent: `theorem_16_2_4_counterexample` (`climbStep`, `climbKernel`). Corrected: `theorem_16_2_4` (`2ρ^{⌊n/m⌋}`, every invariant probability, `ν` finite) |
| (16.22)–(16.23), p. 403 | Proof by coupling: with probability `1 − ρ` both copies move by `ν` and couple, so `‖Pⁿ(x, ·) − π‖ ≤ 2P(T > n) ≤ 2ρⁿ`; for `m > 1` the contraction property | Replaced by the analytic form `tvNorm_comp_le_of_le` (`‖λQ − λ'Q‖ ≤ (1 − ν(X)) ‖λ − λ'‖` if `Q(x, ·) ≥ ν`) and `tvNorm_pow_mul_comp_le` |
| p. 403 | The minorization gives the exact rate, which makes it the most useful condition | Not formalised (informal) |
| p. 403 | The forward recurrence time chain is not uniformly ergodic, by Theorem 16.2.2 (iii), unless the space reduces to a compact set | `fwdChain_not_uniformlyErgodic`, `restrict_fwdChain_not_uniformlyErgodic` (by a direct argument; see corrections) |
| p. 403 | Random walk on `[0, ∞)` has `E_x[τ₀] ∼ cx` [69], so it is never uniformly ergodic | Not formalised (quoted from [69]) |

## §16.2.2 Geometric convergence of given moments

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 403–404 | Uniform ergodicity need not give geometric convergence of unbounded functionals; an i.i.d. sequence is uniformly ergodic whatever its moments | `isUniformlyErgodic_const` |
| (16.24), pp. 404–405 | The ladder chain on `ℤ₊ × ℤ₊`: the whole space is small, so it is uniformly ergodic; with `f(i, k) = k` and suitable `α_{ij}` it is `f`-ergodic but `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f = ∞` for every `r > 1` | The ladder chain is not formalised. The claim is proved for another chain, `resetKernel` (`resetMatrix`, `isTransitionMatrix_resetMatrix`, `isMarkovKernel_resetKernel`, `resetPi`, `resetPi_singleton`, `resetPi_tsum`, `isProbabilityMeasure_resetPi`, `isInvariant_resetPi`, `resetKernel_isSmallSet`, `reset_uniformlyErgodic`, `resetF`, `resetF_eq_ofReal`, `lintegral_resetF_ne_top`, `resetKernel_pow_ge`, `fNorm_reset_ge`, `reset_not_fGeometric`); see corrections |
| p. 406 | Unbounded functions need criteria such as (V4) | Not formalised (informal) |

## §16.2.3 Uniform ergodicity: T-chains on compact spaces

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 16.2.5, p. 406 | A `ψ`-irreducible aperiodic T-chain on a compact space is uniformly ergodic | `theorem_16_2_5` (`CompactSpace X`, Mathlib; `IsTChain`, carried) |
| p. 406 | Proof: `X` is petite by Theorem 6.0.1, then Theorem 16.2.2 | `theorem_6_2_5_ii` (carried), `theorem_16_2_2` |
| p. 406 | Lagrange stability: `A₊(x)` is compact for every `x` | The hypothesis `∀ x, IsCompact (closure (reach F (controlSet γ) x))` of `lemma_16_2_6` and `theorem_16_2_7` (`reach`, `controlSet`, carried) |
| p. 406 | In applications the inputs lie in a bounded set; no condition on the inputs is made | Not formalised (informal) |
| Lemma 16.2.6, p. 406 | For NSS(F) under (NSS1)–(NSS3) with CM(F) forward accessible, Lagrange stable, M-irreducible and aperiodic, each `A₊(x)` is closed, absorbing and small | `lemma_16_2_6` (`IsLSCDensity`, `RankCondition`, `IsMIrreducible`, a minimal set of period one, `IsPeriodOf`, carried); `isAbsorbing_closure_reach` (`proposition_7_2_2_i`, carried) |
| p. 407 | Proof: compact invariant sets are small by Theorem 7.3.5 (ii) | `theorem_7_3_5_ii` (carried), `isSmall_of_isCompact_tChain` (`theorem_6_2_5_ii`, `theorem_5_5_7`, carried) |
| Theorem 16.2.7, p. 407 | Under the same conditions there is a unique invariant probability `π`, the chain restricted to `A₊(x)` is uniformly ergodic, and `E_y[f(Φₖ)] → ∫ f dπ` geometrically for `f` bounded on compact sets | `theorem_16_2_7` (`NSSUniformErgodic`; `|E_y[f(Φₙ)] − ∫ f dπ| ≤ Rρ^{⌊n/m⌋}`); `theorem_16_2_7_restrict` (`UniformModels`, for a T-chain and a compact absorbing set); `eq_of_isInvariant_of_isPositive`, `isInvariant_map_val`, `map_val_restrictKernel_pow` |
| p. 407 | Proof: Theorem 7.3.5, Lemma 16.2.6 and Theorem 16.0.2 | `theorem_7_3_5_ii` (carried), `lemma_16_2_6`, `theorem_16_2_7_restrict` |

## §16.3.1 Strengthening ergodicity to geometric ergodicity

| Source | Claim | Lean |
| --- | --- | --- |
| p. 407 | An increment method for (V4), as for the random walk of §16.1.3 and in §9.5.1 | Not formalised (informal) |
| (16.25), p. 407 | Foster's form: `V` finite, `PV ≤ V − 1` on `Cᶜ` and `PV ≤ b` on `C`, for a petite `C` | The hypotheses of `theorem_16_3_1` (`V : X → ℝ`, `V ≥ 0`, `P(x, ·)`-integrable) |
| p. 407 | `V_C(x) = E_x[σ_C]` is the minimal solution of (16.25) (Theorem 11.3.5) | `theorem_11_3_5_i` (carried); not used in Chapter 16 |
| Theorem 16.3.1, (16.26)–(16.27), pp. 407–408 | For a `ψ`-irreducible ergodic chain with (16.25), uniformly bounded exponential moments of the right increments (16.26) and second moments of the left increments (16.27), `Φ` is `V*`-uniformly ergodic for `V* = e^{δV}`, `δ < β` | `theorem_16_3_1` (aperiodic; positivity and `Σ rⁿ |||Pⁿ − 1 ⊗ μ|||_{V*} < ∞` for every invariant probability); see corrections |
| (16.28), p. 408 | A second-order Taylor expansion of `e^{δ(V(y) − V(x))}` | Replaced by `exp_le_one_add_add_sq` (`eᵗ ≤ 1 + t + t² e^{max(t, 0)}`), `exp_sub_one_sub_le` |
| (16.29), p. 408 | Off `C`, (16.26) and (16.27) bound the right side of (16.28) by a constant below `1` for small `δ`, so (V4) holds for `V*` | `exp_mul_le_increment`, `sq_le_exp_mul`; `increment_driftV4` ((V4) for `V*` with the petite set `C ∩ {V < b + 1}`) |
| p. 408 | For the random walk `V(x) = x`, (16.26) is `Γ ∈ G⁺(γ)` and (16.27) is not needed | Not formalised as such; the walk is treated directly (`halfLine_vUniformlyErgodic`) |
| p. 408 | Geometric tails may be necessary (forward recurrence time chain) but are not always (i.i.d. processes) | `isUniformlyErgodic_const`; the necessity for the forward recurrence time chain is not formalised |
| (16.30), p. 409 | `P(0, i) = αᵢ`, `P(i, i − 1) = γᵢ`, `P(i, i + n) = (1 − γᵢ)(1 − βᵢ)βᵢⁿ` | `upDownMatrix`, `upDownKernel`, `upDownMatrix_up`, `upDownMatrix_low`, `upDownMatrix_down`, `isTransitionMatrix_upDownMatrix`, `isMarkovKernel_upDownKernel`, `upDown_isIrreducibleChain` (`αⱼ > 0` for `j ≥ 1`, `γᵢ > 0`) |
| p. 409 | With `Σ iαᵢ < ∞` and `(1 − γᵢ)βᵢ/(1 − βᵢ) − γᵢ ≤ −ε`, `V(x) = x` satisfies (V2) | `upDown_drift` (`PV(i) + γᵢ = i + (1 − γᵢ)βᵢ/(1 − βᵢ)`), `upDown_driftV2` (off `{0}`), `tsum_nat_mul_pow_of_lt_one`; the ergodicity of the chain is not stated separately |
| p. 409 | If `βⱼ → 1`, `Pⱼ(τ₀ > n) ≥ (1 − γⱼ)(1 − βⱼ)βⱼⁿ`, and the chain is not geometrically ergodic | `upDown_kendallMoment_ge`, `upDown_kendallMoment_eq_top` (`E_0[r^{τ_0}] = ∞` for every `r > 1`), `upDown_not_geomErgodic` (through `theorem_15_1_5`, carried); `upDown_pow_low`, `upDown_pow_apply_eq_zero` |
| p. 409 | The left increments have bounded variances and the right ones exponential tails; (16.26) fails for lack of uniformity | `upDown_left_increments` ((16.27) with `d = 1`), `upDown_right_increments_unbounded` |
| p. 409 | For the chain (15.20), `V₀(j) = E_j[σ₀] = (1 − βⱼ)⁻¹` has bounded right increments, but `Σⱼ P(i, j)(V₀(j) − V₀(i))² = (1 − βᵢ)⁻¹ → ∞`, so (16.27) is needed | `nonGeomV₀`, `nonGeomV₀_eq_meanHitTime`, `one_le_nonGeomV₀`, `nonGeom_setIntegral`, `nonGeom_right_increments`, `nonGeom_left_increments`, `nonGeom_left_increments_unbounded`; `nonGeomKernel`, `nonGeom_not_geomErgodic` (carried) |

## §16.3.2 Geometric ergodicity and the structure of `π`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 410 | `A_{g,n}(x) = {y : g(y) ≤ g(x) − n}`; `g`-skip-free to the left (16.31): `P(x, A_{g,k}(x)) = 0` | The hypothesis of `theorem_16_3_2_skipFree`; `pow_skipFree` (`Pʲ(x, A_{g,jk}(x)) = 0`) |
| p. 410 | Skip-freeness precludes Doeblin's condition when `g` is unbounded off petite sets | Not formalised (remark) |
| Theorem 16.3.2, (16.32), p. 410 | A geometrically ergodic chain has `∫ π(dy) e^{βV_C(y)} < ∞`, `V_C(y) = E_y[σ_C]`, for petite `C ∈ B⁺(X)` | `theorem_16_3_2` ((V4) for a petite set; every `B ∈ B⁺(X)`, every invariant probability; `V_B` finite `π`-a.e.) |
| Theorem 16.3.2, (16.33), p. 410 | If the chain is `g`-skip-free to the left for `g` unbounded off petite sets, `∫ π(dy) e^{β'g(y)} < ∞` | `theorem_16_3_2_skipFree` (`k ≥ 1`; no condition on `g`) |
| (16.34), p. 410 | Proof: `G_C^{(r)}(·, X)` solves (V4), so `∞ > π(V) ≥ ∫ π(dy) E_y[r^{σ_C}]`; Jensen's inequality | `exists_lintegral_tpow_firstHit_le` (through `theorem_15_3_3`, carried), `ofReal_exp_meanHitTime_le`, `firstHit_le_firstReturn`, `toENNReal_le_tpow` |
| p. 410 | Proof of (16.33): for `g(x) ≥ nk + b`, `P_x(σ_C ≤ n) = 0` | `pow_skipFree` in the proof of `theorem_16_3_2_skipFree` |
| pp. 410–411 | Geometric tails of `π` in the scaling `V_C`; skip-free queueing models; an i.i.d. chain is uniformly ergodic whatever `π`; for the chain (15.20), `π(j) ∝ γⱼ(1 − βⱼ)⁻¹`, so the tails of `π` may be geometric or not | Not formalised (remarks), apart from `isUniformlyErgodic_const` |

## §16.4 Models from queueing theory

| Source | Claim | Lean |
| --- | --- | --- |
| p. 411 | For the three models, the minimal solution of (16.25) is comparable to `|i|₁`, and the chain is `e^{δV}`-uniformly ergodic | Not formalised as stated: linear test functions are used directly (`theorem_16_4_1`, `theorem_16_4_2`, `theorem_16_4_3`) |
| Theorem 16.4.1, p. 411 | If the embedded M/G/1 chain (Q4) is ergodic, it is geometrically ergodic when the service time law is in `G⁺(γ)` | `theorem_16_4_1` (`λ > 0`, `H` not concentrated at `0`, ergodicity as `Σₖ k qₖ < 1`; `e^{δi}`-uniform ergodicity; `mG1Matrix`, `poissonWeight`, `mG1_poisson_isIrreducibleChain`, carried); `mG1_lintegral_succ`, `mG1_lintegral_zero` |
| p. 412 | Proof: `V(i) = i` solves (16.25) with `C = {0}` (§11.4); (16.27) holds trivially; `Σ_l e^{δ(l+1)} P(k, k + l) ≤ ∫ exp{(e^δ − 1)λt} dH(t)` | `tsum_exp_mul_poissonWeight` (an equality); then (V4) for `e^{δi}` with `C = {0}` directly, through `exists_mgf_lt_one`; see corrections |
| §16.4.2, p. 412 | The gated-limited polling system: `K` queues, one server, `min(x, ℓₖ)` customers served at queue `k`, Poisson arrivals, i.i.d. service times, observed at returns to queue `1` | `pollKernel` (one cycle), `pollTail`, `visitAt`, `visitAt_eq`, `visitKernel`, `visitMeasure`, `served`, `afterServe`, `sumLaw`, `arrLaw`; `isMarkovKernel_visitKernel`, `isMarkovKernel_pollTail`, `isMarkovKernel_pollKernel`, `measurable_finSum`, `isProbabilityMeasure_sumLaw`, `lintegral_exp_sumLaw`, `lintegral_id_sumLaw`, `isProbabilityMeasure_arrLaw`, `arrLaw_singleton`, `measurable_arrLaw`, `measurable_arrLaw_map`, `lintegral_prod_arrLaw`, `lintegral_sum_arrLaw`, `lintegral_visit`, `isProbabilityMeasure_visit`, `visit_ge`, `visit_afterServe_pos`, `lintegral_pollTail_succ`; `lintegral_poissonMeasure`, `lintegral_id_poissonMeasure`, `lintegral_exp_poissonMeasure`, `poissonMeasure_zero_pos`; see corrections |
| Theorem 16.4.2, (16.35), p. 412 | The polling model is geometrically ergodic if `ρ = Σₖ λₖ/μₖ < 1` and the service time laws are in `G⁺(γ)` | `theorem_16_4_2` (`ℓₖ ≥ 1`, positive mean service times; positive, aperiodic and `e^{δV}`-uniformly ergodic for every invariant probability) |
| pp. 412–413 | Proof: `V(i) = Σₖ iₖ/μₖ` satisfies (16.25); there are finitely many kinds of increments, and the exponential and quadratic sums are finite by the Laplace–Stieltjes transforms | `pollV`, `pollV_add`, `pollV_afterServe`, `pollV_nonneg`, `lintegral_visit_V`, `fullAfter`, `pollTail_drift` (the drift, for a scaled `V`); `lintegral_visit_exp`, `lintegral_visit_exp_neg`, `pollTail_exp` (the increment conditions); `drainAfter`, `pollTail_drain_pos`, `poll_pow_succ_ge`, `pollKernel_reach_zero` (irreducibility), `poll_integral_le` |
| p. 413 | Once ergodicity is known, `V_C(x) = E_x[σ_C]` is a finite solution of (16.25) by minimality | Not formalised (remark) |
| §16.4.3, p. 413 | The M/PH/1 queue: Poisson(`λ`) arrivals, `k` exponential phases with probability `p_k`; the state `(i₁, i₂)`: waiting jobs and remaining phases | `phSpace` (`i₂ = 0 → i₁ = 0`), `mem_phSpace_succ`, `zero_mem_phSpace`, `phZero`, `phStart`, `phMean`, `phSpace_cases` |
| p. 413 | The `h`-approximation for `h < (λ + ν)⁻¹`, with its transition probabilities | `phMeasure`, `phKernel` (corrected transitions; `a = λh`, `b = νh`), `lintegral_phStart`, `lintegral_phKernel_zero`, `lintegral_phKernel_one`, `lintegral_phKernel_succ_one`, `lintegral_phKernel_two`, `ph_coeff_sum`, `isMarkovKernel_phKernel`; see corrections |
| (16.36)–(16.37), pp. 413–414 | `V₀(i) = E_i[σ₀]` satisfies `V₀(i + e₂) − V₀(i) = c` and `V₀(i + e₁) − V₀(i) = c̄ = c Σ l p_l`, so `V₀` is linear | Not formalised as stated (the identification with `E_i[σ₀]`). The linear `V(i) = w(m i₁ + i₂)` is shown to satisfy (16.25) with equality: `phV`, `phV_nonneg`, `phKernel_drift_zero`, `phKernel_drift` (`PV = V − 1` off `0`), `ph_coe_mul_ofReal`, `ph_tsum_linear`, `ph_three`, `ph_coeff_real` |
| Theorem 16.4.3, p. 414 | The `h`-approximation is geometrically ergodic whenever it is ergodic, if the phase distribution is in `G⁺(γ)`; with finitely many phases ergodicity is equivalent to geometric ergodicity | `theorem_16_4_3` (ergodicity as `λm < ν`; positive, aperiodic, `e^{δV}`-uniformly ergodic for every invariant probability), `theorem_16_4_3_finite`, `ph_finite_laplace` |
| p. 414 | Proof: a coupling with two uniform sequences gives (16.36)–(16.37), hence (16.26) | Replaced: `phKernel_exp_le` ((16.26)), `phKernel_sq_le` ((16.27)), `ph_three_le`, `ph_two_le`, `ph_tsum_le`, `ph_integral_le`; `ph_pow_succ_ge`, `phKernel_reach_zero`, `phKernel_isPhiIrreducible` |

## §16.5 Autoregressive and state space models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 414 | Autoregressive models can be geometrically ergodic without `G⁺(γ)` innovations | Not formalised (informal) |
| (16.38), p. 414 | `Φₖ₊₁ = (A + Γₖ₊₁)Φₖ + Wₖ₊₁` | `rcaKernel`, `rcaStep` (carried; `W` in `ℝⁿ`) |
| (16.39), p. 415 | `vec(ABC) = (Cᵀ ⊗ A) vec(B)` and `(A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ` | Not formalised; the proof works with quadratic forms (`quadForm`) |
| (RCA1)–(RCA3), p. 415 | `Γ`, `W` i.i.d. and independent; `E[W] = 0`, `E[WWᵀ] = G`, `E[Γ] = 0`, `E[Γ ⊗ Γ] = C`, eigenvalues of `A ⊗ A + C` inside the unit disc; an everywhere positive density | (RCA1): the product law in `rcaKernel` (carried). (RCA2): only `E[W] = 0` and the integrability of `WWᵀ` are hypotheses of `theorem_16_5_1`; the rest enters through (16.40)–(16.41). (RCA3): not used |
| Theorem 16.5.1, p. 415 | Under (RCA1)–(RCA3), `Φ` is `V`-uniformly ergodic for `V(x) = |x|²`, so a second-order stationary version exists | `theorem_16_5_1` (positive; every invariant probability has `∫ |x|² dμ < ∞`; `|||Pᵏ − 1 ⊗ μ|||_V ≤ R r⁻ᵏ` for `V(x) = |x|² + 1`); see corrections |
| p. 415 | Proof: the chain is weak Feller, a `ψ`-irreducible T-chain with petite compact sets (Theorem 6.2.9), aperiodic by (RCA3) | Not formalised: `ψ`-irreducibility, aperiodicity and the petiteness of compact sets are hypotheses of `theorem_16_5_1` |
| (16.40)–(16.41), p. 415 | From [299]: `M` defined by `vec(M) = (I − A ⊗ A − C)⁻¹ vec(N)` is positive definite, and `E[Φₖᵀ(A + Γ)ᵀM(A + Γ)Φₖ | Φₖ = x] = xᵀMx − xᵀNx` | Not formalised (quoted from [299]); `M`, `N` positive definite with (16.41) are hypotheses of `theorem_16_5_1` |
| (16.42), p. 416 | `E[V(Φₖ₊₁) | Φₖ = x] = E[xᵀ(A + Γ)ᵀM(A + Γ)x] + E[WᵀMW]` | `rca_lintegral_quadForm`; `quadForm`, `integrable_quadForm`, `quadForm_add`, `dotProduct_mulVec_comm_of_symm` |
| (16.43), p. 416 | `PV = V − xᵀNx + tr(VG) < λV + L`, so (V4) by Lemma 15.2.8; `c⁻¹|x|² ≤ V ≤ c|x|²` | In the proof of `theorem_16_5_1`: `lemma_15_2_8` (carried), `exists_quadForm_bounds`, `continuous_quadForm`, `quadForm_smul`, `quadForm_nonneg`, `quadForm_add_le`, `isCompact_dotProduct_le`, `dotProduct_self_nonneg'` |
| p. 416 | The SAC model (SAC1)–(SAC2) with state (2.25); tightness from Proposition 12.5.2 | `sacKernel`, `sacGaussianKernel` (carried); `sacSet`, `measurableSet_sacSet`, `isAbsorbing_sacSet`, `isMarkovKernel_sacRestrict`; `sacSpace` (carried), `sacQ`, `isMarkovKernel_sacQ`, `sacSpace_eq_sacSet` |
| (16.44), p. 416 | `V(y, θ̃, Σ) = θ̃⁴ + ε₀θ̃²y² + ε₀²y²` | `sacV`, `sacV_nonneg`, `isCompact_sacV_le` |
| (16.45), p. 416 | `Py² = θ̃²y² + σ_w²` | In the proof of `sac_drift`; `lintegral_sacGaussian_Ysq`, `lintegral_sq_add_noise` (Gaussian) |
| (16.46)–(16.47), p. 417 | `Pθ̃²y² ≤ σ_z²θ̃²y² + K₁(θ̃⁴ + θ̃² + 1)` and `Pθ̃⁴ ≤ α⁴θ̃⁴ + K₂(θ̃² + 1)`; for `ρ > max(σ_z², α⁴)`, `PV ≤ ρV + R` | `sac_drift` (the combined bound); `sac_theta_eq`, `sac_uv_bounds`, `sac_coeffs`, `sq_add_le_young`, `pow_four_add_le_young` |
| Proposition 16.5.2, (16.48), p. 417 | For `σ_z² < 1`, `Φ` is `V`-uniformly ergodic for (16.44), and `E_x[Y_k²] → ∫ y² dπ` geometrically | `proposition_16_5_2` (general disturbances; irreducibility, aperiodicity and petite compact sets as hypotheses; `V = sacV ε₀ + 1`), `proposition_16_5_2_gaussian` (Gaussian (SAC2); the hypotheses derived through `proposition_7_4_3`, carried; `α ≠ 0`), `proposition_16_5_2_of_eq`, `sacGaussian_moments`; see corrections |
| p. 417 | The performance is characterised by the unique invariant probability | Not stated separately; positivity is part of `proposition_16_5_2_gaussian` |
| p. 417 | In steady state `θ̃ₖ = θₖ − E[θₖ | Y₀, …, Yₖ]` and `Σₖ = E[θ̃ₖ² | Y₀, …, Yₖ]` | `isKalmanLaw_of_isInvariant` (every invariant probability is a Kalman law; `IsKalmanLaw`, `sacKalmanInit`, carried), `isKalmanLaw_of_tendsto`, `ofReal_tvNorm_pow_comp_le`, `lintegral_map_val_of_isInvariant`, `map_val_restrictKernel_pow_comp`, `measurable_sacV_add_one` |
| p. 417 | Expectations of (2.23)–(2.24) under `P_π`: `E_π[Y₀²] = E_π[Σ₀Y₀²] + σ_w²` and `σ_z² E_π[Y₀²] = E_π[Σ₀Y₀²] − α²σ_w² E_π[Σ₀]` | `sac_steady_state_identities` (with `E_π[θ̃²] = E_π[Σ]`), `lintegral_sacGaussian_SYsq`; as hypotheses in `eq_16_49` |
| (16.49), p. 417 | `E_π[Y₀²] = σ_w²/(1 − σ_z²) (1 + α² E_π[|θ̃₀|²])` | `eq_16_49` (from the two identities), `eq_16_49_gaussian` (for every invariant probability of the Gaussian chain) |
| p. 417 | `σ_w²/(1 − σ_z²) (1 + α²σ_z²) ≤ E_π[Y₀²] ≤ σ_w²/(1 − σ_z²) (1 + α²σ_z²/(1 − α²))` | `sac_performance_bounds`, `eq_16_49_gaussian` |
| p. 417 | With `θₖ₋₁` observed the optimal performance would be `σ_w²/(1 − σ_z²)`, so the lower bound is non-trivial | Not formalised (remark) |
| Figure 16.1, p. 418 | A simulation of the model with `Uₖ = 0` | Not formalised (simulation) |

## §16.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 418–420 | History: Markov, Doeblin, Doob, Yosida and Kakutani, Huang and Isaacson, Bonsdorff, Isaacson and Tweedie, Nummelin; quasi-compact operators and Revuz; the decomposition of Tuominen and Tweedie for reducible T-chains on compact spaces; Kartashov, Hordijk and Spieksma; mixing; Rosenthal's coupling proof; Vere-Jones, Miller, Spieksma and Tweedie; the polling, phase-type, RCA and adaptive models; the second-edition commentary | Not formalised (commentary) |
| (16.50), p. 420 | Increments of bounded range, `|V(j) − V(k)| ≥ b ⇒ P(k, j) = 0`, make an ergodic chain geometrically ergodic [243] | `theorem_16_3_1_bounded_range` (`|V(Φ₁) − V(x)| < B` a.s. gives (16.26)–(16.27), then Theorem 16.3.1) |
