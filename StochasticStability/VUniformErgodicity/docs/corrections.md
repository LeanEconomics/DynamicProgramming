# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. One of the claims below is
false as printed. It is refuted in Lean by a counterexample of this project, and a corrected
statement is proved. The other corrections concern a model description (the transition
probabilities of the M/PH/1 queue), a step of a proof, the scaling of test functions and weights,
and a missing constant; the table says why no counterexample is given for them. The book's
statements are paraphrased. The last section lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 16.0.1, p. 393 | For a `ψ`-irreducible aperiodic chain and `V ≥ 1`, (i) `V`-uniform ergodicity, `|||Pⁿ − 1 ⊗ π|||_V → 0`, is equivalent to (ii) the geometric bound (16.3), (iii) the condition (16.4) and (iv) (V4) for an equivalent `V₀` (16.5). | (i) as printed does not imply (ii)–(iv): finitely many of the distances may be infinite. `theorem_16_0_1_counterexample` is the deterministic chain `twoStepKernel` on `ℕ` (`0 ↦ 0`, odd `k ↦ k + 1`, even `k ≥ 2 ↦ 0`) with `V(k) = 1` for odd `k` and `V(k) = k + 1` otherwise (`twoStepWeight`). It is `ψ`-irreducible and aperiodic, `δ₀` is invariant (`isInvariant_twoStepKernel`), and `Pⁿ = 1 ⊗ δ₀` for `n ≥ 2` (`twoStepKernel_pow_add_two`), so the distances vanish from `n = 2` on (`twoStep_vErgDist_add_two`) and (i) holds. But from an odd state `k` the chain jumps to `k + 1`, where `V = k + 2`, while `V(k) = 1`; so `|||P − 1 ⊗ δ₀|||_V = ∞` (`twoStep_vErgDist_one`) and no bound (16.3) holds. The book's proof of (i) ⇒ (iii) goes through Proposition 16.1.3, which needs `|||P − 1 ⊗ π|||_V < ∞`. The equivalence is proved with (i) read as "`V`-uniformly ergodic, with every `|||Pⁿ − 1 ⊗ π|||_V` finite" (`theorem_16_0_1`). Theorem 16.1.5 and (16.17) are proved under this reading of `V`-uniform ergodicity. |
| The `h`-approximation of the M/PH/1 queue, p. 413 | The transition probabilities: `P(0, 0 + e₂) = λp_l h`; `P(i, i + e₁) = λh` for `i₁, i₂ > 0`; `P(i, i − e₂) = νh` for `i₁ > 0`, `i₂ > 1`; `P(i, i − e₁ + l e₂) = νp_l h` for `i₁ > 0`, `i₂ = 1`; the rest of the mass stays at `i`. | The printed list does not describe the M/PH/1 queue of the text (a job needs `l` phases with probability `p_l`; `i₁` jobs wait and the job in service has `i₂` phases left). Four corrections are made in `phMeasure` and `phKernel`. (1) An arrival to the empty queue starts a job with `l` phases: `0 → 0 + l e₂` with probability `λp_l h` (printed `0 + e₂`). (2) When the job in service completes its last phase, the next job starts with `l` phases, so `i₂` becomes `l`: `i → i − e₁ + (l − 1)e₂` (printed `i − e₁ + l e₂`, which gives `l + 1` phases). (3) Arrivals and phase completions occur whenever the server is busy, `i₂ > 0` (printed `i₁ > 0`); with the printed conditions every state `(0, i₂)`, `i₂ ≥ 1`, would be absorbing. (4) The transition `(0, 1) → 0`, the completion of the only job, is missing. The one-step integrals of the corrected chain are `lintegral_phKernel_zero`, `lintegral_phKernel_one` (from `(0, 1)`, with the move to `0`), `lintegral_phKernel_succ_one` and `lintegral_phKernel_two`. This corrects a model description, not a theorem, so there is no counterexample; Theorem 16.4.3 is proved for the corrected chain (`theorem_16_4_3`). |
| Theorem 16.3.1, proof, p. 408 | (16.25)–(16.27) give (V4) for `V* = e^{δV}` with the petite set `C` of (16.25). | (V4) needs a finite constant `b`, so `V*` must be bounded on the set; `V` is finite but may be unbounded on `C`. Since `PV ≤ b` on `C`, the points of `C` with `V ≥ b + 1` have `PV ≤ V − 1` and satisfy the bound used on `Cᶜ`. So (V4) holds with the petite set `C ∩ {V < b + 1}`, on which `V*` is bounded (`increment_driftV4`). The theorem is unchanged (`theorem_16_3_1`); this corrects a step of the proof, so there is no counterexample. |
| Theorems 16.4.1 and 16.4.2, proofs, p. 412 | `V(i) = i` solves (16.25) for the M/G/1 chain with `C = {0}`; `V(i) = Σₖ iₖ/μₖ` solves (16.25) for the polling system. | Both functions have a negative drift, but not of size `1`. For the M/G/1 chain `PV(i) = V(i) − (1 − Σₖ k qₖ)` for `i ≥ 1` (`mG1_lintegral_succ`), so `V(i) = i/(1 − Σₖ k qₖ)` solves (16.25). For the polling system a cycle lowers the mean of `V` by `(1 − ρ) Σₖ sₖ/μₖ`, `sₖ` the number served at queue `k` (`lintegral_visit_V`), so `V` is divided by `d = (1 − ρ) minₖ ℓₖ/μₖ`, and the drift `−1` holds once some queue holds at least its gate limit (`pollTail_drift`, `theorem_16_4_2`). The theorems are unchanged, so there is no counterexample. |
| Theorem 16.5.1, p. 415; Proposition 16.5.2, (16.44), p. 417 | `Φ` is `V`-uniformly ergodic for `V(x) = |x|²`, respectively for `V = θ̃⁴ + ε₀θ̃²y² + ε₀²y²`. | `|||·|||_V` divides by `V` and (V4) is stated for `V ≥ 1` (p. 392), and both functions vanish at `0`. `V(x) = |x|² + 1` and `V = sacV ε₀ + 1` are used (`theorem_16_5_1`, `proposition_16_5_2`, `proposition_16_5_2_gaussian`). The convergence of second moments is unchanged; no counterexample is given. |
| §16.1.3, p. 399 | For the forward recurrence time `δ`-skeleton, `∫ |Pⁿ(x, dy) e^{γy} − π(dy) e^{γy}| < e^{γx} r⁻ⁿ`. | A constant is needed. At `n = 0` the left side is `‖δ_x − π‖_V = V(x) + π(V)`, since the stationary law (normalised `F[y, ∞) dy`) has no atoms, and this exceeds `V(x) = e^{γx}`. The bound proved is `‖Pⁿ(x, ·) − π‖_V ≤ R r⁻ⁿ V(x)` with `R < ∞` (`fwdChain_vUniformlyErgodic`), as Theorem 16.0.1 gives. No counterexample is stated in Lean. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Throughout | `∞ > V ≥ 1` (p. 392), and signed measures of finite `V`-variation, so that `π(V) < ∞` whenever `|||Pⁿ − 1 ⊗ π|||_V` is used. | `V : X → [0, ∞]` is measurable, with `1 ≤ V` and `V ≠ ∞` as hypotheses where they are used. `fNorm` tests only functions integrable for both measures, so `μ(V) < ∞` is an explicit hypothesis of the submultiplicativity (`vOpNorm_comp_le`, `vErgDist_add_le`) and of Proposition 16.1.3 (`proposition_16_1_3`); `lintegral_ne_top_of_vErgDist_zero` shows it is necessary. The state space is countably generated (`MeasurableSpace.CountablyGenerated X`, Mathlib) where petite sets are used. The invariant probability `π` is a parameter `μ`, and the existence results hold for every invariant probability. |
| (16.2), p. 392 | "An ergodic chain" is `V`-uniformly ergodic if the distances tend to `0`. | `IsVUniformlyErgodic V P μ` asks that `μ` be invariant and that the distances tend to `0`; `ψ`-irreducibility and aperiodicity are hypotheses of the theorems that use it. |
| Lemma 16.1.1, p. 395 | If `|||P₁ − P₂|||_V < ∞`, `P₁ − P₂` is a bounded operator on `L∞_V` with norm `|||P₁ − P₂|||_V`. | `P₁(x, V)` and `P₂(x, V)` are assumed finite, so that `P₁g` and `P₂g` are defined for `|g| ≤ V`; then the identity holds in `[0, ∞]` (`lemma_16_1_1`) and the operator bound holds (`lemma_16_1_1_bounded`). |
| Proposition 16.1.3, p. 396 | `|||P − 1 ⊗ π|||_V < ∞` and `|||P^{n₀} − 1 ⊗ π|||_V < 1` for some `n₀`. | `π(V) < ∞` and `n₀ ≥ 1` (`proposition_16_1_3`). |
| Theorem 16.1.4, p. 396 | A `ψ`-irreducible chain; `c⁻¹V ≤ V₀ ≤ cV`. | As in the book, aperiodicity is not assumed. The conclusion is stronger: `V ≤ V₀ ≤ cV` (`theorem_16_1_4`). |
| Theorem 16.1.5, p. 398; (16.17) | A `V`-uniformly ergodic chain. | `ψ`-irreducibility, aperiodicity and finite distances are assumed (`theorem_16_1_5`, `eq_16_17`), as in the corrected Theorem 16.0.1, whose (ii) the proof uses. `g` and `h` are measurable. |
| Theorem 16.0.2, p. 394 | "For any Markov chain" the eight conditions are equivalent. | Conditions (iv) and (vi)–(viii) refer to aperiodicity, which is defined for `ψ`-irreducible chains. The theorem is proved for a `ψ`-irreducible chain (`theorem_16_0_2`), and Theorem 16.2.1 covers (i)–(iii) with no irreducibility (`theorem_16_2_1`). In (viii), as in Theorem 16.2.2 (v), the bounded solution has `V ≥ 1`. |
| Theorem 16.2.1, p. 400 | No irreducibility or aperiodicity; `π` is the limit. | An invariant probability `μ` is given (`theorem_16_2_1`). |
| Theorem 16.2.5, p. 406 | A compact state space. | `X` is a compact Hausdorff space with `OpensMeasurableSpace X` and a countably generated `σ`-algebra (`theorem_16_2_5`). |
| Lemma 16.2.6 and Theorem 16.2.7, pp. 406–407 | CM(F) forward accessible, Lagrange stable, M-irreducible and aperiodic; (NSS1)–(NSS3). | Forward accessibility is the rank condition (`RankCondition`), the disturbance law has a lower semicontinuous density (`IsLSCDensity`), and "aperiodic" is a minimal set of period one (`IsPeriodOf F O M 1`), the setting of Theorem 7.3.5 (ii) (`lemma_16_2_6`, `theorem_16_2_7`). The abstract form `theorem_16_2_7_restrict` takes a `ψ`-irreducible aperiodic T-chain and a non-empty compact absorbing set. The uniqueness of `π` is `eq_of_isInvariant_of_isPositive`. |
| Theorem 16.3.1, p. 407 | A `ψ`-irreducible ergodic chain; a finite test function `V` with (16.25)–(16.27). | "Ergodic" is used for aperiodicity, which is a hypothesis; the rest is not needed beyond (16.25), and positivity is a conclusion. `V : X → ℝ` is measurable and nonnegative, and the integrals in (16.25)–(16.27) are assumed to exist (`theorem_16_3_1`). |
| Theorem 16.3.2, p. 410 | `Φ` geometrically ergodic; (16.32) for petite `C ∈ B⁺(X)`; (16.33) for `g` unbounded off petite sets. | The chain is `ψ`-irreducible and aperiodic, and geometric ergodicity is (V4) for a petite set with `V` finite somewhere (Theorem 15.0.1 (iii)). (16.32) holds for every `B ∈ B⁺(X)`, petite or not (`theorem_16_3_2`), and (16.33) needs no condition on `g` (`theorem_16_3_2_skipFree`, with `k ≥ 1`): Theorem 15.3.3 bounds `E_x[r^{τ_B}]` by `c(B) V(x)` for every `B ∈ B⁺(X)`, and some sublevel set of `g` is always in `B⁺(X)`. |
| §16.1.3, p. 399 | The forward recurrence time `δ`-skeleton `V⁺_δ` with spread-out `Γ ∈ G⁺(γ)`; `V(x) = e^{γx}` and `C = [0, δ]`. | The chain is `fwdChain Γ δ` (carried), which moves by `V⁺_δ` on `(0, ∞)` and restarts uniformly on `(0, δ)` from `(−∞, 0]`, so that it is irreducible on `ℝ`. The restart region belongs to the state space, so `C = [0, δ]` becomes `(−∞, δ]` (`fwdChain_isPetite_Iic`) and `V(x) = e^{γx⁺}` (`fwdExpV`). `Γ` lives on `[0, ∞)` and is not concentrated at `0`, and `δ` is small, as Propositions 5.3.3 and 5.4.7 require for aperiodicity and small sets (`fwdChain_vUniformlyErgodic`). |
| §16.1.3, p. 400 | Random walk on `[0, ∞)` with (a) and (b). | The increment is integrable, so that `β` is defined (`halfLine_vUniformlyErgodic`). |
| (16.30), p. 409 | `αᵢ > 0`, `γᵢ, βᵢ < 1`. | `Σ α = 1`, `γᵢ ≤ 1`, `βᵢ < 1` for the transition matrix; `αⱼ > 0` for `j ≥ 1` and `γᵢ > 0` for irreducibility (`upDown_isIrreducibleChain`). |
| Theorem 16.4.1, p. 411 | The embedded M/G/1 chain is ergodic, with service law in `G⁺(γ)`. | `λ > 0` and a service law not concentrated at `0`, so that the chain is irreducible (`mG1_poisson_isIrreducibleChain`, carried). "Ergodic" is `Σₖ k qₖ < 1`, which is positivity by Proposition 10.3.1 (`theorem_16_4_1`). |
| Theorem 16.4.2, p. 412 | The gated-limited polling model described in the text. | The description is taken literally: there are no switchover times, so a visit to an empty queue takes no time and brings no arrivals; the service times of the `min(x, ℓₖ)` customers served at a visit are added up; and the arrivals during a visit are Poisson in that total time (`visitMeasure`, `pollKernel`). The gate limits are `ℓₖ ≥ 1` and the mean service times are positive (`theorem_16_4_2`). The empty state is the accessible state used for irreducibility and aperiodicity (`pollKernel_reach_zero`). The commentary (p. 420) notes that [2] embeds the system at every gate; that model is not formalised. |
| Theorem 16.4.3, p. 414 | The `h`-approximation, ergodic, with `h < (λ + ν)⁻¹` and the phase distribution in `G⁺(γ)`. | "Ergodic" is the load condition `λm < ν`, `m` the mean number of phases; `h < (λ + ν)⁻¹` is `a + b < 1` with `a = λh`, `b = νh`; `G⁺(γ)` is `Σₖ pₖ e^{γk} < ∞` (`theorem_16_4_3`). |
| Theorem 16.5.1, p. 415 | (RCA1)–(RCA3); the proof quotes two results of Nicholls and Quinn [299]. | The quoted results are hypotheses: positive definite `M` and `N` with (16.41). So are `ψ`-irreducibility, aperiodicity and the petiteness of compact sets, which the book derives from (RCA3) through the T-chain property (Theorem 6.2.9). Of (RCA2) only `E[W] = 0` and the integrability of `WWᵀ` are used directly (`theorem_16_5_1`). |
| Proposition 16.5.2, p. 417 | The SAC model (SAC1)–(SAC2), Gaussian disturbances, `σ_z² < 1`. | `proposition_16_5_2` takes independent centred disturbances with `E[Z²] = σ_z²`, `E[W²] = σ_w²` and finite fourth moments, `|α| < 1`, `σ_z, σ_w ≠ 0`, and assumes `ψ`-irreducibility, aperiodicity and petite compact sets for the chain restricted to `[σ_z², σ_z²/(1 − α²)] × ℝ²`. For Gaussian disturbances these are derived (`proposition_16_5_2_gaussian`, through `proposition_7_4_3`, carried, which needs `α ≠ 0`). |
| (16.49), p. 417 | From ergodicity, in steady state `θ̃ₖ = θₖ − E[θₖ | Y₀, …, Yₖ]` and `Σₖ = E[θ̃ₖ² | Y₀, …, Yₖ]`. | `eq_16_49` takes the two expectation identities as hypotheses. For Gaussian disturbances every invariant probability is shown to be a Kalman law (`isKalmanLaw_of_isInvariant`), and the identities and (16.49) follow with no hypothesis on the steady state (`sac_steady_state_identities`, `eq_16_49_gaussian`). |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 16.1.4, p. 397 | Fix `n` with `Rρⁿ < e⁻¹` and take `V₀ = Σ_{i<n} e^{i/n} PⁱV`. | Any `s > 1` with `R(s/r)ⁿ ≤ 1` works for `V₀ = Σ_{i<n} sⁱ PⁱV`, through the identity `sPV₀ + V = V₀ + sⁿPⁿV`; then Lemma 15.2.8 (`theorem_16_1_4`, `lemma_15_2_8`, carried). |
| Theorem 16.1.5, p. 398 | Centre `g` and `h`, bound `E_x[h̄(Φₖ) ḡ(Φₖ₊ₙ)]` through `√V`, and use (15.35) for `E_x[V(Φₖ)]`. | The covariance is split as `∫ Pᵏ(x, dy) g(y)(Pⁿh(y) − μ(h)) + Pᵏg(x)(μ(h) − Pᵏ⁺ⁿh(x))`, and both terms are bounded with `|||Pⁿ − 1 ⊗ μ|||_{√V}` (`exists_vErgDist_sqrt_le`, `integral_pair_eq`, `theorem_16_1_5`). The bound is the same. |
| Theorem 16.2.3, p. 402 | `V = 1 + 1_{Cᶜ}` is a bounded solution of (16.10) for the `m`-skeleton, so the skeleton and the chain are uniformly ergodic. | `X` is an increasing union of petite sets, so some petite `C` has `φ(C) > ε`; Doeblin's condition makes `X ⇝ C` uniformly, so `X` is petite, and Theorem 16.2.2 applies (`theorem_16_2_3`). The converse uses `φ = μ`, as in the book. |
| Theorem 16.2.4, pp. 402–403 | A coupling of two copies of the chain (16.22)–(16.23), then the contraction property for `m > 1`. | The analytic form of the coupling: if `Q(x, ·) ≥ ν` for every `x`, then `‖λQ − λ'Q‖ ≤ (1 − ν(X)) ‖λ − λ'‖` (`tvNorm_comp_le_of_le`), iterated along `P^{mk}` (`tvNorm_pow_mul_comp_le`). |
| §16.2.2, (16.24), pp. 404–405 | The ladder chain on `ℤ₊ × ℤ₊` is uniformly ergodic, `f`-ergodic for `f(i, k) = k`, and not `f`-geometrically ergodic. | The claim is proved for a simpler chain, `resetKernel`: from `k` it jumps to `0` or to `k + 1` with probability `½` each, `π(k) = 2^{−(k+1)}` (`isInvariant_resetPi`). The whole space is `½δ₀`-small, so `‖Pⁿ(x, ·) − π‖ ≤ 2 · 2⁻ⁿ` (`reset_uniformlyErgodic`). `f(k) = 2ᵏ/(k + 1)²` has `π(f) < ∞` (`lintegral_resetF_ne_top`), but `‖Pⁿ(x, ·) − π‖_f ≥ 1/(2(x + n + 1)²)` (`fNorm_reset_ge`), so `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f = ∞` for every `r > 1` and every `x` (`reset_not_fGeometric`). The ladder chain itself is not formalised. |
| p. 399, p. 403 | The forward recurrence time chain is not uniformly ergodic, since the mean return time to `[0, δ]` from `x` is of order `x` (Theorem 16.2.2 (iii)). | From `x > nδ` the chain moves deterministically, `Pⁿ(x, ·) = δ_{x − nδ}` (`fwdSkelKernel_pow_of_lt`), so `sup_x ‖Pⁿ(x, ·) − π‖ ≥ 1/2` for every `n` and every probability `π` (`fwdChain_not_uniformlyErgodic`), and likewise for every restriction to an absorbing set that is unbounded above (`restrict_fwdChain_not_uniformlyErgodic`). |
| Theorem 16.3.1, p. 408 | A second-order Taylor expansion (16.28) and the bound (16.29) with `x² ≤ eˣ`. | `eᵗ ≤ 1 + t + t² e^{max(t, 0)}` (`exp_le_one_add_add_sq`, from `1 − t ≤ e^{−t}`) and, for `0 < δ ≤ β/2`, `e^{δu} ≤ 1 + δu + δ²(u² 1{u < 0} + 32β⁻² e^{βu} 1{u ≥ 0})` (`exp_mul_le_increment`, with `sq_le_exp_mul`). |
| Theorem 16.3.2, p. 410 | Theorem 15.2.4 gives (V4) for `G_C^{(r)}(·, X)`, Theorem 14.3.7 gives `π(V) < ∞`, then Jensen's inequality. | Theorem 15.3.3 gives `E_x[r^{σ_B}] ≤ c V(x)` for every `B ∈ B⁺(X)` (`exists_lintegral_tpow_firstHit_le`); Jensen's inequality for `σ_B` is proved through the tangent line of the exponential (`ofReal_exp_meanHitTime_le`). |
| Theorem 16.4.1, p. 412 | Theorem 16.3.1 with `V(i) = i`, after checking (16.26)–(16.27). | Theorem 16.3.1 for `V(i) = i`, done directly: with the increment `W = A − 1` off `0`, `E[W] < 0` and the generating function of the arrivals (`tsum_exp_mul_poissonWeight`), `exists_mgf_lt_one` gives `E[e^{δW}] < 1`, which is (V4) for `e^{δi}` with `C = {0}` (`theorem_16_4_1`). |
| Theorem 16.4.2, pp. 412–413 | Finitely many kinds of one-step increments, with finite exponential and quadratic sums by the Laplace–Stieltjes transforms. | The exponential moments are computed visit by visit, `E e^{βV} = e^{βV(j − s eₖ)} (∫ e^{κt} Gₖ(dt))ˢ` (`lintegral_visit_exp`) and `E e^{−V} ≤ e^{−V(j − s eₖ)}` (`lintegral_visit_exp_neg`), and multiplied over a cycle (`pollTail_exp`); they give (16.26)–(16.27) for the scaled linear `V`. |
| Theorem 16.4.3, pp. 413–414 | A coupling with two uniform sequences shows that `V₀(i) = E_i[σ₀]` is linear, (16.36)–(16.37), which gives (16.26). | The linear `V(i) = w(m i₁ + i₂)`, `w = 1/(νh − λh m)`, satisfies (16.25) with equality, `PV = V − 1` off `0` (`phKernel_drift`). Its increments are bounded below and have bounded exponential moments (`phKernel_sq_le`, `phKernel_exp_le`), and Theorem 16.3.1 applies. `V` is not identified with `E_i[σ₀]`. |
| Proposition 16.5.2, pp. 416–417 | `Pθ̃²y²` and `Pθ̃⁴` are bounded separately, (16.46)–(16.47), and combined with (16.45). | `θ̃'²Y'²` and `θ̃'⁴` are bounded pointwise by Young's inequality before integrating (`sq_add_le_young`, `pow_four_add_le_young`, `sac_drift`), which gives the leading coefficients `σ_z²` and `α⁴` up to a factor `1 + δ`. |

## Conventions

* Transition laws are Mathlib's kernels, and `Pⁿ` is the kernel power. Measures, kernels, test
  functions `V` and the distances take values in `[0, ∞]` (`ℝ≥0∞`). `vOpNorm V P₁ P₂` and
  `vErgDist V P μ n = |||Pⁿ − 1 ⊗ μ|||_V` may be `∞`, and `1 ⊗ μ` is `Kernel.const X μ`.
* `L∞_V` is a space of real functions (`vNormFn`); the book's functions into `ℝ₊` would not form a
  vector space.
* `IsVUniformlyErgodic V P μ` and `IsUniformlyErgodic P μ` include the invariance of `μ`. Uniform
  ergodicity is `V`-uniform ergodicity for `V ≡ 1` (`isUniformlyErgodic_iff`). The total variation
  norm `tvNorm` (carried) is at most `2`.
* Doeblin's condition (`IsDoeblin`) asks for `Pᵐ(x, A) ≥ δ`, where (16.9) has `inf_x Pᵐ(x, A) > δ`;
  the two are equivalent up to the choice of `δ`.
* The rate `2ρ^{⌊n/m⌋}` of (16.11) and (16.21), with `ρ = 1 − νₘ(X)`, is proved as stated
  (`theorem_16_2_4`, for every invariant probability; the same rate appears in
  `theorem_16_2_7_restrict` and `theorem_16_2_7`). The integer part cannot be dropped:
  `theorem_16_2_4_counterexample` is the deterministic chain `0 ↦ 1 ↦ 2 ↦ 2` on `ℕ` (`climbStep`,
  `climbKernel`), for which `P²(x, ·) = δ₂` for every `x`, so `X` is `δ₂`-small with `m = 2` and
  `ρ = 0` and `δ₂` is invariant, while `‖P(0, ·) − δ₂‖ = 2 > 2ρ^{1/2} = 0`.
* `Γ ∈ G⁺(γ)` is `IsLaplaceFinite Γ γ`, the finiteness of `∫ e^{sw} Γ(dw)` for `0 < s ≤ γ`. For
  laws on `[0, ∞)` (service times, phases) it is stated as `∫ e^{γt} G(dt) < ∞`, which implies the
  rest.
* In §16.4.3 the phases are completed at rate `ν`, as the transition probabilities `νh` and the
  mean service time `Σₖ kpₖ/ν` require (the text says "with mean `ν`"). A job has `k + 1` phases
  with probability `p k` (`p : ℕ → ℝ≥0∞`). The state space `phSpace` contains only the states with
  `i₂ = 0 → i₁ = 0`: the server is busy whenever a job waits.
* In §16.5.1 `W` takes values in `ℝⁿ`, as the recursion (16.38) requires (the text says
  `p`-vectors). The quadratic form `xᵀMx` is `quadForm M x` on `Fin n → ℝ`.
* The SAC state is `(Σ, θ̃, Y)` on `ℝ³` (`sacKernel`, carried), and its absorbing set is
  `sacSet α σ_z = [σ_z², σ_z²/(1 − α²)] × ℝ²` (equal to `sacSpace`, `sacSpace_eq_sacSet`).
* The carried modules are copied from the earlier projects without change apart from the namespace
  and the imports (see the [README](../README.md)). The corrections they contain belong to
  Chapters 1–15, are recorded in their module docstrings and in those projects, and are not
  repeated here, except where a Chapter 16 entry above uses them.

## Not formalised

* **The ladder chain (16.24)** (pp. 404–405) and its calculations; the claim it illustrates is
  proved for `resetKernel` (above).
* **The centred bound (16.16)** (p. 398), and the remark that integrating it over an initial law
  `μ` with `μ(V) < ∞` gives a mixing condition from `μ`. The covariance bound of Theorem 16.1.5 and
  the stationary bound (16.17) are formalised.
* **The forward recurrence time `δ`-skeleton** (p. 399): the necessity of `Γ ∈ G⁺(γ)` for
  geometric ergodicity, and the uniform ergodicity of the chain on `[0, c]` when `Γ[0, c] = 1`.
  The "only if" half of the bounded-range statement is formalised
  (`fwdChain_unbounded_not_uniformlyErgodic`).
* **Random walk on `[0, ∞)`**: the result `E_x[τ₀] ∼ cx` quoted from [69] (p. 403).
* **The M/PH/1 queue** (pp. 413–414): the identification of the linear function with
  `V₀(i) = E_i[σ₀]` in (16.36)–(16.37) and the coupling proof behind it. The linear function is
  shown to satisfy (16.25) directly.
* **The queueing models** (p. 411): the comparison `ε₁|i|₁ ≤ V(i) ≤ ε₂|i|₁` for the minimal solution
  of (16.25); linear test functions are used directly.
* **The RCA model** (pp. 414–416): the T-chain property, `ψ`-irreducibility and aperiodicity derived
  from (RCA3) through Theorem 6.2.9; the Kronecker identities (16.39); and the two results (16.40)
  and (16.41) of Nicholls and Quinn [299], with the eigenvalue condition of (RCA2), which are
  hypotheses of `theorem_16_5_1`.
* **The adaptive control model**: for general (non-Gaussian) disturbances, the irreducibility,
  aperiodicity and petiteness hypotheses of `proposition_16_5_2` and the steady-state identities
  behind (16.49); the remark on the optimal performance (p. 417); Figure 16.1 (p. 418).
* **§16.6**, the commentary (pp. 418–420), apart from the bounded-range condition (16.50)
  (`theorem_16_3_1_bounded_range`): the history, quasi-compact operators, the decomposition of
  reducible T-chains on compact spaces, and the second-edition notes.
* **Informal remarks.** The aims of the chapter (pp. 392–393, 395); the forward reference to
  Chapter 17 (p. 397); the comparison with §15.1.4 and the typical compact absorbing sets (p. 399);
  the remarks on moments and on the Bernoulli walk (p. 400); the use of the minorization (p. 403);
  the moral of §16.2.2 (p. 406); inputs of Lagrange stable models (p. 406); the remark that the
  random walk does not need (16.27) (p. 408); the minimality of `V_C` (pp. 407, 413), which is
  Theorem 11.3.5 (`theorem_11_3_5_i`, carried); skip-freeness and Doeblin's condition, the scaling
  `V_C`, and the invariant law `π(j) ∝ γⱼ(1 − βⱼ)⁻¹` of the chain (15.20) (pp. 410–411); the
  uniqueness of `π` for the adaptive model, which is not stated separately (p. 417); and the
  motivation for autoregressive models (p. 414).
