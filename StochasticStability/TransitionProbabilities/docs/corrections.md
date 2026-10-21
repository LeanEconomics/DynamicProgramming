# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, or a convention chosen. Six of the claims below are refuted in Lean by a
counterexample, and a corrected statement is proved. For the other corrections the table says why
no counterexample is given. The last section lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| pp. 49, 53 | "The initial condition requires, of course, that `P_x(Φ₀ = x) = 1`." | `{Φ₀ = x}` is an event only when `{x}` is measurable. A countably generated σ-algebra need not contain the singletons; the trivial σ-algebra on a two-point space is an example. On every measurable space, the law of `Φ₀` under `P_x` is `δ_x` (`pathKernel_map_zero`), that is, `P_x(Φ₀ ∈ A) = 1_A(x)` for every measurable `A` (`pathKernel_zero_mem`). When singletons are measurable, `Φ₀ = x` holds `P_x`-almost surely (`ae_pathKernel_zero`). No Lean counterexample is given. |
| p. 55 | The backward recurrence time matrix is displayed with rows `b(1), 1 − b(1), 0, …`; `b(2), 0, 1 − b(2), …`; …, where `b(j) = p(j + 1)/p̄(j)`. | By (3.10), `P(x, 0) = p(x + 1)/p̄(x) = b(x)` (`bwdRecMatrix_zero`), so row `x` is `b(x)` in column `0` and `1 − b(x)` in column `x + 1`. The display shifts the index by one. For `p(1) = p(2) = 1/2` (`halfHalf`), the display gives `P(0, 0) = b(1) = 1`, while (3.10) gives `P(0, 0) = b(0) = 1/2` (`bwdRecMatrix_display_counterexample`). The matrix is `bwdRecMatrix`, with rows `b(0), b(1), …`. |
| p. 56 | For the integer storage model, `Γ(x) = P(Sₙ − Jₙ = x) = Σ_{i ≥ 0} H(i) G(x + i)`. | The sign is wrong. For independent input `S ∼ H` and release `J ∼ G`, `P(S − J = x) = Σᵢ H(i) G(i − x)` (`storage_increment_singleton`). With `S = 0` and `J = 1` surely, `S − J = −1` surely, but the printed sum at `x = 1` is `1` (`storage_increment_counterexample`). |
| (3.18), p. 57 | `P(S₀ + ⋯ + S_{j+1} > t > S₀ + ⋯ + Sⱼ) = e^{−μt}(μt)ʲ/j!`. | The event counts `j + 1` completed services `S₀, …, Sⱼ`, but the right side is the Poisson weight of `j`: the index is off by one. With `j = 0`, `μ = 1` and `t = 2`, the probability that exactly one service is completed by `t` is `2e^{−2}`, not `e^{−2}` (`eq_3_18_counterexample`). The correct statement is `P(S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}) = e^{−μt}(μt)ʲ/j!` (`eq_3_18`, with `countEvent` and `poissonCount`). The book cites this from Çinlar; here it is proved by induction on `j`. |
| (3.19), p. 58 | The text introduces (3.19) "for each `j ≥ 0`", and the display `qⱼ = ∫ {e^{−λt}(λt)ʲ/j!} H(dt)` carries the range `j ≥ 1`. | The display restricts to `j ≥ 1`, the text to `j ≥ 0`. The value `q₀` is needed: it is the first column of the matrix of Proposition 3.3.2. `poissonWeight` is defined for every `j ≥ 0`, and `eq_3_19` holds for every `j`. This is recorded in the docstring of `SpecificMatrices`; there is nothing to refute. |
| (3.32), p. 66 | `E_μ[θ^ζH \| 𝓕_ζ^Φ] = E_{Φ_ζ}[H]` a.s. `[P_μ]`, "on the set `{ζ < ∞}`". | `θ^ζH` is only defined on `{ζ < ∞}`, so the left side is not the conditional expectation of a function on `Ω`. The precise statement multiplies both sides by the `𝓕_ζ^Φ`-measurable factor `1_{ζ<∞}`: `E_μ[1_{ζ<∞} θ^ζH \| 𝓕_ζ^Φ] = 1_{ζ<∞} E_{Φ_ζ}[H]`, `P_μ`-a.s. (`strong_markov_property`; `measurableSet_stoppedField_ne_top`). This makes the statement precise, so there is no counterexample. `StrongMarkovProperty` and `proposition_3_4_6` use this form. |
| (3.37), p. 68 | `Γ(A) = P(Sₙ − Jₙ ∈ A) = ∫ G(A/r + y/r) H(dy)`, with `A/r = {y : ry ∈ A}`. | The printed integral is the law of `J − S`, not of `S − J`; it repeats the sign error of p. 56. The increment law is `Γ(A) = ∫ G{t : y − rt ∈ A} H(dy)` (`eq_3_37`), which is `∫ G((y − A)/r) H(dy)` for `r > 0` (`eq_3_37_div`). With `S = 0`, `T = 1` surely and `r = 1`, `S − J = −1` surely, while the printed formula gives mass `0` to `{−1}` (`eq_3_37_counterexample`). |
| (3.39), p. 70 | For `x ≤ δ`, `P^δ(x, A) = ∫_0^{δ−x} U(dt) Γ(A − [δ − x] − t)`. | The sign of `δ − x` is wrong. The forward recurrence time `δ`-skeleton has `P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)` for `x ≤ δ` and `A ⊆ (0, ∞)` (`eq_3_39`, whose right side is `eq_3_39_corrected`). Take deterministic renewals of length `1` (`Γ = δ₁`), `δ = 1/2` and `x = 1/4`. The epochs are `1/4, 5/4, …`, so `V⁺` moves surely from `1/4` to `3/4`, and `P^δ(1/4, {3/4}) = 1`. The printed right side (`eq_3_39_printed`) gives `0` at `{3/4}`, the corrected one gives `1` (`eq_3_39_counterexample`, with `setLIntegral_renewalMeasure_dirac_one`). |
| p. 70 | For `dv ⊂ [0, δ]`, `P(V⁻(nδ) ∈ dv \| V⁻((n − 1)δ) = x) = ∫_x^{x+δ} Γ(du) U(dv − (u − x) − δ) Γ(v, ∞)/[Γ(x, ∞)]⁻¹`. | Two errors. (i) The normalisation: the conditional law given age `x` divides by `Γ(x, ∞)`, not by `[Γ(x, ∞)]⁻¹`. For `A ⊆ [0, δ)`, `P(V⁻(nδ) ∈ A \| V⁻((n − 1)δ) = x) = Γ(x, ∞)⁻¹ ∫_{(x, x+δ]} Γ(du) ∫ U(ds) 1{δ − (u − x) − s ∈ A} Γ(δ − (u − x) − s, ∞)` (`bwdSkelKernel_apply_of_subset`). With `Γ = ½δ₁ + ½δ₂` (`halfOneTwo`), `δ = 1` and `x = 1`, the item in progress has length `2` and ends one time unit later, so `P(1, {0}) = 1`; the printed normalisation, which multiplies by `Γ(x, ∞) = 1/2`, gives `1/4` (`bwd_display_counterexample`). (ii) The differential `U(dv − (u − x) − δ)` is the reflection of the correct `U(δ − (u − x) − dv)`: the age at `nδ` is `δ − (u − x) − s` for a renewal-measure point `s`. The differential notation is informal, so (ii) is reported only and has no separate Lean statement; the corrected formula above has the correct orientation. |
| p. 71 | "The translation invariant and 'skip-free to the right' nature of the movement of this chain, incorporated in (3.41)"; `Φ` "can be realised as a Markov chain with the structure (3.41)"; "the chain `Φ` has the form (3.41)". | (3.41) is the definition of `Pⁿₜ(x, y)` (`ladderP`). The structure meant is the ladder structure (3.40) (`ladderKernel`, `eq_3_40_zero`, `eq_3_40_mid`, `eq_3_40_up`, `ladderKernel_translate`). A label typo, recorded in the docstring of `LadderChains`. |
| p. 71 | `Rₙ` is the "total residual service time in the system at `Tₙ+`". | (3.41)–(3.43) use the residual service time of the customer in service, the forward recurrence time of the service renewal process started at `R₀ = x` (`resEpoch`). With the total workload in the system in place of `Rₙ`, the transition law is not (3.42)–(3.43). The construction in Lean takes `Rₙ` to be the residual service of the customer in service at `Tₙ+` (`queueR`, `inService`), and with that definition `(Nₙ, Rₙ)` is a Markov chain with the kernel (3.40), (3.42)–(3.43) (`gig1_isMarkovChain`). This is an inconsistency between a definition and the construction that follows it, so no counterexample is given. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| §3.1, p. 50; §3.4.1, p. 59; Theorem 3.4.1, p. 60; §3.6, p. 72 | A general state space has a countably generated σ-algebra. "The one real assumption in the general case is that the σ-field `B(X)` is countably generated." | Not needed anywhere. `X` is an arbitrary measurable space. Theorem 3.4.1 follows from the Ionescu-Tulcea theorem (`theorem_3_4_1`, `theorem_3_4_1_unique`), and the Markov and strong Markov properties hold for every chain on every measurable space (`markov_property`, `strong_markov_property`, `proposition_3_4_6`). The three kinds of state space of §3.1 are defined (`IsCountableStateSpace`, `IsGeneralStateSpace`, `IsTopologicalStateSpace`), but no result assumes them. Measurable singletons are needed only for `P_x(Φ₀ = x) = 1` to be an event (see above) and on countable spaces, where every set is measurable. |
| Theorem 3.4.1, p. 60; Theorem 3.2.1, p. 54 | "For any initial measure `μ` on `B(X)`". The definitions of pp. 51 and 61 call `μ` an initial distribution. | `μ` is a probability measure. `pathMeasure P μ` is defined for every measure `μ`, and the mixture formula (`pathMeasure_eq_comp`), (3.1) (`pathMeasure_inter_zero`) and (3.20) (`pathMeasure_boxSet`) hold for every `μ`. Theorem 3.4.1 (`theorem_3_4_1`: `P_μ` is a probability measure and the coordinate process is a chain), Theorem 3.2.1 (`theorem_3_2_1`), the Markov property and the strong Markov property assume that `μ` is a probability measure. |
| (3.5), Theorem 3.2.1, pp. 52, 54 | `P_μ(Φₙ₊₁ = y \| Φₙ = x, …, Φ₀ = x₀) = P(x, y)`. | An elementary conditional probability, stated when the conditioning event has positive probability (`theorem_3_2_1`). The unconditional form (3.4) holds for all states (`theorem_3_2_1_fdd`). |
| Proposition 3.4.3, (3.27)–(3.28), p. 63 | For bounded measurable `h`. | This is a remark, not a correction: (3.28) holds for every measurable `H` with `θⁿH` integrable (`markov_property`). The bounded case is `markov_property_bdd`, and (3.27) is `proposition_3_4_3`. The nonnegative forms need no integrability (`markov_lintegral`, `markov_lintegral_mul`). |
| (3.32), Proposition 3.4.6, p. 66 | For bounded measurable `h`. | This is a remark, not a correction: (3.32) holds for every measurable `H` with `1_{ζ<∞} θ^ζH` integrable (`strong_markov_property`), and for nonnegative `H` without integrability (`strong_markov_lintegral`, `strong_markov_lintegral_mul`). `StrongMarkovProperty` is stated for bounded `H`, as in the book. |
| (3.35), p. 67 | "For any `A ⊆ (0, ∞)`", `P(x, A) = Γ(A − x)`. | The book states this condition. On the state space `ℝ≥0` it is `0 ∉ A`, and `eq_3_35` assumes it. It cannot be dropped, since the mass at `0` is `Γ(−∞, −x]` by (3.36) (`eq_3_36`), not `Γ{−x}`. |
| §3.5.3, pp. 68–70 | `Γ` is concentrated on `ℝ₊`; "no matter what the structure of the renewal sequence", `V⁺_δ` and `V⁻_δ` are Markovian, for `δ > 0`. | The increment law also must not be concentrated at `0`: `Γ(−∞, 0) = 0` and `Γ(0, ∞) > 0`. Then the epochs increase to infinity almost surely (`ae_good_prod`), and `V⁺(t)` and `V⁻(t)` are defined for every `t`. If `Γ = δ₀`, every epoch equals the first one, and `V⁺(t)` is an infimum over the empty set for later `t`. Under this condition the forward skeleton is a Markov chain for every law `μ` of the first epoch, with initial law the law of `V⁺(0)` (`fwdSkeleton_isMarkovChain`), with initial law `μ` when the delay law `μ` lives on `(0, ∞)` (`fwdSkeleton_isMarkovChain_delayed`), and with initial law `Γ` for the process with a renewal at `0` when `Γ(−∞, 0] = 0` (`fwdSkeleton_isMarkovChain_undelayed`). The backward skeleton is a Markov chain started at age `0` (`bwdSkeleton_isMarkovChain`). `δ = 0` is allowed. (3.39) is proved for `x ≤ δ` and `A ⊆ (0, ∞)` (`eq_3_39`); `P^δ(x, {x − δ}) = 1` for `x > δ` (`fwdSkelKernel_of_lt`). |
| §3.5.4, pp. 70–71 | The GI/G/1 queue satisfies (Q1)–(Q3); each `Λᵢ`, `Λ*ᵢ` is a substochastic kernel. | The row masses of the ladder kernel are `Σₖ Λₖ(x, ℝ)` (`gig1Ladder_rowSum`), the probability that finitely many services fit into an interarrival time. They equal one, so `gig1Ladder` is a Markov kernel, when interarrival times are nonnegative, `G(−∞, 0) = 0`, and service times are nonnegative and not almost surely `0`, `H(−∞, 0) = 0` and `H(0, ∞) > 0` (`gig1Lambda_tsum_univ`, `isMarkovKernel_gig1Ladder_of_pos`). The proof uses the strong law of large numbers for the truncated services (`tendsto_partialSum_atTop_ae`). The embedded chain `(Nₙ, Rₙ)` is a Markov chain with this kernel when `G(−∞, 0) = 0` and service times are positive, `H(−∞, 0] = 0` (`gig1_isMarkovChain`). |
| (3.14)–(3.19), pp. 56–58 | Exponential service times of rate `μ` and Poisson arrivals of rate `λ`. | The rates are positive where exponential laws are used (`eq_3_14`, `eq_3_15`, `eq_3_18`, `eq_3_19`, `proposition_3_3_1_derived`, `proposition_3_3_2_derived`). Propositions 3.3.1 and 3.3.2 as statements about the matrices hold for every rate (`proposition_3_3_1`, `proposition_3_3_2`). |
| p. 72 | `Ph(x) = ∫ h(F(x, w)) Γ(dw)` for bounded measurable `h`. | This is a remark, not a correction: the identity holds for every nonnegative measurable `h` (`kfun_recursionKernel`) and every real measurable `h` (`kfunR_recursionKernel`). |

## Conventions

* Transition laws are Mathlib's `Kernel X X`; a transition probability kernel is a Markov kernel.
  `Pⁿ` is the kernel power, and in Mathlib's product `P * Q` is "first `Q`, then `P`". Powers of
  one kernel commute, so `Pⁿ` is the book's `Pⁿ`. `PᵐPⁿ` in `pow_add_eq` and `kfun_comp` is read
  "first `Pᵐ`, then `Pⁿ`".
* `X` is an arbitrary measurable space. On a countable space all subsets are measurable, and a
  matrix has entries in `[0, ∞]` and acts through `matKernel`.
* The path space is `Ω = ℕ → X` with the product σ-algebra, and `Φₙ(ω) = ω n`. `P_x` is
  `pathKernel P x` and `P_μ` is `pathMeasure P μ`. `IsMarkovChain P μ pr Φ` is the definition of
  p. 61: a process on any probability space `(Ω, pr)` with the finite-dimensional distributions
  (3.20). Only time-homogeneous chains are defined.
* `E_μ` is the Lebesgue or Bochner integral against `pathMeasure P μ`, and conditional
  expectations are Mathlib's. Almost-sure statements are with respect to `P_μ`.
* `𝓕ₙ^Φ` is `natFilt n`, the σ-algebra generated by the coordinates `Φ₀, …, Φₙ` on path space; it
  does not depend on `μ`. Stopping times are those of this filtration, valued in `ℕ ∪ {∞}`.
  `𝓕_ζ^Φ` is Mathlib's σ-algebra of a stopping time, which is the book's
  (`measurableSet_stoppedField_iff`). `Φ_ζ` (`stoppedState`) and `θ^ζ` (`shiftAt`) are defined
  everywhere; their values on `{ζ = ∞}` are never used.
* `shift n` is `θⁿ`, with `(θⁿω)ᵢ = ω_{n+i}`.
* `τ_A`, `σ_A` and `η_A` are valued in `ℕ ∪ {∞}`. `returnTimeK A k` is `τ_A(k)`, with
  `τ_A(0) = 0`, so that `τ_A(1) = τ_A` (`returnTimeK_one`). `L(x, A)` is `hitProb P A x`.
* `tabooKernel P hA n`, with `hA` the measurability of `A`, is `(P I_{Aᶜ})ⁿ P`, so the book's
  `(P I_{Aᶜ})^{k−1} P` is `tabooKernel P hA (k − 1)`. `tabooProb P A n x B` is the book's
  `_APⁿ(x, B)`.
* The forward recurrence time matrix `fwdRecMatrix` uses the state `k` for `V⁺ = k + 1`.
* The mixed Poisson weights `poissonWeight G μ j` are defined for every `j ≥ 0`. The arrival rate
  `λ` of (3.19) is written `r`.
* Random walk on a half line is on `ℝ≥0`. The storage increment on p. 56 is stated on `ℤ`.
* The renewal processes of §3.5.3 live on the canonical spaces `ℝ × ℝ^ℕ` (first epoch and
  increments, law `μ ⊗ Γ^{⊗ℕ}`) and `ℝ^ℕ` (increments, with a renewal at `0`). `fwdSkel δ n` is
  `V⁺_δ(n)` and `bwdSkel δ n` is `V⁻_δ(n)`. Their kernels are `fwdSkelKernel` and `bwdSkelKernel`;
  from age `a`, `bwdSkelKernel` draws the item in progress from `Γ` conditioned on `(a, ∞)`.
* The backward display of p. 70 is proved for `A ⊆ [0, δ)`. The age `x + δ` reached without a
  renewal is the first display (`bwdSkelKernel_apply_add`).
* The ladder space `ℤ₊ × ℝ` is `ℕ × ℝ`. Row `i` of the ladder kernel is written with
  `k = i + 1 − j ∈ {0, …, i}` (`ladderRow`).
* The GI/G/1 queue lives on `ℝ^ℕ × ℝ^ℕ` with law `G^{⊗ℕ} ⊗ H^{⊗ℕ}` (interarrival times,
  service times). Customers are numbered `0, 1, 2, …`, and the first arrives at `T₀ = 0` to an empty
  system, so the initial law of `Φ` is `δ₀ ⊗ H`.
* In `IsIIDNoise` the disturbances are `W₁, W₂, …`; `W₀` is not used. On the canonical space, the
  coordinate `wₖ` plays `Wₖ₊₁`.
* The carried modules are copied without change apart from the namespace and module docstrings.
  The corrections they contain belong to Chapters 1–2, are recorded in their module docstrings,
  and are not repeated here.

## Not formalised

* **The backward recurrence time skeleton from a general initial age.** `bwdSkeleton_isMarkovChain`
  is for the renewal process with a renewal at time `0`, so the chain starts at age `0`. The
  kernel `bwdSkelKernel` and both displays of p. 70 are proved from every age `x ≥ 0`
  (`bwdSkelKernel_apply_add`, `bwdSkelKernel_apply_of_subset`), but a chain started from a general
  age, or from a delayed renewal process, is not constructed.
* **The converse of the countable-space definition.** Every Markov chain with a transition matrix
  has the point finite-dimensional distributions (3.3)–(3.4) (`IsMarkovChain.fdd_points`). The
  converse, that a process with these point distributions satisfies (3.20) and so is an
  `IsMarkovChain`, is not formalised.
* **The notational conventions.** The use of `P(W ∈ A)` without naming the underlying space
  (p. 50); the notation `Pⁿ(x, f) = δ_x Pⁿ f` (p. 62); the definition of `E_μ` on cylinder sets and
  its extension by linearity (p. 62); the convention on incomplete σ-algebras and `P_*`-almost
  sure events (p. 63).
* **The commentary of §3.6** (pp. 72–74).
* **Other heuristics and remarks.** These are the introduction (pp. 48–49), the discussion of
  state spaces and accessible atoms (pp. 50–51), the remarks on inhomogeneous chains (p. 52), on
  the stability of the recurrence time chains (pp. 55, 69) and on the countable structure of the
  linear model (p. 59), and the comparison of `N*` with random walk on a half line (p. 58). That
  the GI/G/1 queue length is not Markovian without exponential assumptions (p. 70) is not
  formalised as a statement about `N`. The other models said to share the law (3.37) (p. 68),
  inventories and insurance, are not formalised.
