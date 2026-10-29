# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, or a convention chosen. Three of the claims below are refuted in Lean by
a counterexample, and a corrected statement is proved. For the other corrections the table says
why no counterexample is given. The last section lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Lemma 5.5.1, (5.45), p. 116 | If `A ⇝ᵃ B` for some sampling distribution `a`, then `A ⇝ B`. The proof identifies `L(x, B) = Pₓ(τ_B < ∞)` with the probability that `Φₙ ∈ B` for some `n ∈ ℤ₊`, writes `K_a(x, B) = Pₓ(Φ_η ∈ B)` with `η ∼ a`, and concludes `L(x, B) ≥ K_a(x, B)` (5.45) for every `a`. | `τ_B` is the first return time, `n ≥ 1`, while `K_a` includes the term `a(0) P⁰(x, B) = a(0) 1_B(x)`. So (5.45) fails when `a(0) > 0`, and the lemma with it. Take the chain on `Bool` that jumps to `true` from every state (`toTrueKernel`) and `a = δ₀` (`diracDist 0`). Then `K_{δ₀}(x, ·) = δₓ`, so `{false} ⇝ᵃ {false}`, but the chain never returns to `false`, and `L(false, {false}) = 0` (`lemma_5_5_1_counterexample`). For `a(0) = 0`, (5.45) and the lemma hold (`sampledKernel_le_hitProb`, `lemma_5_5_1`). For every `a`, `K_a(x, B) ≤ Pₓ(Φₙ ∈ B for some n ≥ 0) = Pₓ(σ_B < ∞)`, which is (5.45) with `σ_B` in place of `τ_B` (`lemma_5_5_1_firstHit`). |
| Proposition 5.5.6 (ii), p. 120 | If `Φ` is strongly aperiodic and `C` is `ν_a`-petite, then `C₀ ∪ C₁ ⊆ X̌` is `ν_a*`-petite for the split chain. In the proof, `A₀ ∪ X₁` is petite because `X₁` is small and `A₀` is small, the latter since `P̌(x, X₁) ≥ δ` for `x₀ ∈ A₀`. | For `x ∈ A`, `P̌(x₀, X₁) = δ R(x, A)`, where `R` is the residual kernel (5.6), and `R(x, A)` can vanish. The ladder chain on `ℕ` (`ladderKernel`) moves from an even state `2i` to `0` or to `2i + 1` with probability `½` each, and from an odd state `n` to `n − 2`, from `1` to `0`. The set `A` of even states is `½δ₀`-small with `m = 1`, so the chain is strongly aperiodic (`ladder_isStronglyAperiodic`); the chain is split on `A` (`ladderMinorization`). The residual law at `2i` is `δ_{2i+1}` (`ladder_resid_even`). From `(2i, 0)` the split chain therefore descends the odd states on the top level, and is at `(2(i − n) + 1, 0)` after `n + 1 ≤ i + 1` steps (`ladder_splitKernel_even`, `ladder_splitKernel_odd`, `ladder_splitKernel_pow`). For each fixed state, the mass that `Ǩ_a((2i, 0), ·)` gives it tends to `0` as `i → ∞`, so no nonzero minorizing measure exists. Hence `A` is petite for `Φ`, but `A₀ ∪ A₁` is not petite for the split chain (`proposition_5_5_6_ii_counterexample`). The example satisfies every hypothesis of the proposition: the chain is `δ₀`-irreducible (`ladder_isPhiIrreducible_dirac`), `{0, 1}` is absorbing (`ladder_isAbsorbing_zero_one`), `ψ = δ₀ + δ₁` is a maximal irreducibility measure (`ladder_isMaximalIrreducibility`), and `ψ(A) > 0` (`proposition_5_5_6_ii_counterexample_irreducible`). The rest of the book's proof survives. On a countably generated space, for a ψ-irreducible chain, every minorization on a set `A` and every petite set `C`, the set `(C \ A)₀ ∪ X₁` is petite for the split chain (`Minorization.proposition_5_5_6_ii`). For `x ∈ C`, the split initial law satisfies `δₓ* Ǩ_a ≥ ν_a*`, so `C` is petite on average over the coin (`Minorization.proposition_5_5_6_ii_average`). |
| p. 108 | In the proof of Proposition 5.3.2, `Λ₀(x, [0, ∞)) = ∫ G(dt) P(0 ≤ t < σ₁ \| R₀ = x) = ∫ G(dt) I{t < x} = G(−∞, x]`, and so `Λ*₀(x, [0, · ]) = H[0, · ] G(x, ∞)`. | `∫ G(dt) I{t < x}` is `G(−∞, x)`, not `G(−∞, x]`. A service that ends exactly at the next arrival empties the queue. The correct values are `Λ₀(x, ℝ) = G(−∞, x)` (`gig1Lambda_zero_univ`), `Σ_{j≥1} Λⱼ(x, ℝ) = G[x, ∞)` (`gig1Lambda_tail_univ`) and `Λ*₀(x, A) = G[x, ∞) H(A)` (`gig1Ladder_bottom`). With `G = H = δ₁` and `x = 1`: `Λ₀(1, ℝ) = 0`, but `G(−∞, 1] = 1` (`gig1Lambda_zero_counterexample`); and `Λ*₀(1, ℝ) = 1`, but `G(1, ∞) H(ℝ) = 0` (`gig1Ladder_bottom_counterexample`). The conclusion of Proposition 5.3.2 is unaffected, since `G[x, ∞) ≥ G(β, ∞)` for `x ≤ β` (`proposition_5_3_2_gig1`, `proposition_5_3_2_queue`). `proposition_5_3_2` takes the book's formula as a hypothesis. |
| Proposition 5.3.3, p. 109; Proposition 5.4.7, p. 115 | For `δ` small enough, the set `[0, δ]` is small for `V⁺_δ`; the proof concludes that `[0, δ)` is small. Here `V⁺(t) := inf(Zₙ − t : Zₙ ≥ t)`. | The statement and the proof differ at `δ`. The carried Chapter 3 construction takes `V⁺(t) = inf(Zₙ − t : Zₙ > t)`, the time to the first epoch strictly after `t` (`fwdTimeCts`). So `V⁺ > 0`, and the bounds (5.33)–(5.35) are proved for `x ∈ (0, δ)` and `B ⊆ (0, δ)` (`fwdSkel_pow_ge`). The small set is `(0, δ)`, with a multiple of Lebesgue measure on `(0, δ)` as minorizing measure, at the two consecutive times `M` and `M + 1` (`proposition_5_3_3`). Proposition 5.4.7 uses the same set (`proposition_5_4_7`). The hypothesis `Γ(0, ∞) > 0`, with `Γ(−∞, 0) = 0`, is added. It is the condition under which `V⁺_δ` is a Markov chain (`fwdSkeleton_isMarkovChain`); for a spread-out `Γ` on `[0, ∞)` it holds, because `δ₀` is singular. This is a change of convention, not a refutation, so no Lean counterexample is given. |
| (5.2), p. 98 | The minorization condition asks for some `δ > 0`. | `δ = 1` is allowed, and then (5.6) divides by `1 − δ = 0`, so the split kernel is not defined on `C₀`. `Minorization` requires `0 < δ < 1`. This costs nothing: `Minorization.ofLe` builds a minorization with `δ ≤ 1/2` from any bound `P(x, ·) ≥ ν'` on `C` with `0 < ν'(C) < ∞`. With `δ = 1` the kernel is undefined rather than wrong, so there is no counterexample. |
| Theorem 5.4.4, p. 113 | The theorem takes any `ν_M`-small `C ∈ B⁺(X)` and `d = g.c.d. E_C`. Before (5.40) the text assumes `ν_M(C) > 0`, without loss of generality by Proposition 5.2.4. | The theorem as stated takes any `ν_M`-small `C`, but the proof needs `ν_M(C) > 0`, and Proposition 5.2.4 (iii) changes `ν_M` and so `E_C`. Without it the claim fails: for the chain that alternates between two states, `C = {0}` is `δ₁`-small with `M = 1`, `E_C` is the set of odd numbers and its g.c.d. is `1`, yet `{0}, {1}` is a `2`-cycle. This example is not formalised. `theorem_5_4_4` assumes `ν_M(C) > 0` (and `ψ(C) > 0`). |
| §5.3.5, p. 110 | `B₁` is `νₙ`-small, with `n` the dimension of the state space. | `IsSmallSet` requires `m ≥ 1`, as (5.14) does, and `n = 0` is allowed, so the index is `m = max(n, 1)` (`lss_isSmallSet_of_isCompact`). For `n ≥ 1` this is the book's `m = n`. A degenerate case, so there is no counterexample. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorems 5.2.1–5.2.3, Proposition 5.2.4 (ii), Proposition 5.4.5 (ii)–(iii), Propositions 5.5.5–5.5.6, Theorem 5.5.7 | `B(X)` is countably generated, the standing assumption of a general state space (§3.1, p. 50). The proof of Theorem 5.2.1 appeals to it (p. 103). | These results assume a countably generated `B(X)`. Theorem 5.2.1 uses it directly, for jointly measurable densities (`measurable_transDensity`) and for a countable measure-dense family of sets (`exists_rect_of_not_ae_zero`). The others use it through Theorem 5.2.2. The existence of the period also needs it (`exists_isPeriod`). Everything else holds on every measurable space: the splitting and Theorem 5.1.3, Proposition 5.2.4 (i) and (iii), Theorem 5.4.4 for a given small set, Propositions 5.4.5 (i) and 5.4.6, Lemmas 5.5.1–5.5.2, and Propositions 5.5.3–5.5.4. |
| Theorem 5.2.1, p. 103 | `φ` is σ-finite; the conclusion is `pᵐ(x, y) > δ` for `x, y ∈ C`, with `m > 1`, for a version of the densities chosen in the proof. | `φ` is finite (`theorem_5_2_1`), which is all Theorem 5.2.2 needs: it applies Theorem 5.2.1 to a probability measure equivalent to `ψ` (`theorem_4_0_1`, carried). The conclusion is the integrated form `Pᵐ(x, B) ≥ δ φ(B ∩ C)` for `x ∈ C`, with `m ≥ 1`, which is how (5.16) is used. For the densities `transDensity` it gives `pᵐ(x, y) ≥ δ` for `x ∈ C` and `φ`-a.e. `y ∈ C` (`theorem_5_2_1_density_ge`). |
| (5.2), p. 98 | `ν(Cᶜ) = 0` and `ν(C) = 1`. | The construction and Theorem 5.1.3 do not use `ν(Cᶜ) = 0`. It is the separate predicate `Minorization.IsConcentrated`, and the minorizations built from small sets satisfy it (`IsSmallSet.minorization_isConcentrated`, `theorem_5_2_3`, `proposition_5_4_5_i`). |
| p. 96 | A single point is always an atom. | An atom must be in `B(X)`, so `{x}` is an atom when singletons are measurable (`isAtom_singleton`). The countable-space results of §5.4.2 also assume measurable singletons, and Propositions 5.4.2–5.4.3 a countable, non-empty space. |
| Proposition 5.1.1, p. 97 | `Σₙ Pⁿ(x, α) > 0` for every `x`. | The sum may include `n = 0` (`proposition_5_1_1`), so states in `α` need not return to `α`. The conclusion also gives `L(x, α) > 0` for every `x`, and accessibility for every maximal irreducibility measure. |
| Proposition 5.3.2, p. 108 | `G(β) < 1` for all `β < ∞`. | The Lean statement fixes `β` and assumes `G(β, ∞) > 0`, which is the book's condition at that `β`. It also assumes nonnegative interarrival times, `G(−∞, 0) = 0`, and a service law `H` on `[0, ∞)` not concentrated at `0` (`proposition_5_3_2_gig1`), or positive service times for the queue (`proposition_5_3_2_queue`), as the Chapter 3 construction of the queue does (`gig1_isMarkovChain`, carried). The residual service time lives in `ℝ`, so the small set is `{0} × (−∞, β]`, which contains `{0} × [0, β]`. |
| Proposition 5.4.7, p. 115 | `V⁺_δ` is aperiodic for small `δ`. | The book leaves the irreducibility of `V⁺_δ` implicit. `proposition_5_4_7` proves `g.c.d. E_C = 1` for `C = (0, δ)`, which is how the book proves it, and aperiodicity for every maximal irreducibility measure `ψ` with `ψ(C) > 0`. |
| §5.4.4, p. 115 | The forward recurrence time chain on the integers with renewal distribution `p`. | `p(0) = 0` (`periodAt_fwdRec`). Renewal times are positive. If `p(0) > 0`, the chain moves from `0` to `0` with probability at least `p(0)`, so `1` is a return time and the period is `1`, while `g.c.d.{n : p(n) > 0}` can be larger, for instance `2` for `p = ½δ₀ + ½δ₂`. This example is not formalised. |
| §5.3.5, p. 110 | The Gaussian model (LSS3); `B₁` and `B₂` any bounded open balls, with `νₙ` uniform on `B₂`. | The proof holds for every disturbance law that dominates a multiple of Lebesgue measure on each closed ball about `0` (`lss_isSmallSet_of_isCompact`); the Gaussian case is `lss_gaussian_isSmallSet_of_isCompact`. The small set is any compact `K`, and the minorizing measure a multiple of Lebesgue measure on a closed ball `B̄(0, r)` centred at `0`. |
| Proposition 5.4.6, p. 115 | `Φ_d` is aperiodic on each `Dᵢ`. | The irreducibility measure of `Pᵈ` on `Dᵢ` is `ψ` restricted to `Dᵢ` (`proposition_5_4_6`). Aperiodicity is stated as: every family of disjoint measurable sets in `Dᵢ` that `Pᵈ` moves cyclically, with `ψ`-null complement in `Dᵢ`, has length `1` (`proposition_5_4_6_aperiodic`). It assumes that `d` is the period (`IsPeriod`), as the proposition does. |
| Proposition 5.5.6 (i), p. 120 | In either case the sampling distribution has a finite mean. | The finite mean is stated for the uniform distribution (`tsum_mul_uniformDist_ne_top`). For the geometric `a_ε` it is not stated. |

## Conventions

* Transition laws are Mathlib's kernels, and `Pⁿ` is the kernel power. `L(x, A)` is `hitProb`,
  `K_a` is `sampledKernel`, `K_{a_ε}` is `resolvent`, and `U` is `potKernel`, all from the carried
  Chapter 3 modules. φ-irreducibility, maximal irreducibility measures and `⇝` are the carried
  `IsPhiIrreducible`, `IsMaximalIrreducibility` and `UnifAccessible`. "The chain is ψ-irreducible"
  means that `ψ` satisfies `IsMaximalIrreducibility`.
* `IsAtom` requires the atom to be measurable. `IsAccessibleAtom P ψ α` includes the requirement
  that `ψ` is a maximal irreducibility measure.
* The split space `X̌ = X × {0, 1}` is `X × Bool`: `false` is the top level `X₀`, `true` the bottom
  level `X₁`, and `xᵢ` is `(x, false)` or `(x, true)`. `A₀ ∪ A₁` is the preimage of `A` under the
  first projection. A minorization is the structure `Minorization P`, which bundles `C`, `δ` and
  `ν`; the split-chain results are in the namespace `Minorization`.
* `λ*` is `Minorization.split`, defined for every measure as `λ` composed with the coin kernel
  `Minorization.splitK`. The split kernel is `P̌ = Minorization.splitKernel`: first move by
  `Minorization.baseK`, which is the residual law `R` (`Minorization.resid`) from the top level and
  `ν` from the bottom level, then toss the coin. On `C`, `R(x, ·) = (1 − δ)⁻¹(P(x, ·) − δν)`; off
  `C`, `R(x, ·) = P(x, ·)`. (5.5)–(5.7) are proved from this definition.
* `IsSmallSet P m ν C` requires `C` measurable, `m ≥ 1`, `ν ≠ 0` and `Pᵐ(x, ·) ≥ ν` for `x ∈ C`.
  `IsPetiteSet P a ν C` requires `C` measurable, `a` a sampling distribution, `ν ≠ 0` and
  `K_a(x, ·) ≥ ν` for `x ∈ C`. A sampling distribution is a function `a : ℕ → [0, ∞]` with
  `Σₙ a(n) = 1` (`IsSamplingDist`).
* The densities `pⁿ(x, y)` of (5.15) are `transDensity`, Mathlib's kernel Radon–Nikodym derivative
  of the absolutely continuous part of `Pⁿ(x, ·)`.
* Cycles are indexed by `ZMod d`: the book's `D₁, …, D_d` with `P(x, D_{i+1}) = 1` (mod `d`) is a
  family `D i`, `i ∈ ZMod d`. `IsCycle P ψ d D` requires measurable, disjoint classes and a
  `ψ`-null complement of their union. The relabelling in the uniqueness part of Theorem 5.4.4 is a
  shift `i ↦ k + i`. `IsPeriod P ψ d` says that a `d`-cycle exists and that `d' ≤ d` for every
  `d'`-cycle. `IsAperiodic` is `IsPeriod` with `d = 1`. `IsStronglyAperiodic` asks for a
  `ν₁`-small set `A` with `ν₁(A) > 0`.
* `E_C` of (5.40) is `smallTimes P C ν`, and the sets `D*ᵢ` are `cycleSet`. The book's
  `Σₙ P^{nd−i}(y, C) > 0` is written as a time `k ≥ 1` with `k + i ≡ 0 (mod d)`.
* `setGcd S` is the largest common divisor of the elements of `S ⊆ ℕ`. It is used for sets that
  are closed under addition and contain a positive element (`IsAddClosed`). The period of a state
  on a countable space is `periodAt`. Aperiodicity and strong aperiodicity on a countable space are
  `IsAperiodicCountable` and `IsStronglyAperiodicCountable`, separate from the general-space
  definitions.
* The deterministic cycle of p. 110 is `cycleChain d`, on the `d + 1` points of `Fin (d + 1)`, so
  its period is `d + 1`.
* The forward recurrence time chain `fwdRecKernel p` uses the state `k` for `V⁺ = k + 1`, as in
  the Chapter 3 project: from `0` it jumps to `n − 1` with probability `p(n)`, and from `j ≥ 1` it
  moves to `j − 1`.
* The forward recurrence time `δ`-skeleton is the carried `fwdSkelKernel Γ δ`, with
  `V⁺(t) = inf(Zₙ − t : Zₙ > t)` (`fwdTimeCts`). "`F` is spread out" in Proposition 5.4.7 is read
  as "`Γ` is spread out" (`IsSpreadOut`).
* The GI/G/1 ladder chain is the carried `gig1Ladder H G` on `ℕ × ℝ`, with service law `H` and
  interarrival law `G`. The ladder kernel of Chapter 3 is renamed `ladderChainKernel` in the
  carried `LadderChains`, since `ladderKernel` here is the chain on `ℕ` of the counterexample to
  Proposition 5.5.6 (ii).
* `ℝⁿ` is `Fin n → ℝ`, and `μ_Leb` is Mathlib's Lebesgue (product) measure on it. (LSS3) is the
  product of `p` standard normal laws.
* The carried modules are copied without change apart from the namespace, the imports, module
  docstrings and the renaming of the ladder kernel. The corrections they contain belong to
  Chapters 1–4, are recorded in their module docstrings and in those projects, and are not
  repeated here.

## Not formalised

* **The Athreya–Ney construction of §5.1.3** (5.12)–(5.13). The book argues informally that the
  regeneration occurs sooner or later, and relies on a fact proved only in Chapter 9. The kernel
  `Q` it uses is the residual kernel of the splitting.
* **(5.11)**, splitting under a minorization `P(x, A) ≥ h(x) ν(A)` by a function `h`. The book
  gives no details and refers to Nummelin.
* **The continuous-state cycle example of p. 110**, on `[0, d)` with uniform laws. The finite
  example of the same page is formalised (`cycleChain`).
* **"`X` is not necessarily petite"** (p. 119). The book gives no example of a ψ-irreducible chain
  for which `X` is not petite.
* **Proof devices replaced by other arguments.** The version of the densities satisfying (5.17)
  and the density-point argument (5.18)–(5.23) in the proof of Theorem 5.2.1; Lemma D.4.3 in the
  proof of Proposition 5.3.1; and the Gaussian form (5.36) of `Pᵏ(x₀, ·)`, with the continuity and
  positivity of its density, in §5.3.5. The replacements are listed in the
  [source map](source-map.md).
* **Forward references.** The `μ_Leb`-irreducibility of spread-out random walks (Chapter 6,
  p. 107) and the role of the recurrence assumption (5.12) (Chapter 9).
* **Informal remarks.** The discussion of atoms and pseudo-atoms (pp. 96–98), the interpretations
  of the split chain, of sampled chains (p. 116) and of Lemma 5.5.2 (i) (p. 117), the description
  of cyclic classes and the super-diagonal form of `P` (p. 112), the remark that strong
  aperiodicity fails in general (pp. 114–115), the remarks after Propositions 5.5.4 and 5.5.5 and
  Theorem 5.5.7 (pp. 118–121), and the commentary of §5.6 (pp. 121–122).
