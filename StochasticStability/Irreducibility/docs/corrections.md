# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, or a convention chosen. Every false claim below is refuted in Lean by a
counterexample, and a corrected statement is proved. The last section lists what is not
formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Proposition 4.2.2, p. 83; Theorem 4.0.1, p. 75 | "If `Φ` is φ-irreducible for some measure `φ`, then there exists a probability measure `ψ`" with (i)–(iv). | The definition of φ-irreducibility is vacuous for `φ = 0`, so every chain is `0`-irreducible (`isPhiIrreducible_zero`). The identity chain on `Bool` is `0`-irreducible. It is `ψ`-irreducible for no probability measure `ψ`, since each of the two states is absorbing (`proposition_4_2_2_zero_counterexample`). With `φ ≠ 0`, Proposition 4.2.2 holds (`proposition_4_2_2`, `proposition_4_2_2_maximal`), and so does Theorem 4.0.1 (`theorem_4_0_1`). In (iv) the irreducibility measure `φ'` must also be nonzero, because `φ' = 0` gives `ψ' = 0`. |
| Proposition 4.2.3 (i), p. 84 | "Every absorbing set is full." | The empty set is absorbing, and it is full for no nonzero measure (`proposition_4_2_3_i_counterexample`). Every non-empty absorbing set is full (`proposition_4_2_3_i`). Part (i) holds for every irreducibility measure, not only for a maximal one. |
| p. 77 | For random walk on a half line, "`L(x, 0) > 0` for all states `x` or for none, depending on whether (4.4) holds or not." | False at `x = 0`. For the increment law `Γ = δ₀` (`diracZeroInt`), (4.4) fails, and the walk stays at its starting point. So `L(0, 0) = 1`, while `L(1, 0) = 0` (`rwhl_dichotomy_counterexample`). The dichotomy holds for the states `x ≠ 0`. Under (4.4), `L(x, 0) > 0` for every `x` (`rwhl_hitProb_zero_pos`). If `Γ(−∞, 0) = 0`, then `L(x, 0) = 0` for every `x ≠ 0` (`rwhl_hitProb_zero_eq_zero`). |
| p. 80 | "Thus the chain `N` [of the GI/M/1 queue] is irreducible no matter what the distribution of the inter-arrival times." | The argument uses `P(x, 0) > 0` for every `x`, which can fail. If the interarrival law is `G = δ₀`, no service is completed between arrivals: the Poisson weights are `p₀ = 1`, `pⱼ = 0` for `j ≥ 1` (`poissonWeight_dirac_zero`). The chain then only moves up, and `1` does not lead to `0` (`giM1_dirac_counterexample`). The chain is irreducible when `p₀ > 0` and `P(x, 0) > 0` for every `x` (`giM1_isIrreducibleChain`). For the chain of Proposition 3.3.1 this holds when the service rate is `μ > 0` and `G` is not concentrated at `0` (`poissonWeight_ne_zero`, `giM1_poisson_isIrreducibleChain`). |
| p. 80 | "A similar approach shows that the embedded chain `N*` of the M/G/1 queue is always irreducible." | If the service law is `H = δ₀`, there are no arrivals during a service: `q₀ = 1`. The chain is then absorbed at `0`, and `0` does not lead to `1` (`mG1_dirac_counterexample`). The chain is irreducible when every `q_j` is positive (`mG1_isIrreducibleChain`). For the chain of Proposition 3.3.2 this holds when the arrival rate is `r > 0` and `H` is not concentrated at `0` (`mG1_poisson_isIrreducibleChain`). |
| (4.17), p. 93 | The variance of `X_k` has full rank for some `k` iff "the controllability grammian, defined as `Σ_{i=0}^∞ F^i G Gᵀ (F^i)ᵀ`, has rank `n`." | The series need not converge. For `F = G = 1` on `ℝ¹` every term is `1` (`gramian_series_counterexample`). Its role is taken by the finite sums `Σ_k = Σ_{i<k} F^i G Gᵀ (F^i)ᵀ` of (4.16) (`gramian`). `Σ_k` has full rank for some `k` iff `(F, G)` is controllable, and then `Σ_n` has full rank (`isControllable_iff_gramian`, with `gramian_eq` and `rank_gramian`). |
| (4.18), p. 93 | `p_k(x, y) = (2π\|Σ_k\|)^{−k/2} exp{−½ (y − F^k x)ᵀ Σ_k⁻¹ (y − F^k x)}`. | The normalising constant of a Gaussian density on `ℝⁿ` is `(2π)^{−n/2} \|Σ_k\|^{−1/2}`, and it does not depend on `k`. Take `n = 1`, `k = 2`, `F = 0`, `G = 1`, so that `Σ₂ = 1`. The printed function integrates to `(2π)^{−1/2} ≠ 1`, while the corrected one integrates to `1` (`density_4_18_counterexample`). The proof of Proposition 4.4.3 does not use (4.18) (see below). |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 4.0.1, §4.2, pp. 75, 81–87 | The state space is a general state space, with a countably generated σ-algebra (§3.1). In the proof of Proposition 4.2.2, "we can assume without loss of generality that `φ(X) = 1`". | Neither condition is needed. `X` is an arbitrary measurable space and `φ` an arbitrary nonzero measure, possibly not σ-finite. An exhaustion lemma does the reduction: if `φ ≪ μ` with `μ` finite, then `μ` restricted to the complement of a largest `φ`-null set is a finite measure equivalent to `φ` (`exists_finite_equiv_of_ac`). For `μ`, take the probability measure `K_{a_{1/2}}(x₀, ·)` for any state `x₀`; by Proposition 4.2.1 it dominates `φ`. Normalising the result gives every nonzero irreducibility measure an equivalent probability measure, which is again an irreducibility measure (`exists_prob_equiv`, `IsPhiIrreducible.mono`). |
| Proposition 4.2.2 (iv), p. 83 | "for any finite irreducibility measure `φ'`". | `φ'` need not be finite, but it must be nonzero (see above). `ψ` is equivalent to `maxIrrMeasure P φ'` for every nonzero irreducibility measure `φ'` (`proposition_4_2_2`). |
| Proposition 4.2.4, proof, p. 85 | "If `Φ` is ψ-irreducible then `A` is full and the result is immediate by Proposition 4.2.3." | This is a remark on the proof, not a correction. Proposition 4.2.3 is not needed: for every irreducibility measure `φ`, `Φ_A` is irreducible for the restriction of `φ` to `A` (`proposition_4_2_4`). For a maximal `ψ` and a non-empty absorbing `A`, the restriction is nonzero, and `A` is an absorbing ψ-irreducible set (`proposition_4_2_4_nonzero`). |
| p. 82 | On a countable space, "if we only know that `x → x*` for every `x` … then the chain is `δ_{x*}`-irreducible." | For `x = x*` the convention `x* → x*` (p. 78) does not give `L(x*, {x*}) > 0` directly. The return to `x*` follows from the other states, as in the proof of Proposition 4.2.1, so the claim holds as stated (`isPhiIrreducible_dirac_of_leads`). |
| (4.6)–(4.7), p. 80 | `r = sup(n : p(n) > 0)`; `A = {1, …, r}` is absorbing, and the chain on `A` is irreducible, by `P^{y+r−x}(y, x) ≥ p(r)`. | (4.6) allows `r = ∞`, but (4.7) uses `p(r)`. The Lean results take `r` finite: `fwdRec_isAbsorbing` assumes `p(n) = 0` for `n > r`, and `fwdRec_communicates` assumes `p(r) > 0` and `r ≥ 1`. |
| p. 80 | GI/M/1: `P(x, x + 1) = p₀ > 0` and `P(x, 0) > 0`; M/G/1 by "a similar approach". | GI/M/1 needs a positive service rate, `μ > 0`, and an interarrival law `G` not concentrated at `0` (`giM1_poisson_isIrreducibleChain`). M/G/1 needs a positive arrival rate, `r > 0`, and a service law `H` not concentrated at `0` (`mG1_poisson_isIrreducibleChain`). See the corrections above. |
| p. 81 | Random walk on `ℤ` is irreducible on each `D_r`, by Lemma D.7.4. | The hypothesis is that `Γ` charges a positive and a negative integer. The monoid generated by the support of `Γ` is then the group `dℤ` it generates, which is proved directly (`rw_monoid_eq_group`, `rw_commClass_eq`). |
| p. 89 | Random walk on `ℝ` with `Γ` concentrated on `ℚ` and `Γ(r) > 0` for all `r ∈ ℚ`. | The cosets `x + ℚ` are absorbing, there are uncountably many, and the walk is irreducible for no nonzero measure. All of this holds for every `Γ` concentrated on `ℚ`. The condition `Γ{q} > 0` is used only to make each coset an irreducible set (`randomWalk_rational`). |
| p. 89 | AR(1) with `W` uniform on `[−1, 1]`: `μ_Leb^{[−1,1]}`-irreducible for `\|α₁\| ≤ 1`, explosive and not irreducible for `\|α₁\| > 1`. | The irreducible case holds for every innovation law with a density bounded below on an interval `(−β, β)` (`ar1_isPhiIrreducible_of_density`); the uniform case is `ar1_uniform_isPhiIrreducible`. The explosive case holds for every noise law concentrated on `[−1, 1]`, and the chain is then irreducible for no nonzero measure (`ar1_explosive_not_irreducible`). |
| p. 88 | Content-dependent storage: if `R(x) < ∞` and `P(Tᵢ > R(x)) > 0` for all `x`, the model is δ₀-irreducible; if `R(x) = ∞` the empty state is never reached. | The release function `q` is abstract. The release time enters only through `q(y, t) = 0` for `t > R(y)`, and `P(T > R(y)) > 0` is assumed at every level `y` (`contentPreInput_isPhiIrreducible`). The case `R = ∞` is read as `q(y, t) > 0` for every `y > 0`, with nonnegative inputs (`contentPreInput_hitProb_zero`, `contentPreInput_not_isPhiIrreducible`). |
| Proposition 4.4.3, p. 92 | The model is Gaussian, (LSS3), and the proof uses the Gaussian density (4.18) of `Pᵏ(x, ·)`. | The proposition holds for every noise law `Γ` on `ℝᵖ` that is equivalent to Lebesgue measure (`proposition_4_4_3`). `Pᵏ(x, ·)` is the image of `Γ^{⊗k}` under `u ↦ F^k x + C_k u` (`lss_pow_eq`). For `k ≥ n`, `C_k` is onto (`range_ctrbMap_eq_top`), so `Pᵏ(x, ·)` is equivalent to Lebesgue measure (`ctrbLaw_equiv`, `lss_pow_equiv`). The Gaussian case is `proposition_4_4_3_gaussian`, with `stdGaussian_equiv_volume`. "`φ` possesses a density" is read as `φ ≪ μ_Leb`. Part (iii) uses the lower semicontinuity of `t ↦ ν(B − t)` (`lss_lowerSemicontinuous`). |
| p. 93 | The restricted process on `X₀` is `μ_Leb`-irreducible, "under the Gaussian assumption". | The same holds for every noise law equivalent to Lebesgue measure, and for every `(F, G)`, with no controllability hypothesis (`restricted_irreducible`). When `(F, G)` is controllable, `X₀ = ℝⁿ`. The Gaussian case is `restricted_irreducible_gaussian`. |

## Conventions

* Transition laws are Mathlib's `Kernel X X`, and `Pⁿ` is the kernel power. `L(x, A)` is
  `hitProb P A x = Pₓ(τ_A < ∞)`, with `τ_A` the first return time, `n ≥ 1`. `U` is `potKernel`.
  These, and the path measures `Pₓ`, are from the carried Chapter 3 modules.
* `X` is an arbitrary measurable space, and `B(X)` is its σ-algebra. On a countable space,
  singletons are measurable, every set is then measurable (`measurableSet_of_countable`), and
  matrices have entries in `[0, ∞]` and act through `matKernel`.
* `Leads P x y` is `x = y ∨ L(x, {y}) > 0`, which is the convention `x → x` of p. 78.
  `IsIrreducibleChain` asks for one class `C(x) = X`; on a non-empty space this is equivalent to
  all states communicating (`isIrreducibleChain_iff`).
* `IsAbsorbing P A` is `P(x, A) = 1` for `x ∈ A`. It requires neither non-emptiness nor
  measurability. One definition serves for communicating classes (p. 78) and for general
  absorbing sets (p. 84).
* `IsPhiIrreducible P φ` is defined for every measure, including the zero measure. A maximal
  irreducibility measure (`IsMaximalIrreducibility`) is nonzero by definition. "The chain is
  ψ-irreducible" (p. 84) means that `ψ` satisfies `IsMaximalIrreducibility`. Proposition 4.2.2 is
  stated for any nonzero `φ`, and its `ψ` is `maxIrrMeasure` applied to an equivalent probability
  measure (`proposition_4_2_2_maximal`).
* `K_{a_{1/2}}` is `resolventHalf P`, the resolvent `K_{a_ε}` of (3.26) with `ε = 1/2`. Its sum
  starts at `n = 0`.
* The chain restricted to an absorbing set `A` is `restrictKernel`, a kernel on the subtype `A`.
  The restriction of a measure `φ` to `A` is `φ` pulled back along the inclusion.
* `UnifAccessible P A B` takes `δ` in `(0, ∞]`. `hitSetLevel P A m` is `Ā(m)`, with the sum over
  `1 ≤ n ≤ m`. For `m = 0` the set is empty, since `0⁻¹ = ∞` in `[0, ∞]`.
* The forward recurrence time matrix `fwdRecMatrix` (carried) uses the state `k` for `V⁺ = k + 1`.
  So the book's `{1, …, r}` is `{k : k < r}`, and `P^{x−y}(x, y) = 1` is written
  `Pᵏ(y + k, y) = 1` (`fwdRec_pow_down`).
* The GI/M/1 and M/G/1 matrices take the laws of the number of services or arrivals as data
  (`giM1Matrix`, `mG1Matrix`). The queues of Propositions 3.3.1 and 3.3.2 use the mixed Poisson
  weights `poissonWeight`.
* Random walk on `ℚ` with integer increments is `arMatrix 1 Γ`, the linear model of
  Proposition 3.3.3 with `α = 1`.
* Random walk on a half line is on `ℝ≥0`, and `δ₀` is the Dirac measure at `0`. "`φ(0, ∞) = 0`,
  `φ{0} = 1`" in Proposition 4.3.1 is `δ₀`. Its maximal measure `Σₙ Pⁿ(0, ·) 2⁻ⁿ` is
  `2 K_{a_{1/2}}(0, ·)` (`halfLine_maximal`).
* The content-dependent storage model is taken just before inputs, as corrected in the
  `MarkovModels` project: input first, then release (`contentPreInputKernel`, copied from that
  project).
* `ℝⁿ` is `Fin n → ℝ`, and `μ_Leb` is Mathlib's Lebesgue (product) measure on it. "Lebesgue
  measure on `X₀`" is any additive Haar measure on the subspace. Any two such measures are
  proportional, and the image of Lebesgue measure under a linear isometry onto `X₀` is one of
  them. (LSS3) is the product of `p` standard normal laws.
* `IsControllable` (carried) is the definition of p. 90: every state is reached from every
  initial state in some number of steps. (LCM3) is `IsCtrbRank`. `ctrbMatrix F G k` is
  `C_k = [F^{k−1}G | ⋯ | FG | G]`, and `ctrbMap F G k` is the same map acting on control
  sequences, `(u₁, …, u_k) ↦ Σᵢ F^{k−1−i} G uᵢ₊₁`.
* The carried modules are copied without change apart from the namespace and module docstrings.
  The corrections they contain belong to Chapters 1–3, are recorded in their module docstrings,
  and are not repeated here.

## Not formalised

* **The heuristic of pp. 79–80.** A chain started in the non-absorbing part `D` is either absorbed
  or leaves every finite subset of `D`. The book makes this rigorous only in Proposition 8.3.1.
  The decomposition (4.5) itself is formalised.
* **The AR(k) explosion heuristics of p. 90.** If the roots of `A(z)` lie outside the closed unit
  disk, the chain reaches `[−1, 1]` from every initial condition. A root in the open unit disk
  makes it explode. The deterministic-control analogy with the dam model is also not formalised.
  For AR(1) both cases are formalised (`ar1_uniform_isPhiIrreducible`,
  `ar1_explosive_not_irreducible`).
* **(4.15)–(4.16) as moments.** The mean `F^k x₀` and the variance `Σ_k` of `X_k`, and the
  Gaussian form of `Pᵏ(x, ·)` with the density (4.18). The proof of Proposition 4.4.3 does not
  use them. `Σ_k` is formalised as a matrix, with `Σ_k = C_k C_kᵀ`, `rank Σ_k = rank C_k` and
  the same range as `C_k` (`range_gramian`).
* **The storage model with `R = ∞`** (p. 88). It is `μ_Leb`-irreducible when the inter-input
  times have a density. The book only sketches this, "by modifying the 'turning off'
  construction". That the empty state is never reached is formalised.
* **The commentary of §4.5** (pp. 93–95).
* **The Doeblin decomposition (4.8) on a general space** (p. 81). It is not a precise claim: the
  remainder `D` is "in some sense ephemeral", and the book declines to discuss such
  decompositions. On a countable space the decomposition (4.5) is one, with countably many
  absorbing classes (`countable_absorbing_classes`); that version is formalised.
* **Other heuristics and remarks.** These are the introductory discussion (pp. 75–76), the
  interpretation of the queueing examples (p. 77) and the block matrix of Figure 4.1. In the
  storage models of p. 88, the following are not formalised: the one-step "turning off"
  construction for the simple storage model, irreducibility for measures other than `δ₀`, and the
  evanescence of the model with deterministic input times (Chapter 9).
