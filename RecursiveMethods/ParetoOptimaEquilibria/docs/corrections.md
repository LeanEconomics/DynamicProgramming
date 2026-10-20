# Corrections and conventions

Places where a Lean statement differs from the book: a claim corrected, a gap in a proof closed,
a hypothesis made explicit, or a convention chosen. Every false claim below has a Lean
counterexample.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| p. 444 | Convexity of the upper contour set `A` is equivalent to concavity of `U`. | Only quasi-concavity follows: `U(l, c) = l³` has convex upper contour sets on `ℝ²` and is not concave (`intro_concavity_counterexample`). |
| Theorem 15.2, p. 450 | Convex `A`, `B` with `B̊ ≠ ∅` and `A ∩ B̊ = ∅`, or `S` finite dimensional and `A ∩ B = ∅`, are separated by a nonzero `φ` and a constant `c`. | False: `A = ∅`, `B = ℝ` (`theorem_15_2_counterexample`, against the book's statement `BookTheorem15_2`); in the finite-dimensional case `A = ℝ`, `B = ∅` (`theorem_15_2_counterexample_finiteDimensional`). Proved with `A ≠ ∅`, and `B ≠ ∅` in the finite-dimensional case (`theorem_15_2`). In Theorem 15.4 both sets are nonempty (`preferredSum_nonempty`). |
| Example 4, p. 449 | `L₁(Z, 𝒵, μ)* = L∞(Z, 𝒵, μ)`. | False without σ-finiteness: for one point of mass `∞` (`infAtom`), `L₁ = {0}` and `L∞ ≅ ℝ` (`l1_dual_counterexample`), and `y ↦ (x ↦ ∫ y x dμ)` is not injective (`l1_dual_pairing_counterexample`). Proved for σ-finite `μ` (`l1_dual_sigmaFinite`). |
| p. 450 | `μ(A) > 0` for all `A ∈ 𝒵`. | Impossible, since `μ(∅) = 0` (`positive_measure_counterexample`). Read as all nonempty `A`, that is `μ{n} > 0` (`example_15_4_linf_nat`). |
| p. 458 | Under Assumptions 15.1–15.5 the competitive equilibrium allocations and the Pareto-optimal allocations coincide exactly. | Both inclusions fail. The Figure 15.3 economy satisfies 15.1–15.5 and local nonsatiation and has a Pareto optimum that is a competitive equilibrium at no price (`paretoOptimal_not_ce_counterexample`). Two consumers with `u(v) = min(v, 0)` on `ℝ` give a competitive equilibrium that is not Pareto optimal (`ce_not_paretoOptimal_counterexample`). Corrected: competitive equilibria are Pareto optimal under local nonsatiation; a Pareto optimum is supported by a nonzero price under 15.1–15.5, and is a competitive equilibrium when that price leaves every consumer a cheaper point (`welfare_theorems_corrected`). |
| Exercise 15.10(b), p. 465 | For `U` bounded with Assumptions 15.2 and 15.3 on `C`, `u(x) = Σ_t βᵗ U(x_t)` satisfies 15.2, 15.3 and 15.7. | False for 15.2: `C = [0, 2]`, `U(c) = c²`, `β = 1/2`, `x = (2, 0, 0, …)`, `x′ = (0, 2, 0, …)` give `u(x) = 4 > u(x′) = 2` and `u((x + x′)/2) = 3/2` (`ex_15_10b_counterexample`). With `U` concave all three hold (`ex_15_10b`). 15.7 needs only `U` bounded (`ex_15_10b_tail`), and 15.3 holds if `U` is also continuous (`ex_15_10b_continuousOn`). |
| Exercise 15.10(c), p. 465 | For an aggregator in the sense of §5.11, the fixed point `u_W` satisfies 15.2, 15.3 and 15.7. | False for 15.2 under (W1)–(W3) alone: `W(c, z) = min(c, 2)² + z/2` (`ex_15_10c_counterexample`). True if `W` is also concave, (W5) (`ex_15_10c`); the manual uses this silently through Exercise 5.11d. (W4) is not needed: a nonnegative concave function on `[0, ∞)` is nondecreasing (`seq_monotoneOn_of_concave_nonneg`). 15.3 and 15.7 hold under (W1)–(W3) (`ex_15_10c_tail`). |
| Exercise 15.11(b), p. 465 | Under 15.6, Assumption 15.7 holds iff `u(x) = lim_T u(xᵀ)` for all `x`. | The "if" is true (`ex_15_11b_if`); the "only if" is false. On `X = ℓ∞`, `u(x) = Σ_t (1/2)ᵗ x_t − limsup_t \|x_t\|` satisfies 15.1–15.3, 15.6 and 15.7, but `u(1ᵀ) → 2 ≠ 1 = u(1)` (`ex_15_11b_counterexample`). Corrected: for `X` convex with 15.6 and `u` continuous on `X`, 15.7 holds iff `liminf_T u(xᵀ) ≥ u(x)` for every `x ∈ X` (`ex_15_11b_liminf`). |
| Exercise 15.11(b) (manual) | 15.7 implies that `lim_T u(xᵀ)` exists and is `≥ u(x)`. | The limit need not exist: `u(x) = Σ_t (1/2)ᵗ x_t − limsup_t \|x_t\| − sup_t (x_{2t+1} − x_{2t+2})⁺` satisfies 15.1–15.3, 15.6 and 15.7, and `u(1ᵀ)` oscillates (`oddDrop`, `oscillatingUtility`, `ex_15_11b_manual_counterexample`). The manual's existence step applies 15.7 to the pair `(x^{T̂}, x̂)`, which says nothing about `u(xᵀ)`. Its inequality `liminf_T u(xᵀ) ≥ u(x)` is correct (`ex_15_11b_liminf`). |
| Exercise 15.12, p. 469 | For `Uᵢ` with Assumptions 15.2 and 15.3, `uᵢ(x) = ∫ Uᵢ(x(z)) dμᵢ(z)` satisfies 15.2, 15.3 and 15.9. | False for 15.2: `Z = {0, 1}`, `μ = μᵢ` uniform, `U(c) = c³`, `x = (2, 0)`, `x′ = (0, 1.9)`, `θ = 1/2` (`ex_15_12_counterexample`); the manual concedes this. With `Uᵢ` concave all three hold (`ex_15_12_assumption15_2`, `ex_15_12`). 15.3 and 15.9 hold for every continuous `Uᵢ` (`ex_15_12_assumption15_3`, `ex_15_12_assumption15_9`). |
| Exercise 15.3 (manual) | `Σ yₙ xₙ` converges because `Σ yₙ` converges and `x` is bounded. | Not enough: `yₙ = (−1)ⁿ/(n + 1)`, `xₙ = (−1)ⁿ` (`ex_15_3_manual_counterexample`). The proof uses `Σ \|yₙ\| < ∞` (`summable_mul_of_one_inf`). |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Example 4, pp. 449–450 | `L_p* = L_q` for `1 ≤ p < ∞` on any measure space (stated without proof). | `p = 1`: `μ` σ-finite (`l1_dual_sigmaFinite`; false without it, see above). `1 < p < ∞`: true for every measure, as the book says. For finite `μ` by Radon–Nikodym (`example_15_4`); for σ-finite `μ` by applying it to the finite measure `w·μ` for an integrable weight `w > 0` (`isDualRep_of_weight`, `example_15_4_sigmaFinite`); for arbitrary `μ` because every `u ∈ L_p` has σ-finite support (`exists_sigmaFinite_support`) and the representations on σ-finite sets agree and have norms bounded by `‖φ‖`, so a set maximising `∫ \|y_S\|^q` carries one representation for all `u` (`exists_preimage_pairLqLp_of_ne_top`, `example_15_4_general`). Injectivity and isometry hold for every `μ` (`pairLqLp_injective_of_ne_top`, `norm_pairLqLp_eq`). |
| Assumptions 15.7, 15.9, 15.9′, p. 465, pp. 468, 470 | `uᵢ(xᵀ)` (or `uᵢ(x^{A_n})`) is used without saying that `xᵀ ∈ Xᵢ`. | `SeqTailInsensitive` asks for `uᵢ(xᵀ) > uᵢ(x′)` only when `xᵀ ∈ Xᵢ`. In `Assumption15_9` and `Assumption15_9'` each `uᵢ` is defined on all of `S`; with Assumptions 15.8 and 15.8′ the truncations are eventually in `Xᵢ`. |
| Theorem 15.6, p. 466 | Assumptions 15.1–15.7. | Only 15.1, 15.2, 15.6 and 15.7 are used (`theorem_15_6`); 15.3 only for the equilibrium corollary (`theorem_15_6_competitiveEq`). |
| Theorem 15.6, p. 467 | "For any Pareto-optimal allocation" Theorems 15.4 and 15.6 give a supporting `ψ`; `ψ ≠ 0` is not asserted. | A strictly preferred point `x̂ᵢ` is needed for every consumer, not for one as in Theorem 15.4 (`theorem_15_6_of_supporting`). `ψ = 0` can happen: in an economy satisfying 15.1–15.7, the Pareto optimum `0` is supported by a `φ ≠ 0` whose regular part is zero, although the nonzero price `σ(x) = Σ_t (1/2)ᵗ x_t` also supports it (`theorem_15_6_counterexample`). The book's added cheaper-point condition for `ψ` excludes this (`seqRegularPart_ne_zero_of_cheaper`, `theorem_15_6_competitiveEq`). |
| Theorem 15.8, p. 469 | Assumptions 15.1–15.5, 15.8, 15.9; `ψ` from Lemma 15.7. | Only 15.1, 15.2, 15.8 and 15.9 are used. The conclusion holds for any `ψ(x) = lim_n φ(x^{A_n})` along any `A_n ↓ 0` (`theorem_15_8`); `theorem_15_8_inner_product` combines it with Lemma 15.7. A strictly preferred point is needed for every consumer, and `ψ ≠ 0` is not asserted. |
| Theorem 15.9, p. 470 | Assumptions 15.1–15.7, 15.8′, 15.9′. | Only 15.1, 15.2, 15.6, 15.7, 15.8′ and 15.9′ are used (`theorem_15_9`). A strictly preferred point is needed for every consumer, and `ν ≠ 0` is not asserted. |
| Exercise 15.10(c), p. 465 | `C = ℝⁿ₊`; `u_W` is the fixed point of `T_W` (Exercise 5.11d). | `C ⊆ E` is any convex set containing `0`. The fixed point is taken as given (`IsAggregatorFixedPoint`: bounded, continuous, nonnegative), not constructed. |
| Exercise 15.12, p. 469 | `μᵢ` a probability measure, `μᵢ ≪ μ`; `Xᵢ` satisfies 15.1 and 15.8. | `μᵢ` any finite measure with `μᵢ ≪ μ`. The conclusions hold on any `Xᵢ`. |
| Proof of Theorem 15.9, step 3, p. 472 | "Repeated application" of 15.8′ and 15.9′ gives one index `N(T)` for all periods `t ≤ T`. | The assumptions truncate one period along one sequence, so applied in turn they give indices that depend on the earlier truncations; a common index is not justified. The proof here uses iterated limits, one period at a time (`linftyTS_consumer_bound`, `linftyTS_firm_bound`). No model in which a common index fails is constructed. |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Proof of Theorem 15.1(b), p. 446 | "`‖x‖ ≤ 1/M` implies `φ(x) ≤ 1`". | The bound needed is `\|φ(x)\| ≤ 1`, and that is the one used (`theorem_15_1b`). |
| Proof of Theorem 15.4, step 1, p. 455 | `Aᵢ` and `Åᵢ` are convex "by Assumption 15.2". | 15.2 alone does not give this: `X = ℝ`, `u = 0` off `0`, `u(0) = −1` satisfies 15.1 and 15.2, but `{u ≥ u(1)} = ℝ ∖ {0}` (`assumption15_2_convex_counterexample`). With 15.3, `uᵢ` is quasi-concave (`quasiconcave_of_assumptions`) and both sets are convex (`convex_weaklyPreferred`, `convex_strictlyPreferred`). |
| Proof of Theorem 15.4, step 3, p. 456 | The separation extends from `Åₕ + Σ_{i≠h} Aᵢ` to `Σᵢ Aᵢ` "since `uₕ` is continuous". | Continuity of `uₕ` is not enough: `u(x) = x²(x² − 1)` on `ℝ` is continuous, has a strictly better point, and `0 ∈ {u ≥ u(0)} ∖ cl {u > u(0)}` (`continuity_closure_counterexample`). The reason is `Aₕ ⊆ cl Åₕ`, from 15.1, 15.2 and `x̂ₕ` (`weaklyPreferred_subset_closure`), with continuity of `φ` (`le_of_weaklyPreferred`). |
| Proof of Theorem 15.4, step 4, p. 456 | (3) and (4) "follow". | They need the separating constant to be `c = φ(Σᵢ xᵢ⁰) = φ(Σⱼ yⱼ⁰)`, which the book does not state. The separation is stated without a constant, and (3), (4) are derived by comparing with `Σᵢ xᵢ⁰ = Σⱼ yⱼ⁰`, which lies in both `Σᵢ Aᵢ` and `Y` (`theorem_15_4`). |
| Proof of Theorem 15.6, step 1, p. 466 | "By 15.1 and 15.2, `uᵢ(x^θ) > uᵢ(xᵢ⁰)`". | Immediate only when `uᵢ(x̂ᵢ) > uᵢ(x)`. A case split covers the rest without 15.3: if `uᵢ(x) > uᵢ(xᵢ⁰)`, 15.6–15.7 apply to `x` itself; if `uᵢ(x) = uᵢ(xᵢ⁰)`, then `uᵢ(x̂ᵢ) > uᵢ(x)` and 15.2 applies (`seq_support_step1_consumer`). |
| Proof of Theorem 15.8, p. 469 | The proof "parallels exactly that of Theorem 15.6". | Proved, by the same case split; the common argument for Theorems 15.6, 15.8 and 15.9 is `supportsAllocation_of_limit_bounds`. |
| Lemma 15.5 and (3), pp. 463–464 | The price sequence `(p_t)` in (3) is not shown to be summable. | `Σ_t \|p_t\| ≤ ‖φ‖` (`seqRegularPart_real`), and `Σ_t Σ_k \|p_{tk}\| ≤ ‖φ‖` for `ℝᴷ` with the max norm (`seqRegularPart_euclid`). The book's separate case `x = θ` is unnecessary. |
| Lemma 15.7, p. 468 | Stated without proof ("follows directly from" Yosida and Hewitt). | Proved directly for every finite `μ`, without `L∞* = ba(μ)` (`lemma_15_7`): the variation of `φ` on events (`linftyRestrictNorm`) gives a nested `A_n` along which `φ(x^{A_n})` is Cauchy (`exists_isLinftyTailSeq`, `IsLinftyTailSeq.limitDual`); the limit is a countably additive signed measure absolutely continuous with respect to `μ` (`IsLinftyTailSeq.limitSignedMeasure`), and Radon–Nikodym gives `p`. Also `‖ψ‖ ≤ ‖φ‖` and `ψ = φ` on every `x^{A_n}`. |
| Proof of Theorem 15.9, step 2, p. 471 | `ν(x) = Σ_t ν_t(x_t)` is called "the continuous linear functional `ν`". | Convergence and boundedness are proved: `Σ_{t<N} \|ν_t(x_t)\| ≤ ‖φ‖ ‖x‖_s` (from `sum_abs_linftyCoordDual_le`), so `ν` is continuous with `‖ν‖ ≤ ‖φ‖` (`linftySumDual`, `norm_linftySumDual_le`, `exists_linftyTimeState_decomposition`). |
| Proof of Theorem 15.9, steps 1 and 4, pp. 470–473 | Goes through the `ψ` of Theorem 15.6 on the time–state space. | (4) and (5) for `φ` are applied directly to the time- and event-truncated points, and step 4 is `supportsAllocation_of_limit_bounds`; the intermediate (10)–(11) are not needed. |
| Theorem 15.2, Examples 2 and 4 | Stated without proof (Luenberger). | Proved. The interior-point case of Theorem 15.2 is Mathlib's geometric Hahn–Banach theorem; the finite-dimensional case is proved here through the affine span of `A − B` (`theorem_15_2_finiteDimensional`). `ℓ_p* = ℓ_q` uses the test vectors `sgn(yᵢ)\|yᵢ\|^{q−1}` (`sum_rpow_le_of_dual_ellP`, `example_15_2`); for `L_p* = L_q` see `DualLp` (`example_15_4`). |
| Exercise 15.5(b) (manual) | The manual never checks that `ν` represents `φ`. | `φ(x) = ∫ x dν` is proved, with Mathlib's integral against a signed measure (`ex_15_5b`). |
| Exercise 15.10(b) (manual) | The proof of 15.3 takes one `δ` for every `t`. | That needs uniform continuity of `U`, which is not assumed. The proof here uses dominated convergence (`ex_15_10b_continuousOn`). |
| Exercise 15.12 (manual) | The proof of 15.3 takes one `δ` for every `z`; `μᵢ(⋂ Aₙ) = μ(⋂ Aₙ)`. | The first needs uniform continuity of `U` on a bounded interval, which holds for continuous `U` (`ex_15_12_assumption15_3`). The second should read `μ(⋂ Aₙ) = lim μ(Aₙ) = 0`, hence `μᵢ(⋂ Aₙ) = 0` by `μᵢ ≪ μ` (`ex_15_12_assumption15_9`). |
| p. 462 | "By Exercise 15.6 the positive orthant has no interior point". | Exercise 15.6 is about the box `{\|x_t\| ≤ 1}`. The claim is true and is proved directly (`weighted_orthant_no_interior`), and so no subset of the orthant, in particular `Y`, has an interior point (`weighted_no_interior_of_subset_orthant`). |

## Conventions

* `S*` is `StrongDual ℝ S`. The book's continuity of a linear functional is sequential
  (`SeqContAt`); `continuous_iff_seqContAt` identifies it with Mathlib's.
* In (1) the unit sphere is empty when `S = {θ}`. With Mathlib's `sSup ∅ = 0` the formula still
  holds, and `dual_norm_eq` has no nontriviality hypothesis.
* Sequence spaces are Mathlib's `lp` over `ℕ`, indexed from `0`. In the example of pp. 460–461,
  indexed `t = 1, 2, …` in the book, the book's period `t + 1` is index `t`. The stochastic
  re-reading on p. 462 then needs probabilities `β^{t−1}(1 − β)` for `t ≥ 1`
  (`hasSum_state_probabilities`, stated over `t ≥ 0`).
* `L_p(Z, 𝒵, μ)` is `MeasureTheory.Lp ℝ p μ`, and `L∞` is `Lp ℝ ⊤ μ`, one good. The book notes
  that Theorem 15.8 works for finitely many goods; only one good is formalised.
* Lemma 15.7, Theorems 15.8–15.9 and Exercise 15.12 use finite measures where the book uses
  probability measures.
* The extension of Lemma 15.5, Assumptions 15.6–15.7 and Theorem 15.6 to period-dependent spaces
  `X₀ × X₁ × …` (pp. 469–470) is formalised only for `X_t = L∞(μ^t)` (`LinftyTimeState`), as
  Theorem 15.9 needs.
* Consumers and firms are indexed by finite types. Each `uᵢ` is defined on all of `S`; only its
  values on `Xᵢ` matter, and Assumption 15.3 is continuity on `Xᵢ`.
* Exercise 15.6 is proved by the isometry `xₜ ↦ βᵗ xₜ` onto `ℓ₁` (`weightToEllOne`), which maps
  the box `B` onto `{z : \|zₜ\| ≤ βᵗ}` (`ex156Box`).
* Figure 15.3 is drawn, not specified. `fig153X`, `fig153U` and `fig153Y` are a concrete economy
  with its features: the endowment `ω = (1, 0)` is a single firm with `Y = {ω}`; consumer `0` has
  `X₀ = {v : v₁ ≥ 0}` and `u₀(v) = v₂`; consumer `1` has `X₁ = ℝ²` and `u₁(v) = v₁ − v₂²`.
* Exercise 15.11(b) is stated with `liminf_T u(xᵀ) ≥ u(x)` in the form: `c < u(x)` implies
  `c < u(xᵀ)` for all large `T`.
