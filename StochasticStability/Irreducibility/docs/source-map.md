# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 4, pp. 75–95. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.Irreducibility`. Names marked "carried" are in the modules
copied from the Chapter 1–3 projects (see the [README](../README.md)). Where the Lean statement
departs from the book, see [corrections](corrections.md).

## Chapter 4 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 75 | Irreducibility: all parts of the space can be reached, whatever the starting point | Not formalised (heuristic) |
| Theorem 4.0.1, (4.1), p. 75 | If some `φ` satisfies (4.1), `φ(A) > 0 ⇒ L(x, A) > 0` for every `x`, there is an essentially unique maximal irreducibility measure `ψ` with (i) `ψ(A) > 0 ⇒ L(x, A) > 0`; (ii) `ψ(A) = 0 ⇒ ψ(Ā) = 0`, `Ā = {y : L(y, A) > 0}`; (iii) if `ψ(Aᶜ) = 0` then `A = A₀ ∪ N` with `N` `ψ`-null and `A₀` absorbing | (4.1) is `IsPhiIrreducible`. `theorem_4_0_1` (for `φ ≠ 0`), `theorem_4_0_1_unique`; the zero measure: `proposition_4_2_2_zero_counterexample` |
| p. 75 | "Maximal": `φ ≪ ψ` for every `φ` satisfying (4.1) | `IsMaximalIrreducibility`, `ac_maxIrrMeasure`, `IsMaximalIrreducibility.isPhiIrreducible_iff` |
| p. 76 | A regeneration point `α` reached from everywhere gives (4.1) with `φ = δ_α` | `isPhiIrreducible_dirac_iff` |
| p. 76 | State space models whose noise has a density satisfy (4.1) with `φ` Lebesgue measure on an open set | §4.3.3 and §4.4 below; the general claim is Chapter 7's, not formalised |
| p. 76 | The value of (ii) and (iii); communication precedes irreducibility | Not formalised (heuristic) |

## §4.1.1 Communication: random walk on a half line

| Source | Claim | Lean |
| --- | --- | --- |
| (4.2)–(4.3), p. 76 | `Φₙ = [Φₙ₋₁ + Wₙ]⁺` on `ℤ₊` with integer increments: `P(x, y) = P(W₁ = y − x)` for `y > 0`, `P(x, 0) = P(W₁ ≤ −x)` | `rwhlMatrix`, `isTransitionMatrix_rwhlMatrix` (carried); the chain is `matKernel (rwhlMatrix Γ)` |
| p. 76 | `{0}` is reached in one step when `Γ` has an infinite negative tail | `rwhl_zero_ge` (`P(x, 0) ≥ Γ(w)` for `w ≤ −x`) |
| (4.4), p. 77 | If `Γ(w) = δ > 0` for some `w < 0`, then `Pₓ(Φₙ = 0) ≥ δⁿ` after `n ≥ \|x/w\|` steps, so `{0}` is always reached | `rwhl_pow_zero_ge`, `rwhl_hitProb_zero_pos` |
| p. 77 | If `P(Wₙ < 0) = 0`, `{0}` is reached from no `x ≠ 0`; hence `L(x, 0) > 0` for all states or for none | `rwhl_hitProb_zero_eq_zero`. The dichotomy fails at `x = 0`: `diracZeroInt`, `rwhl_dichotomy_counterexample` |
| p. 77 | If `P(W = y) > 0` for all `y`, every state is reached from every state at the next step | Not stated separately; a positive entry gives `x → y` (`leads_of_pos`) |
| p. 77 | Increments on the even integers, `P(W = 2y) > 0`: no odd state is reached from an even one, while from an odd state every state is reached, through `{0}`; `ℤ₊ = ℤ₊⁰ ∪ ℤ₊¹` | `rwhl_even_increments` (the even states are absorbing) |
| p. 77 | The GI/M/1 and M/G/1 chains of §2.4.2 have the structure (4.3); reaching `{0}` means the queue empties; design implications of even batches | GI/M/1: `giM1Matrix`, `giM1Increment`, `giM1Matrix_eq_rwhl`, `proposition_3_3_1` (carried); M/G/1: `mG1Matrix`, `proposition_3_3_2` (carried). The interpretation is not formalised |

## §4.1.2 Communicating classes and irreducibility

| Source | Claim | Lean |
| --- | --- | --- |
| p. 78 | `x → y` if `L(x, y) > 0`, with `x → x` by convention; `x ↔ y` if `x → y` and `y → x` | `Leads`, `Communicates`, `Leads.refl`; `L(x, A)` is `hitProb` (carried) |
| p. 78 | Equivalently, `Pⁿ(x, y) > 0` and `Pᵐ(y, x) > 0` for some `n, m ≥ 0` | `leads_iff_exists_pow`. For sets: `hitProb_pos_iff`, `pow_le_hitProb`, `hitProb_le_one`, `potKernel_pos_iff`, `firstReturn_ne_top_eq_iUnion` |
| Proposition 4.1.1, p. 78 | `↔` is an equivalence relation; the classes `C(x) = {y : x ↔ y}` cover `X`, with `x ∈ C(x)` | `proposition_4_1_1`, `commClass`, `mem_commClass_self`, `iUnion_commClass`, `commClass_eq_or_disjoint`, `commClass_eq_iff` |
| (3.23), p. 78 | `P^{n+m}(x, z) ≥ Pⁿ(x, y) Pᵐ(y, z)`, so `→` is transitive | `pow_add_singleton_ge`, `Leads.trans`; the positivity form for sets: `pow_add_pos_iff`, `measurableSet_pow_pos` |
| p. 78 | `X` is irreducible if `C(x) = X` for some `x`; `C(x)` is absorbing if `P(y, C(x)) = 1` for `y ∈ C(x)` | `IsIrreducibleChain`, `isIrreducibleChain_iff` (all states communicate); `IsAbsorbing`, `IsAbsorbing.pow_apply`, `IsAbsorbing.pow_compl`, `IsAbsorbing.hitProb_compl`, `IsAbsorbing.hitProb_eq_zero` |
| p. 78 | Some `y ∉ C(x)` has `x → y` iff `C(x)` is not absorbing | `not_isAbsorbing_commClass_iff`, with `exists_singleton_pos_of_pos`, `measurableSet_of_countable` |
| (4.5), Figure 4.1, pp. 78–79 | `X = ⋃_{x ∈ I} C(x) ∪ D`, a disjoint union of the absorbing classes and the states `D` in no absorbing class | `nonAbsorbingPart`, `commClass_subset_nonAbsorbingPart`, `decomposition_4_5`, `decomposition_4_5_disjoint`; there are countably many absorbing classes (`countable_absorbing_classes`). The block matrix of Figure 4.1 is not formalised |
| Proposition 4.1.2, p. 79 | For an absorbing class `C`, the matrix `P_C` defines an irreducible chain `Φ_C` on `C` | `proposition_4_1_2`; `restrictKernel`, `restrictKernel_apply`, `isMarkovKernel_restrictKernel`, `restrictKernel_pow_apply`; the chain is built by Theorem 3.2.1 (`theorem_3_2_1`, carried) |
| pp. 79–80 | Started in `D`, the chain is either absorbed or leaves every finite subset of `D` | Not formalised (heuristic; the book makes it rigorous in Proposition 8.3.1) |

## §4.1.3 Irreducible models on a countable space

| Source | Claim | Lean |
| --- | --- | --- |
| p. 80 | Conditions on `P` itself usually ensure irreducibility | For matrix chains: `matKernel_pow_one_singleton`, `leads_of_pos`, `Leads.step`, `isAbsorbing_matKernel_iff`, `IsAbsorbing.mem_of_leads` |
| (4.6)–(4.7), p. 80 | For the forward recurrence time chain, with `r = sup(n : p(n) > 0)`, `A = {1, …, r}` is absorbing, and the chain restricted to `A` is irreducible: `P^{x−y}(x, y) = 1` and `P^{y+r−x}(y, x) ≥ p(r)` | `fwdRecMatrix` (carried), `fwdRec_isAbsorbing`, `fwdRec_leads_down`, `fwdRec_pow_down`, `fwdRec_communicates` (for finite `r`; see [corrections](corrections.md)) |
| p. 80 | GI/M/1: `P(x, x + 1) = p₀ > 0` and `P(x, 0) > 0`, so `P^{y+1}(x, y) > 0`; the chain is irreducible "no matter what the distribution of the inter-arrival times" | `giM1_isIrreducibleChain`; for the Poisson weights of Proposition 3.3.1: `poissonWeight_ne_zero`, `giM1_poisson_isIrreducibleChain`. False for `G = δ₀`: `poissonWeight_dirac_zero`, `giM1_dirac_counterexample` |
| p. 80 | The M/G/1 chain `N*` is always irreducible | `mG1_isIrreducibleChain`, `mG1_poisson_isIrreducibleChain`. False for `H = δ₀`: `mG1_dirac_counterexample` |
| p. 81 | Random walk on `ℤ`: with `d` the g.c.d. of `{n : Γ(n) > 0}`, each `D_r = {md + r}` is absorbing | `rwMatrix` (carried), `rwSupportGroup`, `rw_closure_eq_zmultiples`, `rw_coset_isAbsorbing`; that the walk is then not irreducible (for `d ≥ 2`) is not stated separately |
| p. 81 | If `Γ(−∞, 0) > 0` and `Γ(0, ∞) > 0`, the walk is irreducible on each `D_r`, by Lemma D.7.4; finitely many irreducible absorbing classes | `rw_leads_add`, `rw_monoid_eq_group`, `rw_commClass_eq`, `rw_commClass_finite`; proved directly, without Lemma D.7.4 |
| p. 81 | The walk on `ℚ` with `P(Wₙ = x) > 0`, `x ∈ ℤ`: `C(q) = q + ℤ` is absorbing and irreducible, and there are countably infinitely many such classes | `arMatrix` (carried; the linear model of Proposition 3.3.3 with `α = 1`), `ratClass`, `ratWalk_isAbsorbing`, `ratWalk_commClass_eq`, `ratWalk_commClass_infinite` |

## §4.2.1 The concept of φ-irreducibility

| Source | Claim | Lean |
| --- | --- | --- |
| p. 81 | On a general space there is no analogue of `↔`; the Doeblin decomposition (4.8), with countably many absorbing sets `C(x)` and a remainder `D` "in some sense ephemeral" | On a countable space, (4.5) is such a decomposition: countably many absorbing classes, which together with `D` cover `X` (`countable_absorbing_classes`), disjoint by `decomposition_4_5_disjoint`. On a general space (4.8) is not formalised: it is not a precise claim, and the book declines to discuss it |
| p. 82 | `Φ` is φ-irreducible if `φ(A) > 0` implies `L(x, A) > 0` for all `x` | `IsPhiIrreducible`; every chain is `0`-irreducible: `isPhiIrreducible_zero` |
| (4.9), p. 82 | `K_{a_{1/2}}(x, A) = Σₙ Pⁿ(x, A) 2^{−(n+1)}`, a resolvent; `K_{a_{1/2}}(x, ·)` is a probability measure equivalent to `I(x, ·) + U(x, ·)` | `resolventHalf` (the resolvent `resolvent P 2⁻¹`, carried), `resolventHalf_apply`, `isMarkovKernel_resolventHalf`, `resolventHalf_pos_iff`, `resolventHalf_eq_zero_iff`, `resolventHalf_equiv` |
| Proposition 4.2.1, p. 82 | φ-irreducibility is equivalent to each of (i) `U(x, A) > 0`, (ii) `Pⁿ(x, A) > 0` for some `n > 0`, (iii) `K_{a_{1/2}}(x, A) > 0`, whenever `φ(A) > 0` | `proposition_4_2_1` |
| p. 82 | Proof: if `L(x, A) > 0` for all `x ∈ Aᶜ`, then for all `x`, by `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)` | `hitProb_pos_of_compl`, with `hitProb_first_step` (carried) |

## §4.2.2 Maximal irreducibility measures

| Source | Claim | Lean |
| --- | --- | --- |
| p. 82 | Any restriction of an irreducibility measure is an irreducibility measure | `IsPhiIrreducible.restrict`; more generally `IsPhiIrreducible.mono` (`φ' ≪ φ`) |
| p. 82 | On a countable space, if `x → x*` for every `x`, the chain is `δ_{x*}`-irreducible | `isPhiIrreducible_dirac_of_leads`, `isPhiIrreducible_dirac_iff` |
| p. 83 | For a chain irreducible in the sense of §4.1, counting measure is the maximal irreducibility measure | `isIrreducibleChain_iff_count`, `isMaximalIrreducibility_count` |
| Proposition 4.2.2, p. 83 | If `Φ` is φ-irreducible, there is a probability measure `ψ` with (i) `Φ` is `ψ`-irreducible; (ii) `Φ` is `φ'`-irreducible iff `ψ ≫ φ'`; (iii) `ψ(A) = 0 ⇒ ψ{y : L(y, A) > 0} = 0`; (iv) `ψ` is equivalent to `ψ'(A) = ∫ φ'(dy) K_{a_{1/2}}(y, A)` for every finite irreducibility measure `φ'` | `proposition_4_2_2` (for `φ ≠ 0`, and in (iv) for nonzero `φ'`), `proposition_4_2_2_maximal`; the zero measure: `proposition_4_2_2_zero_counterexample` |
| p. 83 | Without loss of generality `φ(X) = 1`: an equivalent probability measure is an irreducibility measure | `exists_finite_equiv_of_ac`, `exists_prob_equiv`, `IsPhiIrreducible.mono` |
| (4.10), p. 83 | `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)` is a probability measure | `maxIrrMeasure`, `maxIrrMeasure_apply`, `maxIrrMeasure_univ`, `isProbabilityMeasure_maxIrrMeasure` |
| p. 83 | Proof of (i), through `Ā(k)` and the Chapman–Kolmogorov equations | `isPhiIrreducible_maxIrrMeasure`, with `setOf_resolventHalf_pos`, `setOf_hitProb_pos`, `measurableSet_hitProb_pos`, `exists_measure_pos_of_iUnion` |
| p. 84 | Proof of (ii) | `ac_maxIrrMeasure`, `isMaximalIrreducibility_maxIrrMeasure`, `IsMaximalIrreducibility.isPhiIrreducible_iff` |
| p. 84 | Proof of (iv): any two maximal irreducibility measures are equivalent | `IsMaximalIrreducibility.equiv`, `IsMaximalIrreducibility.of_equiv` |
| p. 84 | `∫ ψ(dy) Pᵐ(y, A) 2⁻ᵐ ≤ ψ(A)`, from which (iii) follows | `maxIrrMeasure_comp_pow_le`, `maxIrrMeasure_hitSet_null`, `IsMaximalIrreducibility.hitSet_null` |
| p. 84 | ψ-irreducibility notation: (i) ψ-irreducible, with `ψ` maximal; (ii) `B⁺(X)`, uniquely defined; (iii) full sets; (iv) absorbing sets | (i) `IsMaximalIrreducibility`; (ii) `posSets`, `posSets_eq_of_maximal`; (iii) `IsFull`; (iv) `IsAbsorbing` |
| Proposition 4.2.3, pp. 84–85 | If `Φ` is `ψ`-irreducible, (i) every absorbing set is full; (ii) every full set contains a non-empty absorbing set | (i) `proposition_4_2_3_i` (non-empty absorbing sets), and the empty set: `proposition_4_2_3_i_counterexample`; (ii) `proposition_4_2_3_ii` (the absorbing set is also full) |
| Theorem 4.0.1, proof, p. 75 | (i) and (ii) by Proposition 4.2.2, (iii) by Proposition 4.2.3 | `theorem_4_0_1` |
| p. 85 | An absorbing ψ-irreducible set | `IsAbsorbingIrreducibleSet` |
| Proposition 4.2.4, p. 85 | For an absorbing set `A`, `P_A` defines a chain `Φ_A` on `A` (Theorem 3.4.1); if `Φ` is `ψ`-irreducible, so is `Φ_A` | `proposition_4_2_4`, `proposition_4_2_4_nonzero`; `restrictKernel`, `restrictKernel_apply_eq`, `isMarkovKernel_restrictKernel`, `lintegral_restrictKernel`; the chain: `pathMeasure`, `theorem_3_4_1` (carried) |

## §4.2.3 Uniform accessibility of sets

| Source | Claim | Lean |
| --- | --- | --- |
| p. 85 | `x ↔ y` is not useful on an uncountable space; accessibility replaces it | Not formalised (heuristic) |
| (4.11), p. 86 | `B` is accessible from `A` if `L(x, B) > 0` on `A`; uniformly accessible, `A ⇝ B`, if `inf_{x ∈ A} L(x, B) ≥ δ > 0` | `IsAccessibleFrom`, `UnifAccessible`, `UnifAccessible.isAccessibleFrom` |
| p. 86 | `⇝` is non-reflexive in general | `unifAccessible_not_refl` (the chain on `Bool` that jumps to `false` and stays there: `{true}` is not even accessible from itself) |
| Lemma 4.2.5, p. 86 | If `A ⇝ B` and `B ⇝ C`, then `A ⇝ C`; the proof uses the taboo potential `U_B` of (3.34) | `lemma_4_2_5`, `hitProb_ge_mul`, `stoppedState_firstReturn_mem`. The proof uses the strong Markov property at `τ_B` (`strong_markov_lintegral`, carried) in place of `U_B` (`tabooPotKernel`, carried) |
| p. 86 | `Ā = {x : L(x, A) > 0}`, `Ā(m) = {x : Σ_{n=1}^m Pⁿ(x, A) ≥ m⁻¹}`, `A⁰ = {x : L(x, A) = 0} = [Ā]ᶜ` | `hitSet`, `hitSetLevel`, `measurableSet_hitSetLevel`, `noHitSet`, `noHitSet_eq_compl` |
| Lemma 4.2.6, pp. 86–87 | `Ā = ⋃ₘ Ā(m)` and `Ā(m) ⇝ A`, since `L(x, A) ≥ Pₓ(τ_A ≤ m) ≥ m⁻²` on `Ā(m)` | `lemma_4_2_6`, `lemma_4_2_6_bound` |
| p. 87 | For a ψ-irreducible chain, `X` has a countable cover by sets from which a given `A ∈ B⁺(X)` is uniformly accessible | `countable_cover_unifAccessible` |

## §4.3.1 Random walk on a half line

| Source | Claim | Lean |
| --- | --- | --- |
| p. 87 | Random walk on the half line `[0, ∞)` | `halfLineWalkKernel` (carried), on `ℝ≥0` |
| Proposition 4.3.1, (4.12), p. 87 | The walk is `φ`-irreducible with `φ = δ₀` iff `Γ(−∞, 0) > 0`; then `C ⇝ {0}` for every compact `C` | `proposition_4_3_1`, `proposition_4_3_1_compact` |
| p. 87 | Proof: necessity is trivial; if `Γ(−∞, −ε) > δ`, then `Pⁿ(x, {0}) ≥ δⁿ` for `x/ε < n`, and `Pₓ(τ₀ ≤ c/ε) ≥ δ^{1+c/ε}` on `[0, c]` | `halfLine_hitProb_zero_eq_zero`, `exists_Iio_neg_pos`, `halfLine_pow_zero_ge` |
| p. 87 | φ-irreducibility is often easy to check, but says little about the motion of the chain | Not formalised (heuristic) |
| p. 87 | `ψ(A) = Σₙ Pⁿ(0, A) 2⁻ⁿ` is a maximal irreducibility measure | `halfLine_maximal` |

## §4.3.2 Storage models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 88 | Proposition 4.3.1 gives ψ-irreducibility of the simple storage model when `P(Sₙ − Jₙ < 0) > 0` | `proposition_4_3_1` with `Γ` the law of `Sₙ − Jₙ`; the reduction of the storage model to random walk on a half line is in the `MarkovModels` project |
| p. 88 | Turning off the input for longer than `s/r` gives δ₀-irreducibility in one step; infinite tails suffice | Not formalised for the simple model; the content-dependent case is below |
| p. 88 | Deterministic integer input times with inputs above unity: not irreducible, and evanescent | That it is not δ₀-irreducible is the "only if" part of `proposition_4_3_1` (`halfLine_hitProb_zero_eq_zero`), since then `Γ(−∞, 0) = 0`; irreducibility for other measures and evanescence (Chapter 9) are not formalised |
| (2.32), p. 88 | Content-dependent release: if `R(x) < ∞` and `P(Tᵢ > R(x)) > 0` for all `x`, the model is δ₀-irreducible | `inputKernel`, `inputKernel_apply`, `isMarkovKernel_inputKernel`, `contentPreInputKernel`, `isMarkovKernel_contentPreInputKernel`, `contentPreInput_zero_pos`, `contentPreInput_isPhiIrreducible` |
| p. 88 | If `R(x) = ∞`, the empty state is never reached and the construction fails | `contentPreInput_hitProb_zero`, `contentPreInput_not_isPhiIrreducible` |
| p. 88 | With `R = ∞` and inter-input times with a density, the model is still `μ_Leb`-irreducible | Not formalised (sketched only in the book) |
| p. 88 | Exact conditions for φ-irreducibility are unknown | Not formalised (not a mathematical claim) |

## §4.3.3 Unrestricted random walk

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 88–89 | `Γ ≥ γ(x) dx` with `γ ≥ δ > 0` on `\|x\| < β`; for `C = [−β/2, β/2]`, `P(x, B) ≥ δ μ_Leb(B)` when `x ∈ C`, `B ⊆ C` | `randomWalkKernel` (carried), `le_of_density`, `randomWalk_step_ge` |
| p. 89 | `C` is reached from every `x` in at most `2\|x\|/β` steps, so `μ_Leb` restricted to `C` is an irreducibility measure | `randomWalk_isPhiIrreducible_Icc`; on `(−β, β)`: `randomWalk_isPhiIrreducible_of_density`, from `isPhiIrreducible_of_local_density` and `exists_pow_pos_of_reach` |
| (RW2), p. 544 (not in §4.3.3) | Spread-out increments: some convolution power has such a density | `randomWalk_isPhiIrreducible_of_convPow`, `isPhiIrreducible_of_skeleton`; `convPow`, `IsSpreadOut` (carried) |
| p. 89 | `Γ` on `ℚ` with `Γ(r) > 0`: every `x + ℚ` is absorbing, and there are uncountably many absorbing irreducible sets | `ratCoset`, `randomWalk_rational` |
| p. 89 | ψ-irreducibility excludes this behaviour | `not_isPhiIrreducible_of_disjoint_absorbing` (two disjoint non-empty absorbing sets allow no nonzero irreducibility measure) |

## §4.4.1 Scalar models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 89 | AR(k), (AR1), in the Markovian form (2.1) | `arKernel`, `companion`, `firstUnit`, `arKernel_eq_lssMatrixKernel` (carried) |
| p. 89 | With an everywhere positive innovation density, AR(k) is `μ_Leb`-irreducible whatever `α₁, …, α_k` | `ar_isPhiIrreducible`, for an innovation law equivalent to Lebesgue measure (with `map_fin_one_equiv`): `φ`-irreducible for every `φ ≪ μ_Leb`, Lebesgue measure maximal, and `A ⇝ B` for compact `A` and `μ_Leb(B) > 0`; it combines `proposition_4_4_2`, `proposition_4_4_3` and `arKernel_eq_lssMatrixKernel` |
| p. 89 | AR(1) with `W` uniform on `[−1, 1]` and `\|α₁\| ≤ 1` is `μ_Leb^{[−1,1]}`-irreducible, as for random walk | `ar1_uniform_isPhiIrreducible`; for any local density: `ar1_isPhiIrreducible_of_density`, `isPhiIrreducible_of_local_density`; `ar1Kernel` (carried) |
| p. 89 | If `\|α₁\| > 1`, from an initial state above `(\|α₁\| − 1)⁻¹` the chain explodes monotonically and is not irreducible | `ar1_abs_lt_step`, `ar1_explosive_not_irreducible` |
| p. 90 | If the zeros of `A(z)` lie outside the closed unit disk, the chain reaches `[−1, 1]` from every initial condition; a root in the open unit disk makes it explode | Not formalised (heuristic) |
| p. 90 | The analogy with the dam model: drive the chain deterministically towards a centre | Not formalised (heuristic) |

## §4.4.2 Communication for linear control models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 90 | LCM(F, G) is controllable if every state `x` is reached from every `x₀` by some controls | `lcmTrajectory`, `IsControllable` (carried) |
| (LCM3), (4.13), p. 90 | The controllability matrix `C_n = [F^{n−1}G \| ⋯ \| FG \| G]`; `(F, G)` is controllable if `rank C_n = n` | `ctrbMatrix`, `ctrbMap`, `ctrbMap_apply`, `ctrbMatrix_mulVec`, `range_ctrbMatrix`, `rank_ctrbMatrix_eq_iff`, `IsCtrbRank` |
| pp. 90–91 | Cayley–Hamilton: `(F, G)` is controllable iff `rank C_k = n` for some `k` | `pow_dim_eq_sum`, `pow_mul_mulVec_mem_range`, `pow_mul_mulVec_mem_range_n`, `range_ctrbMap_le_n`, `range_ctrbMap_mono`, `isControllable_iff_rank`, `isControllable_iff_exists_rank`, `range_ctrbMap_eq_top` |
| Proposition 4.4.1, (4.14), p. 91 | Under (LCM3), LCM(F, G) is controllable: `x_k = F^k x₀ + C_k (u₁, …, u_k)` and `C_k` is onto | `proposition_4_4_1` (every state in `n` steps), `lcmTrajectory_eq_ctrbMap`, `reach_of_range_eq_top` |
| Proposition 4.4.2, p. 91 | The control model of AR(k) in the form (2.1) is controllable: `C_n` is triangular, with `η₀ = 1` and `η_j = Σᵢ αᵢ η_{j−i}` | `proposition_4_4_2`, `firstVec`, `firstUnit_mulVec`, `companion_mulVec_of_ne_zero`, `companion_mulVec_zero`, `companion_pow_firstUnit_triangular`, `companionEta`, `companion_eta_rec` |

## §4.4.3 Gaussian linear models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 92 | LSS(F, G) is ψ-irreducible when LCM(F, G) is controllable and the noise allows a full cross-section of controls | `lssMatrixKernel` (carried); see Proposition 4.4.3 |
| (LSS3), p. 92 | `W ∼ N(0, I)` on `ℝᵖ` | The product of `p` standard normal laws; `stdGaussian_equiv_volume` (it is equivalent to Lebesgue measure) |
| p. 92 | If `p = n` and `G` has full rank, the scalar argument gives `μ_Leb`-irreducibility | `isControllable_of_rank_G` (`(F, G)` is then controllable, in one step), `lss_fullRank_G_irreducible` (Gaussian noise: `φ`-irreducible for every `φ ≪ μ_Leb`, Lebesgue measure maximal) |
| Proposition 4.4.3, p. 92 | For a Gaussian LSS(F, G) with controllable LCM(F, G): `φ`-irreducible for every non-trivial `φ` with a density; Lebesgue measure is maximal; `A ⇝ B` for compact `A` and `μ_Leb(B) > 0` | `proposition_4_4_3` (noise equivalent to Lebesgue measure), `proposition_4_4_3_gaussian`; the parts: `lss_isPhiIrreducible`, `lss_isMaximalIrreducibility`, `lss_unifAccessible` |
| p. 92 | Proof: `Pᵏ(x, ·)` has an everywhere positive density | `ctrbLaw`, `lss_pow_eq`, `ctrbLaw_equiv`, `lss_pow_equiv`, `pi_absolutelyContinuous`, `measurable_ctrbMap`; for (iii): `translateCM`, `lss_lowerSemicontinuous` |
| (4.15)–(4.16), pp. 92–93 | `E_{x₀}[X_k] = F^k x₀`, and the variance is `Σ_k = Σ_{i<k} F^i G Gᵀ (F^i)ᵀ` | `gramian` (`Σ_k` as a matrix), `gramian_eq` (`Σ_k = C_k C_kᵀ`), `rank_gramian`. As moments of `X_k` they are not formalised |
| p. 93 | `Σ_k` has rank `n` for some `k` iff `(F, G)` is controllable, and then for `k = n` | `isControllable_iff_gramian` |
| (4.17), p. 93 | The controllability grammian `Σ_{i ≥ 0} F^i G Gᵀ (F^i)ᵀ` | `gramian_series_counterexample` |
| (4.18), p. 93 | `Pᵏ(x, dy) = p_k(x, y) dy` with `p_k(x, y) = (2π\|Σ_k\|)^{−k/2} exp{−½ (y − F^k x)ᵀ Σ_k⁻¹ (y − F^k x)}` | `density_4_18_counterexample`; the Gaussian form of `Pᵏ(x, ·)` is not formalised |
| p. 93 | Positive densities are a sledge hammer; Chapter 7 relaxes them | Not formalised (commentary) |
| p. 93 | `X₀`, the range of `C_n` (and of the grammian), is absorbing: `x₀ ∈ X₀ ⇒ Fx₀ + Gw₁ ∈ X₀` | `ctrbSubspace`, `measurableSet_ctrbSubspace`, `pow_mulVec_mem_ctrbSubspace`, `ctrbMap_mem_ctrbSubspace`, `ctrbSubspace_absorbing_step`, `ctrbSubspace_isAbsorbing`. The range of `Σ_k` is that of `C_k` (`range_gramian`), so the range of `Σ_n` is `X₀` (`range_gramian_n`) |
| p. 93 | The restricted process is a linear state space model on `X₀` with a controllable pair `(F₀, G₀)`, hence `μ_Leb`-irreducible | `ctrbF₀`, `ctrbG₀`, `coe_ctrbStep`, `restrictKernel_eq_lssKernel` (it is `lssKernel`, carried), `ctrbMap₀`, `ctrbMap₀_surjective`, `coe_controlMap_ctrb`, `restricted_controllable`, `restricted_pow_eq_zero_iff`, `restricted_isPhiIrreducible`, `restricted_isMaximalIrreducibility`, `restricted_irreducible`, `restricted_irreducible_gaussian`. `dim X₀ = rank C_n` (`finrank_ctrbSubspace`), and `dim X₀ < n` when `(F, G)` is not controllable (`finrank_ctrbSubspace_lt`) |

## §4.5 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 93–95 | History; other notions of irreducibility (equal null sets of `K_{1/2}(x, ·)`, irreducibility from `φ`-almost every `x`); the Doeblin decomposition; practical verification; the link with Chapter 7 | Not formalised (commentary) |
