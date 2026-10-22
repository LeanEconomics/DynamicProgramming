# Meyn and Tweedie, Chapter 15: Geometric Ergodicity, in Lean

This is the `StochasticStability/GeometricErgodicity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 15 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 362–391. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 15 asks for a geometric rate in the `f`-norm convergence of Chapter 14: some `r > 1` with
`Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f < ∞` (15.7). The tools are the generating functions of hitting times at
`r ≥ 1`: `E_x[r^{τ_A}]`, `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` and
`U_B^{(r)}(x, f) = E_x[Σ_{k=1}^{τ_B} f(Φ_k) rᵏ]` (15.12), (15.22). §15.1 works with an accessible
atom. Multiplying the Regenerative Decomposition by `rⁿ` and summing bounds the geometric sums by
three terms (15.8)–(15.11). Kendall's Theorem 15.1.1 says that a renewal sequence converges
geometrically fast exactly when its increment law has a geometric moment. Together they give the
geometric rate at a Kendall atom (Proposition 15.1.2), the full absorbing set
`{U_α^{(κ)}(·, f) < ∞}` (Proposition 15.1.3), and geometric ergodicity from an `f`-Kendall atom
(Theorem 15.1.4) or a geometrically ergodic atom (Theorem 15.1.5). §15.1.4 gives examples on
countable spaces. §15.2 extends Kendall atoms to Kendall sets, `sup_{x ∈ A} E_x[κ^{τ_A}] < ∞`, and
`f`-Kendall sets (15.22). A geometric trials argument shows that a petite `f`-Kendall set is
`f`-geometrically regular (Theorem 15.2.1). The geometric drift condition (V4), `ΔV ≤ −βV + b 1_C`
(15.28), is the dual notion. `G_C^{(κ)}(·, f)` solves (V4) (Lemma 15.2.3, Theorem 15.2.4). Under
(V4) for a petite set, every set on which `V` is bounded is `V`-geometrically regular (Lemma 15.2.2,
Theorems 15.2.5–15.2.7, Lemmas 15.2.8–15.2.9). §15.3 defines `f`-geometric regularity of the chain
(15.36). It is equivalent to an everywhere finite solution of (V4) (Propositions 15.3.1–15.3.2,
Theorem 15.3.3), and it passes between the chain and its skeletons (Theorems 15.3.4–15.3.7). §15.4
proves geometric ergodicity from a petite `f`-Kendall set through the split chain and a skeleton
(Theorem 15.4.1), the converse (Theorem 15.4.2) and a local criterion (Theorem 15.4.3). These
results make up the Geometric Ergodic Theorem 15.0.1: for a `ψ`-irreducible aperiodic chain, local
geometric convergence on a petite set (15.1), a petite Kendall set (15.2) and the drift (15.3) are
equivalent, and they give (15.4) with the same `V` on both sides. §15.5 applies (V4) to the
Bernoulli random walk on `ℤ₊`, the simple linear model and the scalar bilinear model. §15.6 is
commentary.

Every numbered result of Chapter 15 is formalised: Theorem 15.0.1, Theorem 15.1.1,
Propositions 15.1.2–15.1.3, Theorems 15.1.4–15.1.5, Theorem 15.2.1, Lemmas 15.2.2–15.2.3,
Theorems 15.2.4–15.2.7, Lemmas 15.2.8–15.2.9, Propositions 15.3.1–15.3.2, Theorems 15.3.3–15.3.7 and
Theorems 15.4.1–15.4.3. Kendall's Theorem 15.1.1 is proved in the carried renewal module
`KendallTheorem`, which comes from the Chapter 13 project `Ergodicity` (`theorem_15_1_1`); the
Chapter 15 modules use its directions (`kendall_geometric_bound`, `kendall_moment_of_geometric`,
`kendall_geometric_of_moment`). Eight claims are false as printed. Seven are refuted in Lean by a
counterexample of this project and one by an exact computation, and for each a corrected statement
is proved. Theorems 15.2.1 and 15.0.1 (ii) fail for `C = ∅`, which is petite and Kendall vacuously
(`theorem_15_2_1_counterexample`, `theorem_15_0_1_counterexample`). Theorem 15.2.7 needs `C` petite:
the whole space is always a Kendall set, and the null recurrent forward recurrence time chain of
`heavyRenewal` refutes the theorem as printed (`theorem_15_2_7_counterexample`). The identity in the
proof of Proposition 15.1.3 omits a term `−P(x, B)` (`proposition_15_1_3_counterexample`); the
corrected identity is `proposition_15_1_3_identity`. Theorem 15.1.4 needs aperiodicity: the period-2
flip chain on `Bool` has a `1`-Kendall atom and does not converge (`theorem_15_1_4_counterexample`);
(15.18) also holds only with the sum over `n ≥ 1`. The inequality (15.44) has the wrong sign
(`eq_15_44_counterexample`). In the `3 × 3` example of p. 371 the best rate for state `1` is exactly
`1/4` (`rateKernel_state_one`), and the printed `U^{(z)}(1, 1)` has the wrong `z²` coefficient
(`rateKernel_U11_counterexample`). The book's proof of Theorem 15.4.2 for chains without an atom has
a gap: its reduction to the split atom needs the `ν`-average of `x ↦ Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f` to be
finite, and it need not be. The statement is true, so there is no counterexample; it is proved by
another route (`theorem_15_4_2`, below). Smaller points of indexing and precision are corrected:
(15.20) for `j ≥ 1`, the rate on the right of (15.37) in Proposition 15.3.1, the bound in the proof
of Lemma 15.2.9, the bound of Theorem 15.4.1 with `G_C^{(κ)}`, and `V(x) = x² + 1` in §15.5.2.
Further points are made explicit without a counterexample of their own. `f` is measurable, and
`f ≥ 1` or `V ≥ 1` is assumed where the book's standing assumption is used; `b ≠ ∞` in (V4); the
state space is countably generated where petite sets are used; Theorem 15.3.4 (ii) takes `ψ(C) > 0`;
Theorem 15.4.2 assumes aperiodicity, an invariant probability in place of positive Harris
recurrence, and the sums only on a full set; Theorem 15.4.3 needs positivity, not positive Harris
recurrence; the linear and bilinear models take `ψ`-irreducibility, aperiodicity and petite compact
sets as hypotheses; and the Bernoulli walk takes `p > 0`. Two hypotheses are not needed.
Theorem 15.2.4 uses neither the `ψ`-irreducibility of the chain nor `C ∈ B⁺(X)`. Theorem 15.1.5,
whose proof the book omits as following the steps of Theorem 15.1.4, needs no aperiodicity: it
follows from `Pⁿ(α, α) → π(α) > 0`. Some statements are proved in a stronger form. Theorem 15.3.3
needs `V` finite at one point only; Theorem 15.4.1 also gives positivity and `π(f) < ∞`;
Theorem 15.4.3 does not need `P^∞(C) > 0`. The following are not formalised: the generating
functions (15.48) of the Bernoulli walk and their analyticity, where the drift route gives the same
conclusion; Teugels' `(N + 1)`-state example beyond its uniform invariant law, whose eigenvalue
analysis the book quotes; the informal remarks; and the commentary of §15.6. See
[corrections](docs/corrections.md). The library contains **2916 theorems**. Of these, 275 are in the
9 Chapter 15 modules. The other 2641 are in the 122 modules carried from the Chapter 14 project
`FErgodicity`, which cover Chapters 1–11, 13 and 14 and the renewal theory.

The chapter rests on eight groups of results.

* **Geometric sums along the path** (`GeometricSums`). `tpow r t = rᵗ` for `t ∈ ℕ ∪ {∞}`, with
  `r^∞ = ∞`. `kendallMoment P A r x` is `E_x[r^{τ_A}]` (15.2), `geomSum P B r f x` is
  `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` (15.22), `geomTaboo P B r f x` is `U_B^{(r)}(x, f)` (15.12), (15.23),
  and `geomG P B r f x` is `G_B^{(r)}(x, f) = E_x[Σ_{k=0}^{σ_B} f(Φ_k) rᵏ]` (15.29). At `r = 1` they
  are the Chapter 14 quantities (`geomSum_one`, `geomTaboo_one`, `geomG_one`). The first-step
  identities are `geomTaboo_eq` (15.31) and `geomG_eq`, and `E_x[r^{τ_B}] ≤ U_B^{(r)}(x, f)` for
  `f ≥ 1` is `kendallMoment_le_geomTaboo`. The strong Markov property with geometric weights
  (`lintegral_weight_shiftAt`, `lintegral_sumBefore_le_weighted`) gives the bounds through an
  intermediate set (`geomTaboo_le_add_mul`, `geomSum_le_add_mul`).
* **Kendall sets and the geometric trials argument** (`KendallSets`). Kendall sets, `f`-Kendall sets
  and `f`-geometrically regular sets are `IsKendall`, `IsFKendall` and `IsFGeomRegularSet`. The
  trials bound `geomTaboo_trials` combines (15.24) (`lintegral_tpow_returnTimeK_le_pow`), the
  sample-path bound of p. 374 (`sumBefore_le_tsum_returnTimeK`), `xy ≤ γⁿx² + γ⁻ⁿy²`
  (`le_mul_sq_add_inv`) and (15.27) (`measure_returnTimeK_lt_le_pow`). For a petite set the
  probability of `m` visits before `τ_B` is at most `1/2` (`exists_returnTimeK_lt_le_half`).
  Jensen's inequality on p. 374 is replaced by `tpow_le_one_add`. Theorem 15.2.1 is
  `theorem_15_2_1`, with `C` non-empty, and its quantitative form is `theorem_15_2_1_bound`.
* **The geometric drift condition (V4)** (`GeometricDrift`). (V4) is `DriftV4 P V ρ b C`, written
  `PV ≤ ρV + b 1_C` with `ρ = 1 − β`; it is (V3) with `f = (1 − ρ) V` (`DriftV4.driftV3`).
  Lemmas 15.2.2, 15.2.3, 15.2.8 and 15.2.9 are `lemma_15_2_2_i`, `lemma_15_2_2_ii`, `lemma_15_2_3`,
  `lemma_15_2_8` and `lemma_15_2_9`. Theorem 15.2.4 is `theorem_15_2_4`. The geometric comparison
  theorem 15.2.5 is `theorem_15_2_5`, from the multiplied form `geom_comparison`.
  Theorems 15.2.6–15.2.7 are `theorem_15_2_6` and `theorem_15_2_7`, and the sets (15.33) are
  `exists_kendall_sublevel`. The `f`-geometric regularity of the chain (15.36) is `IsFGeomRegularOn`
  and `IsFGeomRegularChain`. Propositions 15.3.1–15.3.2 are `proposition_15_3_1` and
  `proposition_15_3_2`, and Theorem 15.3.3 is `theorem_15_3_3` and `theorem_15_3_3_converse`.
* **Chains with atoms** (`GeometricAtoms`, and `KendallTheorem`, carried). (15.9) is
  `tsum_pow_lintegral_tabooKernel`, and the summed regenerative bound (15.8)–(15.11) is
  `tsum_fNorm_le_geom_atom`: from an atom with an aperiodic return-time law and
  `U_α^{(κ)}(a, f) < ∞`, `Σₙ rⁿ⁺¹ ‖λPⁿ⁺¹ − π‖_f ≤ R E_λ[U_α^{(κ)}(Φ₀, f)]` for some `r ∈ (1, κ]`.
  Geometrically ergodic atoms are `IsGeomErgodicAtom`. Proposition 15.1.2 is `proposition_15_1_2`,
  Proposition 15.1.3 is `proposition_15_1_3`, and Theorems 15.1.4–15.1.5 are `theorem_15_1_4` and
  `theorem_15_1_5`. A renewal sequence with a positive limit has an aperiodic increment law
  (`isAperiodicLaw_of_tendsto_pos`).
* **Skeletons** (`GeometricSkeletons`). (V4) iterates (`DriftV4.iterate`), and
  `f^{(m)} ≤ m (1 + bm) V` for `f ≤ V` (`fSkel_le_of_driftV4`). The skeleton dominates the chain
  (`geomSum_le_skeleton`), and a set petite for a skeleton is petite for the chain
  (`IsPetite.of_skeleton`). Theorems 15.3.4–15.3.7 are `theorem_15_3_4_i`, `theorem_15_3_4_ii`,
  `theorem_15_3_5`, `theorem_15_3_6` and `theorem_15_3_7`.
* **The Geometric Ergodic Theorem** (`GeometricErgodicTheorem`). The strongly aperiodic case is
  `Minorization.tsum_fNorm_le_geom`: in the split chain every visit to `C̃` lands in the atom with
  probability `δ` (`Minorization.measure_returnTimeK_one_lt_le`), so the trials argument makes the
  split atom `f̌`-Kendall. Through a skeleton, (V4) for a petite set gives (15.4)
  (`geometric_ergodic_of_driftV4`). Theorem 15.4.1 is `theorem_15_4_1` and Theorem 15.4.3 is
  `theorem_15_4_3`. Theorem 15.0.1 is `theorem_15_0_1`, a `List.TFAE` (Mathlib) of
  `IsLocallyGeomErgodic` (15.1), `HasKendallPetite` (15.2, with a non-empty set) and `HasDriftV4`
  (15.3). Its consequences, that `S_V` is absorbing and full, positivity, `π(V) < ∞` and (15.4), are
  `theorem_15_0_1_consequences`. The four implications are `hasDriftV4_of_hasKendallPetite`,
  `hasKendallPetite_of_hasDriftV4`, `isLocallyGeomErgodic_of_hasDriftV4` and
  `hasKendallPetite_of_isLocallyGeomErgodic`.
* **The converse, Theorem 15.4.2** (`GeometricConverse`, `GeometricConverseGeneral`). With an
  accessible atom it is `theorem_15_4_2_atom`. The argument (15.44)–(15.46) runs with truncated sums
  in `[0, ∞]`, through the tail bound `atom_tail_le` (with the corrected sign) and the Fubini
  identity `tsum_pow_mul_eq_add`. With `f` bounded on the atom, `theorem_15_4_2_atom_regular` gives
  an `f`-Kendall atom and `f`-geometric regularity on a full absorbing set. Without an atom the
  book's reduction fails, and the theorem is proved by another route (`theorem_15_4_2`;
  `theorem_15_4_2_univ` is the book's form, with the sums finite everywhere). The atom argument
  needs only two test functions, `1_α` and `f` (`atom_geomTaboo_ne_top`, `atom_tail_le_tsub`). For a
  small set `C` these give measurable functions `D(x) = Σⱼ rʲ |Pʲ(x, C) − π(C)|` and
  `E(x) = Σⱼ rʲ (π(f) − Pʲ(x, f))⁺`, finite on `C`. The minorizing measure is restricted to the part
  of `C` where `D + E ≤ ℓ`, which it charges, so the split atom satisfies the two hypotheses for
  `f^{(m)}`. Then `G_{α̌}^{(s)}(·, f̌)` satisfies (V4) at the atom with no bound on `f̌` there
  (`IsAtom.driftV4_geomG`), and `x ↦ ∫ x*(dz) G(z)` satisfies (V4) for the skeleton
  (`Minorization.driftV4_of_split_drift`). Theorems 15.3.3 and 15.3.7 and Proposition 15.3.2 go back
  to the chain.
* **Examples and models** (`GeometricModels`). For the forward recurrence time chain the renewal
  state is Kendall exactly when the increment law has a geometric moment (`fwdRec_isKendall_iff`),
  and geometric ergodicity and geometric tails go together (`fwdRec_tails_of_isGeomErgodicAtom`,
  `fwdRec_geomErgodic_of_tails`). The chain (15.20) is `nonGeomKernel`; it is positive iff (15.21)
  holds (`nonGeom_isPositive_iff`) and not geometrically ergodic when `β_j → 1`
  (`nonGeom_not_geomErgodic`). The `3 × 3` example is `rateKernel`, with the rates of its states in
  `rateKernel_pow_zero_two` and `rateKernel_state_one`. For Teugels' example the uniform invariant
  law is `isInvariant_uniform_of_symm`. The Bernoulli walk `bernoulliWalk` satisfies (V4) with
  `V(x) = zˣ` (`bernoulliWalk_driftV4`) and is `V`-geometrically ergodic for `0 < p < 1/2`
  (`bernoulliWalk_geometricErgodic`). The simple linear model is `ar1_geometricErgodic` ((15.49) is
  `ar1_eq_15_49`), and the bilinear model with `V(x) = |x|ᵏ + 1` is `bilinear_geometricErgodic`
  ((15.51) is `bilinear_eq_15_51`; `k = 1` is (15.52)). The variances converge geometrically
  (`bilinear_variance_convergence`).

The library covers the chapter as follows.

* **The Geometric Ergodic Theorem** (Chapter 15 introduction, pp. 362–364). Theorem 15.0.1 with
  (15.1)–(15.4) and the correction to (ii), and (15.7).
* **Using the regenerative decomposition** (§15.1.1). (15.8)–(15.12).
* **Kendall's renewal theorem** (§15.1.2). Theorem 15.1.1 with (15.13)–(15.16), carried.
* **The geometric ergodic theorem for atoms** (§15.1.3). Kendall atoms, `f`-Kendall atoms and
  geometrically ergodic atoms, Proposition 15.1.2, Proposition 15.1.3 with (15.17) and the corrected
  identity, Theorem 15.1.4 with (15.18) and its counterexample, Theorem 15.1.5 with (15.19).
* **Geometrically ergodic chains on countable spaces** (§15.1.4). Forward recurrence time chains,
  (15.20)–(15.21), the `3 × 3` example with its corrections, and the uniform invariant law of
  Teugels' example.
* **`f`-Kendall sets and `f`-geometrically regular sets** (§15.2.1). The definitions,
  (15.22)–(15.27), Theorem 15.2.1 with its counterexample and correction.
* **The geometric drift condition** (§15.2.2). (V4) and (15.28)–(15.31), Lemmas 15.2.2–15.2.3,
  Theorem 15.2.4.
* **Other solutions of the drift inequalities** (§15.2.3). Theorem 15.2.5 and (15.32),
  Theorem 15.2.6 and (15.33)–(15.34), Theorem 15.2.7 with its counterexample and correction,
  Lemma 15.2.8 and (15.35), Lemma 15.2.9.
* **`f`-geometric regularity of chains** (§15.3.1). (15.36), Proposition 15.3.1 and (15.37),
  Proposition 15.3.2 and (15.38), Theorem 15.3.3.
* **Connections between `Φ` and `Φⁿ`** (§15.3.2). Theorem 15.3.4 and (15.39),
  Theorems 15.3.5–15.3.7.
* **`f`-geometric ergodicity for general chains** (§15.4). Theorem 15.4.1 and (15.40)–(15.43),
  Theorem 15.4.2 with (15.44)–(15.46), the counterexample to (15.44) and the general case,
  Theorem 15.4.3 and (15.47).
* **Simple random walk and linear models** (§15.5). The Bernoulli walk, (15.49)–(15.52) and the
  convergence of the variances.

All names are in the namespace `MeynTweedie.GeometricErgodicity`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

### The Chapter 15 modules (275 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [GeometricSums](GeometricErgodicity/GeometricSums.lean) | 56 | §§15.1–15.2: `rᵗ` for `t ∈ ℕ ∪ {∞}` and the bound replacing Jensen's inequality on p. 374, `E_x[r^{τ_A}]` (15.2), `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` (15.22), `U_B^{(r)}(x, f)` (15.12), `G_B^{(r)}(x, f)` (15.29), measurability, monotonicity, the case `r = 1`, the first step (15.31), `E_x[r^{τ_B}] ≤ U_B^{(r)}(x, f)`, the strong Markov property with geometric weights, bounds through an intermediate set |
| [KendallSets](GeometricErgodicity/KendallSets.lean) | 41 | §15.2.1: Kendall sets, `f`-Kendall sets and `f`-geometrically regular sets, `n`-th return times and their shifts, the sample-path bound of p. 374, (15.24), (15.27), `xy ≤ γⁿx² + γ⁻ⁿy²`, the geometric trials bound, petite sets are left geometrically often, Theorem 15.2.1 corrected and its counterexample |
| [GeometricDrift](GeometricErgodicity/GeometricDrift.lean) | 30 | §§15.2.2–15.3.1: (V4) (15.28) and its relation to (V2) and (V3), Lemmas 15.2.2–15.2.3, (15.30), Theorem 15.2.4, the geometric comparison theorem 15.2.5 and (15.32), (15.33)–(15.34), Theorem 15.2.6, Theorem 15.2.7 corrected and its counterexample, Lemmas 15.2.8–15.2.9, (15.36), Propositions 15.3.1–15.3.2, Theorem 15.3.3 |
| [GeometricAtoms](GeometricErgodicity/GeometricAtoms.lean) | 28 | §15.1: generating functions of return times, (15.9), the geometric regenerative bound (15.8)–(15.11), geometrically ergodic atoms, Proposition 15.1.2, Proposition 15.1.3 with the corrected identity and its counterexample, Theorem 15.1.4 corrected and its counterexample (the flip chain), aperiodicity from a positive limit, Theorem 15.1.5 |
| [GeometricSkeletons](GeometricErgodicity/GeometricSkeletons.lean) | 18 | §15.3.2: (V4) iterated, `f^{(m)} ≤ m (1 + bm) V`, petite sets of a skeleton, the skeleton dominates the chain, Theorem 15.3.4 and (15.39), Theorems 15.3.5–15.3.7 |
| [GeometricErgodicTheorem](GeometricErgodicity/GeometricErgodicTheorem.lean) | 30 | §15.4 and Theorem 15.0.1: path functionals of the split chain, the trials argument in the split chain, the strongly aperiodic bound, (15.4) from (V4), Theorem 15.4.1, the conditions (15.1)–(15.3) and the four implications, a Kendall split atom from local convergence, (V4) from a Kendall split atom, concentrated minorizations of skeletons, Theorem 15.4.3, Theorem 15.0.1 and its consequences, the counterexample to (ii) |
| [GeometricConverse](GeometricErgodicity/GeometricConverse.lean) | 7 | Theorem 15.4.2 with an atom: `ν(f) ≤ μ(f) + ‖μ − ν‖_f`, the last-exit decomposition integrated, the tail bound behind (15.44) corrected, the Fubini identity (15.46), Theorem 15.4.2 for an accessible atom and its regularity form, the counterexample to (15.44) |
| [GeometricModels](GeometricErgodicity/GeometricModels.lean) | 47 | §§15.1.4, 15.5: forward recurrence time chains, the chain (15.20) and (15.21), the `3 × 3` example and the rates of its states with the corrections, symmetric matrices, the Bernoulli walk and (V4) with `V(x) = zˣ`, (15.49), (15.51)–(15.52), the simple linear model, the bilinear model with `V(x) = |x|ᵏ + 1`, the convergence of the variances |
| [GeometricConverseGeneral](GeometricErgodicity/GeometricConverseGeneral.lean) | 18 | Theorem 15.4.2 without an atom: positive parts and Jensen's inequality for them, the split chain started from its atom, (V4) at an atom from a finite `U_α^{(s)}(a, f)`, (V4) for the chain from (V4) for the split chain, the atom argument with two test functions, Theorem 15.4.2 on a full set and everywhere |

### Carried modules (2641 theorems)

Carried from the Chapter 14 project `FErgodicity` (2641 theorems): 122 of its 136 modules. They come
from that project as it stood before its follow-up modules were added. They are its 11 first
Chapter 14 modules (216 theorems) `FNorm` (23), `FRegularSets` (44), `FRegularityDrift` (21),
`FRegularAtoms` (29), `FSkeletons` (23), `FSplitChain` (10), `FNormErgodic` (8),
`FNormErgodicTheorem` (20), `FErgodicModels` (25), `FPeriodicErgodic` (10), `ContinuousRenewal` (3),
and the 111 modules that `FErgodicity` carries from the Chapter 13 project `Ergodicity` (2425
theorems). The 14 follow-up modules of `FErgodicity` are not carried: the §14.5 continuous-time
renewal modules `RenewalMeasure`, `RenewalRegeneration`, `RenewalChain`, `RenewalKey`,
`RenewalEquilibrium`, `RenewalUniform` and `RenewalAbsCont`, the Blackwell modules
`BlackwellHarmonic` and `BlackwellRenewal`, and `FNormMeasurable`, `FHalfLineIntegrated`,
`FLazyChain`, `FPeriodicCycle` and `FPeriodicAll`. So the results of `FErgodicity` that those
modules prove are not part of this library: among them Blackwell's renewal theorem 14.5.1, the
Uniform Key Renewal Theorem 14.5.2 (of which only the step from (i) to (ii),
`theorem_14_5_2_ii_of_i`, is here), Theorem 14.2.11 without aperiodicity and Theorem 14.3.6 (ii) for
every initial state. The carried modules are identical to the copies there except for the namespace
and the imports, and except that `ContinuousRenewal`, `FErgodicModels`, `FNormErgodic` and
`FPeriodicErgodic` keep the module docstrings they had before the follow-up modules were written.
The `f`-norm (`fNorm`, `IsFTest`, `fNorm_le_add`, `fNorm_map_le`), `E_x[Σ_{k<τ_B} f(Φ_k)]`,
`f`-regular sets and (V3) (`fSumReturn`, `IsFRegularSet`, `DriftV3`, `lemma_14_2_1`,
`proposition_14_1_1`, `theorem_14_2_4`, `lintegral_sumBefore_indicator_le`), the regenerative bound
in `f`-norm (`fNorm_comp_pow_succ_le`, `lintegral_eq_atom`), skeletons (`fSkel`, `lemma_14_2_8`,
`exists_forall_large_minorization`, `tsum_eq_tsum_sum_block`), the split chain
(`Minorization.split_positive`, `Minorization.lintegral_split_comp_fst`), Lemma 14.3.2
(`lemma_14_3_2_i_measure`), `isAperiodic_of_minorization`, `isPositive_of_driftV3`,
`lintegral_dirac_le` and the bilinear model of Chapter 14 (`proposition_14_4_2`,
`bilinear_lintegral_pow_le`, `bilinear_condition_14_32`) are used. No Chapter 15 module depends,
directly or through other modules, on `ContinuousRenewal` or `FPeriodicErgodic`.

Carried in turn by `FErgodicity` from the Chapter 13 project `Ergodicity`, and by `Ergodicity` from
the earlier projects (see those projects' READMEs for how the copies differ from the originals):

* From the Chapter 13 project `Ergodicity`, its own modules (420 theorems): the renewal modules (134
  theorems) `SequenceLemmas` (30), `RenewalSequences` (41), `RenewalTheorem` (22), `KeyRenewal` (5),
  `KendallTheorem` (36), and the Chapter 13 modules (286 theorems) `TotalVariation` (36),
  `RegenerativeDecomposition` (52), `AtomErgodic` (11), `SplitErgodic` (14), `AperiodicErgodic` (9),
  `CountableErgodic` (35), `PeriodicErgodic` (47), `LinkedRenewal` (25), `SumsOfTransitions` (31),
  `CouplingRenewal` (10), `SumsNoAtom` (12), `ErgodicTheorem` (4). The directions of Kendall's
  Theorem 15.1.1 (`kendall_geometric_of_moment`, `kendall_moment_of_geometric`), the geometric rate
  `kendall_geometric_bound`, the bound of p. 365 (`geometric_delayed_bound`), increment laws and
  renewal sequences (`IsIncrementLaw`, `realRenewalSeq`, `incrMean`, `IsAperiodicLaw`), the entry
  law and renewal sequence of an atom and the last-exit decomposition (`entryLaw`, `atomRenewal`,
  `IsAtom.pow_succ_lastExit`, `eq_smul_atomMeasure_of_accessible`), ergodic atoms
  (`tendsto_atomRenewal_of_aperiodicLaw`, `isAperiodicLaw_entryLaw`), the split chain
  (`split_comp_pow_map_fst`, `Minorization.isAperiodicLaw_entryLaw_checkAlpha`), skeletons with a
  minorization on a set in `B⁺(X)` (`exists_skeleton_minorization`) and `meanReturnTime_eq_tsum` are
  used. The docstring of `KendallTheorem` lists Proposition 15.1.3, Theorems 15.1.4–15.1.5 and
  §15.1.4 as not formalised there; they are formalised in `GeometricAtoms` and `GeometricModels`. No
  Chapter 15 module depends on `KeyRenewal`, `CountableErgodic`, `CouplingRenewal` or
  `ErgodicTheorem`.
* From the Chapter 11 project `DriftRegularity` (134 theorems): `Comparison` (33), `RegularSets`
  (29), `FosterCriterion` (27), `RegularityConverse` (38), `AtomHittingBounds` (7). Sums along the
  path and the Comparison Theorem (`sumBefore`, `comparison_theorem`), `G_A(x, f)` and `U_A(x, f)`
  (`gKernelFn`, `tabooPotFn`), mean hitting times (`meanHitTime`), (V2) and Theorem 11.3.4
  (`DriftV2`, `theorem_11_3_4`), Lemma 11.3.7 (`isPetite_meanHitTime_le`) and the petiteness of
  atoms (`IsAtom.isPetite`) are used.
* From the Chapter 10 project `InvariantMeasures`, its own modules (316 theorems): `Invariance`
  (39), `MinimalInvariant` (22), `AtomInvariant` (30), `SplitInvariant` (8), `UniqueInvariant` (18),
  `PositiveNull` (14), `CountableInvariant` (22), `QueueInvariant` (19), `MG1Invariant` (25),
  `ModelInvariant` (11), `QueueInvariantMinimal` (26), `LadderInvariant` (42), `GIG1Invariant` (9),
  `RenewalInvariant` (17), `LinearInvariant` (14). Invariant measures and positive chains
  (`IsInvariant`, `IsPositive`, `proposition_10_1_1`), the atom measure and mean return times
  (`atomMeasure`, `meanReturnTime`, `theorem_10_2_2`), the taboo measures (`tabooSeq`),
  Theorem 10.4.9 (`theorem_10_4_9_equiv`), and the forward recurrence time chain of the heavy-tailed
  renewal law (`heavyRenewal`, `fwdRecInv`, `fwdRec_isAccessibleAtom`, `fwdRec_tabooKernel`,
  `theorem_10_0_1_counterexample`) are used. No Chapter 15 module depends on `GIG1Invariant`,
  `RenewalInvariant` or `LinearInvariant`.
* From the Chapter 9 project `HarrisRecurrence` (212 theorems): `HarrisDefinitions` (29),
  `HarrisProperties` (15), `HarrisDecomposition` (18), `SupermartingaleDrift` (14), `NonEvanescence`
  (21), `TopologicalRecurrence` (21), `TopologicalExamples` (33), `DriftHarris` (29),
  `StochasticComparison` (32). Petite sets in `B⁺(X)` and skeletons on path space
  (`exists_petite_pos`, `pathKernel_map_skeleton`) are used. No Chapter 15 module depends on
  `TopologicalExamples`.
* From the Chapter 8 project `TransienceRecurrence` (220 theorems): `UniformTransience` (46),
  `Decompositions` (8), `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23),
  `CountableClassification` (18), `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16),
  `SkipFreeWalk` (15), `RandomWalkMeanZero` (5). Properties of the return times (`le_returnTimeK`,
  `returnTimeK_mem`) are used. No Chapter 15 module depends on `RandomWalkIntegers`, `SkipFreeWalk`
  or `RandomWalkMeanZero`.
* From the Chapter 6 project `TopologyContinuity` (130 theorems): `FellerChains` (40), `TChains`
  (14), `EChains` (16), `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16),
  `TChainModels` (10), `EChainsStability` (12). No Chapter 15 module depends on `EChains`,
  `LinearTChains`, `CompactPetite` or `EChainsStability`.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes` (36),
  `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` (`pathKernel`), hitting
  and return times (`firstHit`, `firstReturn`, `returnTimeK`, `hitProb`), the taboo kernels `_APⁿ`
  (`tabooKernel`), the shift and the strong Markov property (`shift`, `shiftAt`, `stoppedState`,
  `markov_lintegral`) and transition matrices (`IsTransitionMatrix`, `matKernel`) are used
  throughout. No Chapter 15 module depends on `StateSpaces` or `SpecificMatrices`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Absorbing and full sets (`IsAbsorbing`, `IsFull`,
  `proposition_4_2_3_i`) and irreducibility (`IsPhiIrreducible`, `IsMaximalIrreducibility`,
  `IsIrreducibleChain`) are used. No Chapter 15 module depends on `CountableIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Atoms (`IsAtom`, `IsAccessibleAtom`),
  the split chain (`Minorization`, `Minorization.splitKernel`, `Minorization.checkAlpha`,
  `Minorization.splitK`, `Minorization.IsConcentrated`), small and petite sets (`IsSmallSet`,
  `IsSmall`, `IsPetite`, `proposition_5_5_3`), aperiodicity (`IsAperiodic`, `proposition_5_4_5_iii`)
  and the forward recurrence time chain (`fwdRecKernel`) are used. No Chapter 15 module depends on
  `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). The AR(1) model
  (`ar1Kernel`) and the bilinear model (`bilinearKernel`) are used.
* From the Chapter 5 project `PseudoAtoms` directly (286 theorems): `ModelKernels` (19),
  `ModelCountableModels` (9), `ModelQueues` (16), `ModelStorage` (18), `ModelRenewal` (29),
  `SpecificKernels` (42), `Regeneration` (12), `PoissonCounts` (12), `RenewalSkeletons` (53),
  `LadderChains` (25), `GIG1Embedding` (37), `GIG1SmallSets` (7), `RenewalSmallSets` (7). The
  reflected random walk on `ℤ₊` (`reflectedWalkKernel`), on which the Bernoulli walk is built, is
  used. No Chapter 15 module depends on `ModelKernels`, `ModelQueues`, `ModelStorage`,
  `ModelRenewal`, `SpecificKernels`, `Regeneration`, `PoissonCounts`, `RenewalSkeletons`,
  `GIG1Embedding`, `GIG1SmallSets` or `RenewalSmallSets`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
