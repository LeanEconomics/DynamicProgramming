# Meyn and Tweedie, Chapter 13: Ergodicity, in Lean

This is the `StochasticStability/Ergodicity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 13 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 313–335, together with the renewal theory of Chapters 13–15 and
Appendix D.7. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 13 proves that a positive Harris chain converges to its invariant probability in total
variation. The total variation norm (13.7) is `‖μ − ν‖ = sup_{|f| ≤ 1} |μ(f) − ν(f)|`, and for
measures of equal mass it is `2 sup_A |μ(A) − ν(A)|` (13.8). §13.1 works on a countable space. For
a reference state `α` it writes the first-entrance last-exit decomposition (13.9) through the entry
law `a_x(n) = P_x(τ_α = n)`, the renewal sequence `u(n) = P_α(Φₙ = α)` and the taboo sequence
`t_y(n) = _αPⁿ(α, y)` (13.10)–(13.12) as `Pⁿ(x, y) = _αPⁿ(x, y) + a_x ∗ u ∗ t_y (n)` (13.16). With
the representation (13.13) of `π` this gives the bound (13.17) (Proposition 13.1.1), and one
ergodic atom, `Pⁿ(α, α) → π(α)` (13.22), gives total variation convergence from every state
(Theorem 13.1.2). §13.2 supplies the renewal theory that makes an atom ergodic. For an aperiodic
increment law `p` with finite mean `m_p` and delay laws `a`, `b`, the coupling time of the two
delayed renewal processes is almost surely finite (Proposition 13.2.1), so
`|a ∗ u (n) − b ∗ u (n)| → 0` (Theorem 13.2.2) and `a ∗ u (n) → m_p⁻¹` (Theorem 13.2.3), and every
accessible atom of a positive aperiodic chain is ergodic (Proposition 13.2.4). The decomposition
then extends to general spaces as the Regenerative Decompositions (13.47)–(13.48) (Theorem 13.2.5).
§13.3 proves `‖λPⁿ − π‖ → 0` for a positive Harris chain with an accessible ergodic atom and, by
splitting, for a strongly aperiodic one (Theorem 13.3.1), shows that `‖λPⁿ − π‖` is non-increasing
(Proposition 13.3.2), and passes to a skeleton for the Aperiodic Ergodic Theorem (Theorem 13.3.3).
It then gives the periodic and the non-Harris forms (Theorem 13.3.4) and derives positivity and
convergence from convergence on a small set (Theorem 13.3.5). §13.4 bounds sums. It proves
`Σₙ |a ∗ u (n) − b ∗ u (n)| < ∞` for delays of finite mean, through the variation
`Var(u) = Σₙ |u(n) − u(n − 1)| < ∞` (Proposition 13.4.1), and `Σₙ |u(n) − m_p⁻¹| < ∞` when
`Σ n² p(n) < ∞` (Proposition 13.4.2). It proves
`∫∫ λ(dx) μ(dy) Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` for regular initial laws, with an atom
(Theorem 13.4.3) and without (Theorem 13.4.4), and `Σₙ ‖λPⁿ − π‖ < ∞` when `E_α[τ_α²] < ∞`
(Theorem 13.4.5). The Aperiodic Ergodic Theorem 13.0.1 collects these results. For an aperiodic
Harris chain it states that positivity, the convergence (13.1) on a small set, a regular set, the
bound (13.2) on a petite set, the drift condition (13.3) and the convergence (13.4) from every state
are equivalent, and that (13.5) follows.

The renewal theory was built for this chapter and is documented here. It also covers material
that belongs to later chapters. Lemmas D.7.1–D.7.4 of Appendix D.7 are proved. The renewal theorem
`u(n) → m_p⁻¹` is proved analytically, by the argument of Erdős, Feller and Pollard, and not by
the book's coupling; it also gives `u(n) → 0` when `m_p = ∞`. §14.5 uses this renewal theory: its
key renewal theorem (14.34), Blackwell's theorem (Theorem 14.5.1), the Uniform Key Renewal Theorem
(Theorem 14.5.2 (i)) and Proposition 14.5.5 are proved here in their discrete forms, for renewal
sequences on `ℤ₊`. Kendall's Theorem 15.1.1 belongs to Chapter 15. It is proved here as a `TFAE`
of the three conditions, by generating functions, with Mathlib's power series and the Cauchy
integral formula, together with the renewal content of Proposition 15.1.2.

Every numbered result of Chapter 13 is formalised: Theorem 13.0.1, Proposition 13.1.1,
Theorem 13.1.2, Proposition 13.2.1, Theorems 13.2.2–13.2.3, Proposition 13.2.4, Theorem 13.2.5,
Theorem 13.3.1, Proposition 13.3.2, Theorems 13.3.3–13.3.5, Propositions 13.4.1–13.4.2 and
Theorems 13.4.3–13.4.5, together with Lemmas D.7.1–D.7.4 and Theorem 15.1.1. Four claims are false
as printed. Three are refuted in Lean by a counterexample of this project, and the fourth by a
counterexample carried from Chapter 11; for each a corrected statement is proved.
Proposition 13.1.1 is stated "for any `x, y, α ∈ X`", but (13.13) needs `α ∈ B⁺(X)`, and (13.17)
fails for the oscillating chain `oscKernel` with its transient state `α = 0`. Proposition 13.2.4 (ii)
fails for a positive recurrent aperiodic chain on `ℕ` (`leakKernel`) whose state `1` escapes to
infinity with probability at least `1/2`; it holds for positive Harris chains. Theorem 13.3.1 is
false under the book's strong aperiodicity, which does not require the small set to lie in
`B⁺(X)`: `oscKernel` is positive Harris and strongly aperiodic, with period `2` on `{1, 2}`.
Theorem 13.0.1 (iii) needs a non-empty petite set, since `C = ∅` satisfies (13.2) for every chain
(`theorem_11_3_14_counterexample`, carried). Further points are made explicit without a
counterexample of their own: the state space is countably generated wherever small sets or the
Harris property from every state are used; Theorem 13.2.5 is stated for bounded `f`; Theorem 13.3.5
needs `ν(C) > 0`; Theorem 13.0.1 (i) needs a nonzero invariant measure; Kendall's "ergodic renewal
sequence" is an aperiodic increment law; and Lemma D.7.4 needs a positive element. Some statements
are proved in a stronger form: Theorems 13.2.5 and 13.4.3–13.4.5 need only positivity, not positive
Harris recurrence; Proposition 13.1.1 needs neither the Harris property nor a countable space;
and Theorem 13.2.2 holds without `m_p < ∞`, as the book remarks on p. 322. Two proofs are
replaced. The renewal theorems of §13.2 are proved analytically. The coupling identities
(13.32)–(13.33) for general delays are not used. Their special case `a = δ₀`, `b = δ₁`, which
gives `Var(u) < ∞` (13.69), is proved at the level of kernels on the linked forward recurrence time
chain. The following are not formalised: the
coupled renewal processes and the coupling time `T_ab` as random variables, with (13.30) and
(13.67); the continuous-time statements of §14.5, which belong to Chapter 14; Proposition 15.1.3,
Theorems 15.1.4–15.1.5 and the examples of §15.1.4, which belong to Chapter 15; and the commentary of
§13.5. See [corrections](docs/corrections.md). The library contains **2425 theorems**. Of these,
420 are new: 134 in the renewal modules and 286 in the Chapter 13 modules. The other 2005 are in
the modules carried from Chapters 1–11.

The chapter rests on six groups of results.

* **The total variation norm** (`TotalVariation`). `tvNorm μ ν` is (13.7),
  `sup_{|f| ≤ 1} |μ(f) − ν(f)|` over measurable `f : X → ℝ`, and `tvSup μ ν` is
  `sup_A |μ(A) − ν(A)|`. Through the Hahn decomposition of `μ − ν` (`IsHahnDecomposition`, Mathlib)
  the norm is `sup_A (μ − ν)(A) − inf_A (μ − ν)(A)` (`tvNorm_eq_sup_sub_inf`, (13.7)), and for
  measures of equal mass it is `2 tvSup μ ν` (`tvNorm_eq_two_mul_tvSup`, (13.8)). On a countable
  space it is `Σ_y |μ{y} − ν{y}|` (`tvNorm_eq_tsum`). Transport by a kernel does not increase it
  (`tvNorm_comp_le`), which is Proposition 13.3.2 (`proposition_13_3_2`), and a decomposition
  `μ − ν = σ₁ − σ₂` bounds it by `σ₁(X) + σ₂(X)` (`tvNorm_le_of_sub_eq`), which is how the
  regenerative decompositions become total variation bounds.
* **Renewal theory** (`SequenceLemmas`, `RenewalSequences`, `RenewalTheorem`, `KeyRenewal`,
  `KendallTheorem`). Sequences on `ℤ₊` are `ℕ → ℝ`, `a ∗ b` is `realConv a b`, an increment law is
  `IsIncrementLaw p`, its renewal sequence `u = Σₖ p^{∗k}` is `realRenewalSeq p` and its mean is
  `incrMean p`. Lemmas D.7.1–D.7.4 are `lemma_D_7_1`, `lemma_D_7_2_i`, `lemma_D_7_2_ii`,
  `lemma_D_7_3` and `lemma_D_7_4_gcd`. The renewal theorem is `renewal_theorem` (`u(n) → m_p⁻¹`,
  with `m_p⁻¹ = 0` when the mean is infinite), proved from the renewal equation along
  subsequences at `lim sup u` and `lim inf u` (`tendsto_shift_of_limsup`, `exists_shift_closure`,
  `limsup_mul_sum_renewalTail_le`, `one_le_liminf_mul_incrMean`); Theorems 13.2.2 and 13.2.3 are
  `theorem_13_2_2` and `theorem_13_2_3`. The discrete key renewal, Blackwell and uniform key
  renewal theorems of §14.5 are `key_renewal_theorem`, `delayed_key_renewal_theorem`,
  `blackwell_renewal_theorem`, `uniform_key_renewal_theorem` and
  `uniform_key_renewal_two_delays`. Kendall's Theorem 15.1.1 is `theorem_15_1_1`, a `List.TFAE`
  (Mathlib) of geometric convergence of `u`, the meromorphic extension of `U(z)` and a geometric
  moment of `p`. Its analytic core is `geometric_inverse`, which inverts a generating function
  with no zero on the closed unit disc, and `exists_summable_of_differentiableOn`, which gets
  geometric decay of coefficients from an analytic extension by Cauchy's estimate.
* **The regenerative decomposition** (`RegenerativeDecomposition`). For an atom `α` with `a ∈ α`
  the three sequences of (13.10)–(13.12) and (13.42)–(13.43) are `entryLaw P hα λ`,
  `atomRenewal P α a` and `lastExitSeq P hα a f`. The decompositions (13.44)–(13.46) are identities
  of measures (`comp_pow_succ_atom_toReal`, `lintegral_pow_succ_atom_toReal`,
  `lintegral_comp_pow_succ_atom_toReal`), and (13.50) is `lintegral_eq_tsum_lastExitSeq`. The
  Regenerative Decompositions (13.47)–(13.48) are `regenerative_decomposition_47` and
  `regenerative_decomposition_48`, and Theorem 13.2.5 is `theorem_13_2_5`. Taken uniformly over
  `|f| ≤ 1`, (13.48) becomes the total variation bound `tvNorm_comp_pow_succ_le`, and its three
  terms tend to `0` for an ergodic atom reached almost surely (`tendsto_tvNorm_of_ergodic_atom`,
  the prescription (E1)–(E3)).
* **Ergodic atoms, splitting and countable spaces** (`AtomErgodic`, `SplitErgodic`,
  `CountableErgodic`). An ergodic atom is `IsErgodicAtom P π α` (13.22). Proposition 13.2.4 (i) is
  `proposition_13_2_4_i`, by the renewal theorem at the atom (`tendsto_atomRenewal_of_aperiodicLaw`)
  and the aperiodicity of its return-time law (`isAperiodicLaw_entryLaw`). Theorem 13.3.1 is
  `theorem_13_3_1_i` and, corrected, `theorem_13_3_1_ii`: the atom `α̌` of the split chain is reached
  almost surely from every state (`Minorization.hitProb_checkAlpha_eq_one`), and the marginal of the
  split chain is no farther from `π` than the split chain is from `π̌` (`tvNorm_le_split`, (13.57)).
  On countable spaces Proposition 13.1.1 is `proposition_13_1_1` (corrected), Theorem 13.1.2 is
  `theorem_13_1_2`, and Proposition 13.2.4 (ii) is `proposition_13_2_4_ii` (corrected); the
  counterexamples are `proposition_13_1_1_counterexample`,
  `proposition_13_2_4_ii_counterexample` and `theorem_13_3_1_counterexample`.
* **The Aperiodic Ergodic Theorem** (`AperiodicErgodic`, `PeriodicErgodic`, `ErgodicTheorem`).
  Theorem 13.3.3 is `theorem_13_3_3`: every aperiodic positive Harris chain has
  `‖λPⁿ − π‖ → 0` for every initial probability `λ`. A skeleton has a minorization on a set in
  `B⁺(X)` (`exists_skeleton_minorization`), Theorem 13.3.1 (ii) applies to it, and
  Proposition 13.3.2 returns to `Pⁿ`. From a state it is `theorem_13_3_3_dirac`, and in the form
  (13.4) `theorem_13_3_3_sup`. Theorem 13.3.4 is `theorem_13_3_4_i` and `theorem_13_3_4_ii`, through
  `absorbKernel`, which makes a chain restricted to an absorbing set into a chain on `X`. Theorem
  13.3.5 is `theorem_13_3_5_positive`, `theorem_13_3_5` and `theorem_13_3_5_null`. Theorem 13.0.1
  is `theorem_13_0_1` ((i), (ii) and (13.4)) and, in full, `theorem_13_0_1_full`, a `List.TFAE` of
  six conditions: (i) positivity, (ii) the convergence (13.1) on a small set in `B⁺(X)`, (13.4),
  (iii) a regular set in `B⁺(X)`, (iii′) the bound (13.2) on a non-empty petite set, and (iv) the
  drift condition (13.3). Theorem 13.0.1 (i) is `theorem_13_0_1_finite` and (13.5) is
  `theorem_13_0_1_sum`.
* **Sums of transition probabilities** (`LinkedRenewal`, `CouplingRenewal`, `SumsOfTransitions`,
  `SumsNoAtom`). The linked forward recurrence time chain `V* = V⁺ ∥ V⁺` (`linkedFwdRec`, carried)
  reaches `(0, 0)` almost surely from every state (`linked_hitProb_eq_one`), and so from the
  initial law `a ⊗ b` of two delays, which is Proposition 13.2.1 (`proposition_13_2_1`). The coupling bound
  `|u(n + 1) − u(n)| ≤ P_{(0,1)}(τ_{(0,0)} ≥ n + 1)` (`abs_sub_realRenewalSeq_le`) is proved from the
  first-entrance decomposition of `V*` at the atom `(0, 0)` and the symmetry of `V*`, with no
  coupled processes. With `E_{(0,1)}[τ_{(0,0)}] < ∞` (`linked_meanReturnTime_ne_top`, (13.68)) it
  gives `Var(u) < ∞` (`summable_seqDiff_realRenewalSeq`, (13.69)). Propositions 13.4.1 and 13.4.2
  are `proposition_13_4_1` and `proposition_13_4_2`, with `Var(u)` as `renewalVar p`.
  Theorem 13.4.3 is `theorem_13_4_3`, with `theorem_13_4_3_states` and `theorem_13_4_3_regular`,
  from the summed bound `summable_tvNorm_atom`; Theorem 13.4.5 is `theorem_13_4_5`. Theorem 13.4.4,
  for chains without an atom, is `theorem_13_4_4`, with `theorem_13_4_4_states` and
  `theorem_13_4_4_regular`. Its proof needs that a regular initial law is regular for every
  skeleton (`IsRegularMeasure.pow`), a fact the book uses without stating it; it is proved through
  a drift function for the skeleton built from Theorem 11.3.12.

The library covers the chapter as follows.

* **The Aperiodic Ergodic Theorem** (Chapter 13 introduction, pp. 313–314). Theorem 13.0.1 and
  (13.1)–(13.5), with the correction to (iii).
* **Modes of convergence** (pp. 314–315). (13.6)–(13.8), the total variation norm in both forms,
  and the remarks that total variation convergence gives (13.6) uniformly in the end point and
  convergence of `μₙ(f)` for every bounded measurable `f`.
* **First-entrance last-exit decompositions** (§13.1.1). (13.9)–(13.16), Proposition 13.1.1 with its
  counterexample and correction, (13.18).
* **Solidarity from one ergodic state** (§13.1.2). (13.19)–(13.22), Theorem 13.1.2 and
  (13.23)–(13.27), and the remark that an ergodic atom forces aperiodicity.
* **Coupling renewal processes** (§13.2.1). Renewal sequences and delayed renewal sequences,
  (13.28), Proposition 13.2.1 for the linked forward recurrence time chain, and Theorem 13.2.2 and
  (13.31) by the analytic proof.
* **Convergence of the renewal function** (§13.2.2). The equilibrium law (13.34), (13.35),
  Theorem 13.2.3 and (13.37), Proposition 13.2.4 and (13.38) with the counterexample to (ii) and its
  correction.
* **The regenerative decomposition for chains with atoms** (§13.2.3). (13.39) in its first-entrance
  form, (13.40)–(13.46), Theorem 13.2.5 and (13.47)–(13.50), and the prescription (E1)–(E3) with
  (13.51)–(13.52).
* **Strongly aperiodic chains** (§13.3.1). Theorem 13.3.1 and (13.53)–(13.57), with the
  counterexample and the corrected (ii).
* **The ergodic theorem for ψ-irreducible chains** (§13.3.2). Proposition 13.3.2 and (13.58),
  Theorem 13.3.3 and (13.59)–(13.60), Theorem 13.3.4 and (13.61)–(13.62), Theorem 13.3.5 and
  (13.63)–(13.65).
* **A stronger coupling theorem** (§13.4.1). Proposition 13.4.1 and (13.66)–(13.72), the mean of
  the equilibrium law and (13.73), Proposition 13.4.2 and (13.74).
* **General chains with atoms** (§13.4.2). Theorem 13.4.3 and (13.75)–(13.80).
* **General aperiodic chains** (§13.4.3). Theorem 13.4.4 and (13.81), the regularity of split
  measures and of skeletons, Theorem 13.4.5 and (13.82)–(13.83).
* **A key renewal theorem** (§14.5). Discrete forms of (14.34), Theorem 14.5.1 and (14.35),
  Theorem 14.5.2 (i) and (14.36), and Proposition 14.5.5.
* **Kendall's renewal theorem** (§§15.1.1–15.1.2). The bound of p. 365, Theorem 15.1.1 and
  (15.13)–(15.16), and the renewal content of Proposition 15.1.2.
* **Sequences and numbers** (Appendix D.7). Lemmas D.7.1–D.7.4.

All names are in the namespace `MeynTweedie.Ergodicity`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

### Renewal theory (134 theorems)

Kendall's theorem belongs to Chapter 15, and §14.5 also uses this renewal theory. Both are
documented here because they were built here.

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SequenceLemmas](Ergodicity/SequenceLemmas.lean) | 30 | Appendix D.7: convolution of real sequences on `ℤ₊` and its algebra, Lemma D.7.1 and its form for `Σ |a| < ∞`, Lemma D.7.2 (i) with its converse and (ii), Lemma D.7.3, Lemma D.7.4 for additively closed subsets of `ℕ` |
| [RenewalSequences](Ergodicity/RenewalSequences.lean) | 41 | §§13.2.1, 15.1: increment laws, convolution powers, the renewal sequence as the coefficients of `(1 − P)⁻¹`, the renewal equation, delayed renewal sequences, tails and the mean `m_p` (13.28), the identity `Σ_{i ≤ n} tail(i) u(n − i) = 1`, generating functions on the unit disc and `U(z) = 1/(1 − P(z))` |
| [RenewalTheorem](Ergodicity/RenewalTheorem.lean) | 22 | §§13.2.1–13.2.2: aperiodic increment laws, the renewal theorem by the analytic proof of Erdős, Feller and Pollard for finite and infinite mean, delayed renewal sequences (13.20), Theorem 13.2.2 without `m_p < ∞`, the equilibrium law (13.34)–(13.35), Theorem 13.2.3 |
| [KeyRenewal](Ergodicity/KeyRenewal.lean) | 5 | §14.5 on `ℤ₊`: the key renewal theorem (14.34) undelayed and delayed, Blackwell's theorem (14.35), the uniform key renewal theorem (14.36), the form of Proposition 14.5.5 for two delays |
| [KendallTheorem](Ergodicity/KendallTheorem.lean) | 36 | §§15.1.1–15.1.2: generating functions as power series on `ℂ`, coefficient decay from an analytic extension, the inversion of a geometrically summable sequence, first differences and (15.15)–(15.16), `P(z) ≠ 1` on the unit circle off `z = 1`, deviations and differences (Lemma D.7.2), Kendall's Theorem 15.1.1, the renewal content of Proposition 15.1.2, the bound of p. 365 |

### The Chapter 13 modules (286 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [TotalVariation](Ergodicity/TotalVariation.lean) | 36 | Chapter 13 introduction and Proposition 13.3.2: the total variation norm (13.7) and its pseudometric properties, both forms (13.7)–(13.8) by the Hahn decomposition, countable spaces, bounds from decompositions of `μ − ν`, transport by maps and kernels, Proposition 13.3.2, total variation convergence implies convergence of bounded integrals, sums and multiples |
| [RegenerativeDecomposition](Ergodicity/RegenerativeDecomposition.lean) | 52 | §§13.1.1, 13.2.3: first-entrance and last-exit decompositions as identities of measures, (13.40), the sequences `a_λ`, `u`, `t_f` (13.10)–(13.12), (13.42)–(13.43), the decompositions (13.14)–(13.16), (13.44)–(13.46), (13.50), the return-time law and the renewal sequence of an atom, Theorem 13.2.5 and the Regenerative Decompositions (13.47)–(13.49), the total variation bound (13.54)–(13.56) |
| [AtomErgodic](Ergodicity/AtomErgodic.lean) | 11 | §§13.1.2, 13.2.2, 13.3.1: ergodic atoms (13.22), the renewal theorem at an atom, the aperiodicity of the return-time law, Proposition 13.2.4 (i), an ergodic atom forces aperiodicity, convergence from an ergodic atom by (E1)–(E3) and (13.51)–(13.52), Theorem 13.3.1 (i) |
| [SplitErgodic](Ergodicity/SplitErgodic.lean) | 14 | §13.3.1: the escape function of the split chain, its harmonicity, the split atom is reached almost surely from every state, the aperiodic return-time law of the split atom, (13.57), Theorem 13.3.1 (ii) in the corrected form |
| [AperiodicErgodic](Ergodicity/AperiodicErgodic.lean) | 9 | §13.3.2 and Theorem 13.0.1: skeletons with a minorization on a set in `B⁺(X)`, Theorem 13.3.3 and (13.59)–(13.60), (13.4), positivity from convergence on a small set (13.65), Theorem 13.3.5 for Harris chains, Theorem 13.0.1 for (i), (ii) and (13.4) |
| [CountableErgodic](Ergodicity/CountableErgodic.lean) | 35 | §§13.1, 13.2.2: (13.27), (13.20), Proposition 13.1.1 corrected, Theorem 13.1.2, Proposition 13.2.4 (ii) corrected, the leaky chain and the counterexample to Proposition 13.2.4 (ii), the oscillating chain and the counterexamples to Proposition 13.1.1 and Theorem 13.3.1 |
| [PeriodicErgodic](Ergodicity/PeriodicErgodic.lean) | 47 | §13.3.2: chains agreeing on an absorbing set, the invariant probabilities of a cycle, the `d`-skeleton on a cyclic set, phase averages, the restriction to the maximal Harris set, Theorem 13.3.4 and (13.61)–(13.62), Theorem 13.3.3 for positive chains off a `ψ`-null set, Theorem 13.3.5 and (13.64) |
| [LinkedRenewal](Ergodicity/LinkedRenewal.lean) | 25 | §§13.2.1, 13.4.1: the forward recurrence time chain of a real increment law and its renewal sequence, the linked chain (10.19), positivity of `u` for large `n`, irreducibility of the linked chain and its invariant probability, the composition of taboo kernels, (13.68), the coupling bound (13.33) for `δ₀`, `δ₁`, (13.69) |
| [SumsOfTransitions](Ergodicity/SumsOfTransitions.lean) | 31 | §§13.4.1–13.4.2: delay laws and their tails, (13.70)–(13.72), Proposition 13.4.1, the mean of the equilibrium law and (13.73), Proposition 13.4.2, the entry law and its mean, the total variation form of (13.47), (13.77)–(13.80), Theorem 13.4.3, the regularity of `π` under (13.82), Theorem 13.4.5 |
| [CouplingRenewal](Ergodicity/CouplingRenewal.lean) | 10 | §13.2.1: escape probabilities for any chain and any set, the support of the forward recurrence time chain, the linked chain reaches `(0, 0)` almost surely from every state, Proposition 13.2.1 |
| [SumsNoAtom](Ergodicity/SumsNoAtom.lean) | 12 | §13.4.3: mean hitting times of the split chain, the split atom from a regular law, the strongly aperiodic case, regular measures are regular for skeletons, Proposition 13.3.2 for sums, Theorem 13.4.4 and (13.81) |
| [ErgodicTheorem](Ergodicity/ErgodicTheorem.lean) | 4 | Theorem 13.0.1: positivity, regular sets, (13.2) and (13.3) for a `ψ`-irreducible chain, Theorem 13.0.1 with all six conditions, Theorem 13.0.1 (i), (13.5) |

### Carried modules (2005 theorems)

Carried from the Chapter 10 project `InvariantMeasures` (1871 theorems): all 89 modules of that
project, identical to the copies there except for the namespace. Its own Chapter 10 modules (316
theorems): `Invariance` (39), `MinimalInvariant` (22), `AtomInvariant` (30), `SplitInvariant` (8),
`UniqueInvariant` (18), `PositiveNull` (14), `CountableInvariant` (22), `QueueInvariant` (19),
`MG1Invariant` (25), `ModelInvariant` (11), `QueueInvariantMinimal` (26), `LadderInvariant` (42),
`GIG1Invariant` (9), `RenewalInvariant` (17), `LinearInvariant` (14). Invariant measures and
positive and positive Harris chains (`IsInvariant`, `IsInvariantMeasure`, `IsPositive`,
`IsPositiveHarris`), Proposition 10.1.1 (`proposition_10_1_1`), mean return times
(`meanReturnTime`, `meanReturnTime_eq_tabooPotKernel`), the measure `μ°_α` of an atom
(`atomMeasure`, `theorem_10_2_1_ii_smul`) and Kac's theorem (`theorem_10_2_2`), the taboo measures
`λ _αPⁿ` (`tabooSeq`), Proposition 10.4.1 (`proposition_10_4_1_i`, `proposition_10_4_1_ii`),
skeletons (`theorem_10_4_5_positive`), Theorem 10.4.9 (`theorem_10_4_9_equiv`), the invariant
probability (`stationaryDist`) and the linked forward recurrence time chain (`linkedFwdRec`,
`fwdRecInv`) are used. No Chapter 13 module depends, directly or through other modules, on
`QueueInvariant`, `MG1Invariant`, `ModelInvariant`, `QueueInvariantMinimal`, `LadderInvariant`,
`GIG1Invariant`, `RenewalInvariant` or `LinearInvariant`.

Carried in turn by `InvariantMeasures` from the Chapter 9 project `HarrisRecurrence` (1269
theorems; see those projects' READMEs for how they differ from the originals):

* Its own Chapter 9 modules (212 theorems): `HarrisDefinitions` (29), `HarrisProperties` (15),
  `HarrisDecomposition` (18), `SupermartingaleDrift` (14), `NonEvanescence` (21),
  `TopologicalRecurrence` (21), `TopologicalExamples` (33), `DriftHarris` (29),
  `StochasticComparison` (32). Harris chains (`IsHarris`), `Q ≤ L` (`harrisQ_le_hitProb`),
  Proposition 9.1.1 (`proposition_9_1_1`), Theorem 9.1.4 (`theorem_9_1_4`), the Harris
  decomposition (`theorem_9_1_5`, `IsMaximalHarrisSet`) and Harris skeletons (`theorem_9_1_6`) are
  used. No Chapter 13 module depends on `SupermartingaleDrift`, `NonEvanescence`,
  `TopologicalRecurrence`, `TopologicalExamples`, `DriftHarris` or `StochasticComparison`.
* From the Chapter 8 project `TransienceRecurrence` (220 theorems): `UniformTransience` (46),
  `Decompositions` (8), `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23),
  `CountableClassification` (18), `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16),
  `SkipFreeWalk` (15), `RandomWalkMeanZero` (5). Recurrent chains (`IsRecurrentChain`), the
  first-entrance and last-exit decompositions (`firstEntrance_decomposition`,
  `lastExit_decomposition`) and the recurrence of the split chain
  (`Minorization.isRecurrentChain_split_of_isRecurrentChain`) are used. No Chapter 13 module
  depends on `RandomWalkIntegers`, `RandomWalkHalfLine`, `SkipFreeWalk` or `RandomWalkMeanZero`.
* From the Chapter 6 project `TopologyContinuity` (130 theorems): `FellerChains` (40), `TChains`
  (14), `EChains` (16), `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16),
  `TChainModels` (10), `EChainsStability` (12). No Chapter 13 module depends on any of them.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` (`pathKernel`),
  the kernels `U`, `U_A`, `_APⁿ` and `I_A` (`potKernel`, `tabooPotKernel`, `tabooKernel`,
  `indKernel`), skeletons (`skeleton`), hitting probabilities and return times (`hitProb`,
  `firstReturn`) and taboo probabilities (`tabooProb`) are used throughout. No Chapter 13 module
  depends on `StateSpaces` or `SpecificMatrices`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Irreducibility (`IsPhiIrreducible`, `IsMaximalIrreducibility`,
  `maxIrrMeasure`) and the positivity of hitting probabilities (`hitProb_pos_iff`) are used. No
  Chapter 13 module depends on `CountableIrreducibility`, `RandomWalkIrreducibility`,
  `LinearControllability` or `LinearIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Atoms (`IsAtom`,
  `IsAccessibleAtom`), minorizations and the split chain (`Minorization`,
  `Minorization.splitKernel`, `Minorization.checkAlpha`, `Minorization.split`,
  `Minorization.theorem_5_1_3_ii`), small and petite sets (`IsSmallSet`, `theorem_5_2_2`,
  `IsPetite`), periods, cycles and aperiodicity (`IsPeriod`, `IsCycle`, `IsAperiodic`,
  `IsStronglyAperiodic`, `smallTimes`, `proposition_5_4_5_iii`, `setGcd`) and the forward
  recurrence time chain (`fwdRecKernel`) are used. No Chapter 13 module depends on
  `SmallSetsModels`, `SpreadOut` or `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). No Chapter 13
  module depends on any of them.

Carried by `InvariantMeasures` from the Chapter 5 project `PseudoAtoms` directly (286 theorems):
`ModelKernels` (19), `ModelCountableModels` (9), `ModelQueues` (16), `ModelStorage` (18),
`ModelRenewal` (29), `SpecificKernels` (42), `Regeneration` (12), `PoissonCounts` (12),
`RenewalSkeletons` (53), `LadderChains` (25), `GIG1Embedding` (37), `GIG1SmallSets` (7) and
`RenewalSmallSets` (7). No Chapter 13 module depends on any of them.

Carried from the Chapter 11 project `DriftRegularity` (134 theorems): its modules `Comparison`
(33), `RegularSets` (29), `FosterCriterion` (27), `RegularityConverse` (38) and
`AtomHittingBounds` (7). They are identical to the copies in `DriftRegularity` except for the
namespace, the imports, and a paragraph added to each module docstring that records the copy. Its
modules `NonPositivity`, `DriftExamples`, `GIG1Reentry`, `SetarMarginRecurrence` and
`SetarNullMargins` are not carried. Regular sets, chains and measures (`IsRegularSet`,
`IsRegularChain`, `IsRegularMeasure`, `regV`), the drift condition (V2) (`DriftV2`), Theorem 11.3.4
(`theorem_11_3_4`), Theorems 11.3.11–11.3.12 (`theorem_11_3_11_ii`, `theorem_11_3_12_i`,
`theorem_11_3_12_ii`), Proposition 11.3.13 (`proposition_11_3_13`), Theorem 11.3.14
(`theorem_11_3_14`) and its counterexample (`theorem_11_3_14_counterexample`), Theorem 11.0.1
(`theorem_11_0_1`), the equivalence of regularity and positivity (`isPositive_of_isRegularSet`,
`exists_regularSet_of_isPositive`) and a bound on mean hitting times
(`meanReturnTime_le_add_of_forall_le`) are used.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
