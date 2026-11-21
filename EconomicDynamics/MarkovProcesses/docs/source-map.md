# Source map

Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), Chapter 3, "Markov
Processes", pp. 85–114 (draft of 21 April 2013). Lean names are relative to `Miao.MarkovProcesses`. See
[corrections](corrections.md).

## Copied from Meyn and Tweedie

| Source | Lean modules |
| --- | --- |
| `StochasticStability/DriftRegularity` (period arithmetic) | `ChainNumberTheory` (helpers prefixed `mc_`) |

## Opening and §3.1 Markov chains (pp. 85–99)

Finite chains use a row-stochastic real matrix `P` and its powers; countable chains use
`P : S → S → ℝ≥0∞` with row sums one and `tsum` products.

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 3.0.1, p. 85 | Markov process, time-homogeneous; finite-dimensional laws of a chain | `mc_IsMarkovProcess`, `mc_IsTimeHomogeneous`, `mc_cylProb`, `mc_HasChainLaw`, `mc_markov_of_chainLaw`, `mc_marginal_of_chainLaw` |
| (3.1), p. 87 | `n`-step transitions | `eq_3_1`, `eq_3_1_countable` |
| Figure 3.1 | | `fig31_communicate`, `fig31_recurrent` |
| Example 3.1.1, p. 87 | Regime shifts: powers, limit, stationary distribution | `example_3_1_1_pow`, `example_3_1_1_tendsto`, `example_3_1_1_stationary` |
| Example 3.1.2, p. 88 | Cyclical moving subsets | `example_3_1_2_pow_even`, `example_3_1_2_pow_odd`, `example_3_1_2_classes`, `example_3_1_2_stationary`, `example_3_1_2_not_tendsto` |
| Example 3.1.3, p. 88 | | `example_3_1_3_pow`, `example_3_1_3_tendsto`, `example_3_1_3_classes` |
| Example 3.1.4, p. 89 | Birth–death chain: transient for `p > 1/2`, positive recurrent for `p < 1/2`, not positive recurrent for `p = 1/2` | `example_3_1_4_irreducible`, `example_3_1_4_transient`, `example_3_1_4_stationary`, `example_3_1_4_half`; recurrence for `p = 1/2` not formalised |
| Example 3.1.5, p. 89 | Random walk on `ℤ` | `example_3_1_5`; `p^n_{ij} → 0` not formalised |
| Example 3.1.6, p. 89 | Random walk with two barriers | `example_3_1_6_classes`, `example_3_1_6_infinite` |
| Definitions 3.1.1–3.1.5, pp. 90–94 | Accessibility, communication, irreducibility, recurrence, transience, period, stationary distribution | `mc_Accessible`, `mc_Communicate`, `mc_communicate_equivalence`, `mc_IsIrreducible`, `mc_IsDecomposable`, `mc_isIrreducible_iff`, `mc_IsRecurrent`, `mc_IsTransient`, `mc_period`, `mc_IsAperiodic`, `mc_IsPeriodic`, `mc_period_spec`, `mc_IsStationary` |
| Theorem 3.1.1, p. 91 | Classes of finite chains | `theorem_3_1_1a`, `theorem_3_1_1b`, `theorem_3_1_1c`, `theorem_3_1_1a_countable`, `theorem_3_1_1b_proof_counterexample`, `theorem_3_1_1b_countable_counterexample` |
| Theorem 3.1.2, p. 92 | Period is a class property | `theorem_3_1_2`, `theorem_3_1_2_countable` |
| Theorem 3.1.3, p. 94 | Convergence to the unique stationary distribution | `theorem_3_1_3`, `theorem_3_1_3_mono`, `theorem_3_1_3_anti`, `theorem_3_1_3_min_step`, `theorem_3_1_3_max_step`, `theorem_3_1_3_gap_step`, `theorem_3_1_3_counterexample` |
| p. 97 | Non-irreducible finite chains: existence, uniqueness, decomposition | `mc_exists_stationary`, `mc_stationary_unique_of_irreducible`, `mc_stationary_pos_of_irreducible`, `mc_irreducible_stationary`, `stationary_p97_transient`, `stationary_p97_class`, `stationary_p97_decomposition`, `stationary_p97_infinite` |
| Theorem 3.1.4, p. 96 | Irreducible and aperiodic iff some power is positive (countable case corrected) | `theorem_3_1_4`, `theorem_3_1_4_countable`, `theorem_3_1_4_countable_counterexample` |
| Definition 3.1.6, p. 98 | Transient, null and positive recurrent states | `mc_IsTransientE`, `mc_IsRecurrentE`, `mc_IsPositiveRecurrentE`, `mc_IsNullRecurrentE`, `mc_hitE`, `mc_meanRetE` |
| Theorem 3.1.5, p. 98 | The trichotomy for irreducible aperiodic countable chains | `theorem_3_1_5a`, `theorem_3_1_5b`, `theorem_3_1_5c`, `theorem_3_1_5_trichotomy`, `theorem_3_1_5_finite`, `mc_first_entrance`, `mc_visits_eq`, `mc_isTransientE_iff`, `mc_recurrent_of_stationary`, `mc_stationary_eq_inv`; the limits `p^k_{ij} → 0` in (b) and `→ π_j` in (c) are not formalised (renewal theorem) |
| Remark 3.1.1, Ex 1 | Ergodic sets are recurrent classes (corrected) | `remark_3_1_1_literal`, `mc_IsErgodicSet`, `ex_3_1` |
| Ex 3 | Truncated birth–death chain | `ex_3_3`, `ex_3_3_half`, `ex_3_3_limit_lt`, `ex_3_3_limit_gt`, `ex33_irreducible` |
| Ex 6 | Doubly stochastic chains: uniform stationary distribution | `ex_3_6`, `ex_3_6_irreducible` |

## Copied from Stokey–Lucas–Prescott

| Source | Lean modules (SLP-numbered results prefixed `slp_`, helpers `gp_`) |
| --- | --- |
| `RecursiveMethods/MarkovProcesses` (Ch 8) | `GeneralSLPTransitionFunctions` (`markovOp`, `markovOpR`, `adjointOp`, `kpow`, `IsFeller`, `IsMonotoneTF`) |
| `RecursiveMethods/StrongConvergence` (Ch 11) | `ConvergenceSLPTotalVariation`, `ConvergenceSLPTVConvergence`, `ConvergenceSLPConditionM` (`tvDist`, `ConditionMFor`, `ConditionM`) |
| `RecursiveMethods/WeakConvergence` (Ch 12) | `ConvergenceSLPWeakBasics`, `ConvergenceSLPPortmanteau`, `ConvergenceSLPDetermining`, `ConvergenceSLPDistributionFunctions`, `ConvergenceSLPDistributionConvergence`, `ConvergenceSLPHelly`, `ConvergenceSLPFellerInvariant`, `ConvergenceSLPMonotoneProcesses`, `ConvergenceSLPParameters` (`ConvWeak`, `Dominates`) |

## §3.2 General Markov processes

| Source | Claim | Lean |
| --- | --- | --- |
| Def 3.2.1, p. 99 | Stochastic kernel, transition function | `IsStochasticKernel`, `definition_3_2_1`, `definition_3_2_1_transition` |
| Thm 3.2.1, p. 100 | Direct product `P₁ ⊗ P₂` | `theorem_3_2_1` |
| Thm 3.2.2, (3.2), p. 100 | Kolmogorov extension (standard Borel) | `theorem_3_2_2`, `eq_3_2_iff`, `gp_extendBox` |
| Thm 3.2.3, Remark 3.2.1, p. 101 | Markov process of `(μ₀, P)`, canonical space | `markovPath`, `theorem_3_2_3`, `theorem_3_2_3_transition`, `theorem_3_2_3_marginal` |
| Thm 3.2.4, p. 102 | Ionescu Tulcea | `tulceaFD`, `tulceaFD_zero`, `tulceaFD_succ`, `theorem_3_2_4`, `gp_eq_of_map_frestrictLe` |
| Thm 3.2.5, (3.4), (3.5), Ex 2 | `Pⁿ` transition functions, Chapman–Kolmogorov | `theorem_3_2_5`, `eq_3_4`, `eq_3_4_unique`, `eq_3_5`, `ex_3_2` |
| Def 3.2.2, Ex 4, p. 103 | `T`, `T*`, duality | `markovOpR`, `adjointOp`, `ex_3_4` |
| pp. 103–104 | `T⁽ⁿ⁺ᵐ⁾`, `T*⁽ⁿ⁺ᵐ⁾`, `λₙ = T*ⁿλ₀`, invariant distributions | `eq_p103_T`, `eq_p103_Tstar`, `eq_p104_iterate`, `IsInvariantDist`, `isInvariantDist_iff` |

## §3.3.1 Strong convergence

| Source | Claim | Lean |
| --- | --- | --- |
| (3.6), p. 104 | `dTV` | `dTV`, `gp_tvDist_eq_two_mul_dTV` |
| p. 105 | metric, complete | `eq_p105_metric`, `eq_p105_complete` |
| (3.7), Ex 5(a)(b) | TV formulas | `eq_3_7`, `ex_3_5a`, `ex_3_5b` |
| Def 3.3.1 | strong convergence | `ConvStrongly` |
| Condition M, Thm 3.3.1 | geometric convergence and converse | `ConditionMFor`, `theorem_3_3_1`, `theorem_3_3_1_contraction`, `theorem_3_3_1_invariant`, `theorem_3_3_1_converse` |
| Minorization, Prop 3.3.1 | | `MinorizationFor`, `Minorization`, `proposition_3_3_1`, `proposition_3_3_1_forward`, `proposition_3_3_1_counterexample`, `proposition_3_3_1_of_atom` |
| Examples 3.3.1–3.3.3 | | `example_3_3_1`, `example_3_3_2`, `example_3_3_3`, `example_3_3_3_finite` |

## §3.3.2 Weak convergence

| Source | Claim | Lean |
| --- | --- | --- |
| p. 104, p. 108 | strong ⇒ weak; `δ_{1/n}` | `eq_p104_strong_imp_weak`, `eq_p108_dirac` |
| Defs 3.3.2–3.3.4 | weak convergence, tight, Feller | `definition_3_3_2`, `IsTightFamily`, `definition_3_3_4` |
| Thm 3.3.2 | Prohorov (corrected) | `theorem_3_3_2`, `theorem_3_3_2_counterexample` |
| Thm 3.3.3, Cor 3.3.1 | Krylov–Bogolubov | `theorem_3_3_3`, `corollary_3_3_1` |
| Def 3.3.5, pp. 111–112 | invariant sets, ergodic measures, example | `IsPInvariantSet`, `IsErgodicMeasure`, `IsErgodicSetBook`, `definition_3_3_5_ergodicSet_eq_empty`, `example_p111_invariant`, `example_p111_ergodic` |
| Thm 3.3.4 | convex, extreme points, singular | `theorem_3_3_4_convex`, `theorem_3_3_4_extreme`, `theorem_3_3_4_singular`, `theorem_3_3_4_combination_counterexample` |
| Def 3.3.6, Mixing, Thm 3.3.5 | monotone processes | `definition_3_3_6`, `MixingCondition`, `theorem_3_3_5` |
| Thm 3.3.6 | parameters | `theorem_3_3_6`, `theorem_3_3_6_euclidean` |
