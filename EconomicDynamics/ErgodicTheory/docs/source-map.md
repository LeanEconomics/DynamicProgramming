# Source map

Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), Chapter 4, "Ergodic Theory
and Stationary Processes". Page numbers are those of the author's draft of 21 April 2013,
pp. 115–130. Lean names are relative to `Miao.ErgodicTheory`. Where the Lean statement departs
from the book, see [corrections](corrections.md).

## Copied from Meyn and Tweedie

| Source | Claim | Lean |
| --- | --- | --- |
| `StochasticStability/LimitTheorems` and its prerequisites | Birkhoff's theorem, the path space of a Markov chain, kernels, the Markov property, invariant events and Lévy's upward theorem | `BirkhoffErgodic`, `PathSpace`, `Kernels`, `MarkovProperty`, `InvariantEvents` (results numbered in Meyn–Tweedie carry the prefix `mt_`) |

## §4.1 Ergodic theorem (pp. 115–120)

| Source | Claim | Lean |
| --- | --- | --- |
| Definitions 4.1.1–4.1.2, p. 115 | Measurable and measure-preserving transformations | `IsMeasurableTransformation`, `isMeasurableTransformation_iff`, `IsMeasurePreserving`, `isMeasurePreserving_iff` |
| Example 4.1.1, p. 116 | The shift on `ℝ^∞` | `example_4_1_1_measurable`, `iterate_shift_one`, `example_4_1_1_not_measurePreserving` |
| Example 4.1.2, p. 116 | The cyclic permutation of `n` points preserves the uniform measure (and is ergodic) | `example_4_1_2`, `exists_uniform_fin`, `example_4_1_2_ergodic` |
| Definitions 4.1.3–4.1.4, p. 116 | Invariant sets, ergodic dynamical systems | `IsTransformationInvariant`, `IsErgodic`, `isErgodic_iff_ergodic` |
| Theorem 4.1.1, p. 117 | Birkhoff: time averages converge a.s. (and in `L¹`) to `E[f | I]`, and to `Ef` when ergodic | `theorem_4_1_1`, `theorem_4_1_1_L1`, `theorem_4_1_1_ergodic`, `theorem_4_1_1_ergodic_L1`, `theorem_4_1_1_condExp_const`, `theorem_4_1_1_sum_succ`, `birkhoffLimit_ae_eq_condExp` |
| Lemma 4.1.1, p. 117 | The maximal ergodic theorem | `lemma_4_1_1`, `lemma_4_1_1_step`, `lemma_4_1_1_on_pos` |

## §4.2 Application to stationary processes (pp. 120–125)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 4.2.1, p. 120 | Stationary process; equivalently the shift preserves the path law | `IsStationary`, `isStationary_iff_map_shift`, `isStationary_iff_measurePreserving`, `pathLaw` |
| p. 120 | IID processes and functions of windows are stationary | `isStationary_of_iid`, `isStationary_comp_window` |
| p. 121 | A measure-preserving map generates stationary processes, and every stationary process arises so | `isStationary_of_measurePreserving`, `stationary_representation` |
| Definitions 4.2.2–4.2.3, p. 123 | Shift-invariant sets, ergodic stationary processes (corrected) | `IsShiftInvariant`, `shiftInvariant_compl_counterexample`, `isShiftInvariant_of_preimage_eq`, `exists_invariant_ae_eq`, `IsErgodicProcess`, `isErgodicProcess_iff_isErgodic`, `invariantField` |
| Theorem 4.2.1, p. 123 | The strong law for stationary processes | `theorem_4_2_1`, `theorem_4_2_1_ergodic`, `eq_4_3`, `condExp_comp_ae_eq` |
| Theorem 4.2.2, p. 124 | Equivalent characterizations of ergodicity | `theorem_4_2_2`, `ex_4_5_a` |
| Definition 4.2.4, Theorem 4.2.3, p. 124 | Mixing implies ergodic | `IsMixing`, `theorem_4_2_3` |
| Theorem 4.2.4, p. 125 | A central limit theorem for stationary ergodic sequences | Not formalised (needs a martingale central limit theorem); its filtration `theorem_4_2_4_filtration_mono` |
| p. 120 | A covariance-stationary process need not be stationary | Not formalised |

## §4.3 Application to stationary Markov processes (pp. 125–129)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 125 | The set `M` of invariant distributions is convex; path measures are affine in the initial law | `invariantDistributions`, `convex_invariantDistributions`, `pathMeasure_add_smul` |
| p. 125, Ex 3 | The chain started at `π` is a stationary Markov process with marginals `π` | `ex_4_3` |
| (4.4), p. 126 | | `eq_4_4` |
| Definition 3.3.5 (used p. 128) | `P`-invariant sets and ergodic invariant measures | `IsPInvariantSet`, `IsErgodicMeasure` |
| Lemma 4.3.1, p. 126 | Shift-invariant events are `{x₀ ∈ A₁}` up to null sets, with `A₁` `P`-invariant | `lemma_4_3_1`, `expectFn_harmonic_of_invariant` |
| p. 128 | Restrictions of `π` to invariant sets | `isInvariant_restrict`, `isInvariant_restrict_compl`, `setLIntegral_compl_eq_zero` |
| Theorem 4.3.1, p. 126 | Ergodic invariant measures are the extreme points of `M` | `theorem_4_3_1`, `theorem_4_3_1_iff_isErgodicMeasure`, `not_mem_extremePoints_of_invariantSet`, `eq_of_ergodic_of_absolutelyContinuous` |
| Corollary 4.3.1, p. 128 | | `corollary_4_3_1` |
| Theorem 4.3.2, p. 128 | The strong law for stationary Markov processes | `theorem_4_3_2`, `ex_4_5_b` |

## §4.4 Exercises (pp. 129–130)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 1 | Invariant sets form a σ-algebra | `ex_4_1`, `ex_4_1_empty`, `ex_4_1_compl`, `ex_4_1_iUnion` |
| Ex 2 | `Ef = E[f ∘ θ]` | `ex_4_2` |
| Ex 3 | The stationary Markov process | `ex_4_3` |
| Ex 4 | Conditional independence (corrected) | `ex_4_4`, `ex_4_4_of_condExp_eq`, `ex_4_4_one`, `ex_4_4_counterexample` |
| Ex 5 | Theorems 4.2.2 and 4.3.2 | `theorem_4_2_2`, `ex_4_5_a`, `theorem_4_3_2`, `ex_4_5_b` |
| Ex 6 | Distinct ergodic invariant measures are mutually singular | `ex_4_6`, `ex_4_6_markov` |
| Ex 7 | A Gaussian stationary sequence with `R_n → 0` is ergodic | Partial: mixing implies ergodic (`ex_4_7_reduction`), covariances of linear combinations (`HasCovariance`, `IsCenteredGaussian`, `integral_sum_mul_sum`, `ex_4_7_cross_covariance`) and mixing for characters (`ex_4_7_charFun`); the passage from characters to sets is not formalised |
