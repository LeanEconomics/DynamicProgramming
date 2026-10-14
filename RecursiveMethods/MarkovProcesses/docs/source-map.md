# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 8, pp. 210–238. Lean names are relative to `StokeyLucasPrescott.MarkovProcesses`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## §8.1 Transition functions

| Source | Claim | Lean |
| --- | --- | --- |
| p. 212 | Transition functions | `IsTransitionFunction`, `isTransitionFunction_iff` |
| (1)–(2), p. 213 | The Markov operator `T` and its adjoint `T*` | `markovOp`, `markovOpR`, `adjointOp`, `markovOp_indicator`, `adjointOp_apply` |
| Theorem 8.1, p. 213 | `T : M⁺ → M⁺`; corollary `T : B → B` | `theorem_8_1`, `integrable_of_bounded`, `theorem_8_1_cor` |
| Ex 8.1, p. 215 | Linearity of `T` | `ex_8_1` |
| Theorem 8.2, p. 215 | `T* : Λ → Λ` | `theorem_8_2` |
| Ex 8.2, p. 216 | `T*` is affine | `ex_8_2` |
| Theorem 8.3, p. 216 | `∫ Tf dλ = ∫ f d(T*λ)`; corollary for bounded `f` | `theorem_8_3`, `theorem_8_3_cor` |
| Ex 8.3, p. 218 | `⟨f, λ⟩` is bilinear | `pairing`, `ex_8_3` |
| Ex 8.4, p. 219 | `Qⁿ` are transition functions; `T⁽ⁿ⁺ᵐ⁾ = TⁿTᵐ`, `T*⁽ⁿ⁺ᵐ⁾ = T*ⁿT*ᵐ` | `kpow`, `kpow_one`, `kpow_add`, `markovOp_comp`, `adjointOp_comp`, `ex_8_4a`, `ex_8_4b` |
| p. 219 | `λₙ = T*λₙ₋₁ = T*ⁿλ₀` | `adjointOp_iterate` |
| p. 220 | The Feller property; monotone transition functions | `IsFeller`, `IsMonotoneTF` |

## §8.2 Probability measures on spaces of sequences

| Source | Claim | Lean |
| --- | --- | --- |
| p. 221 | `μᵗ(z₀, ·)` on `Zᵗ` | `hist`, `measurable_cons`, `measurable_snoc`, `hist_zero_lintegral`, `hist_succ_lintegral` |
| Ex 8.5, p. 221 | `μᵗ` satisfies the hypotheses of Exercise 7.29, with `μᵗ(z₀, Zᵗ) = 1` | `ex_8_5` |
| pp. 221–222 | `μ^∞(z₀, ·)` on `Z^∞`, determined by its values on finite rectangles | `trajKernel`, `isMarkovKernel_trajKernel`, `pathMeasure`, `isProbabilityMeasure_pathMeasure`, `pathMeasure_map_zero`, `prefixHist`, `measurable_prefixHist`, `pathMeasure_marginal`, `muInf`, `muInf_marginal`, `pathMeasure_unique` |
| p. 223 | Stochastic processes | `IsStochasticProcess`, `prefixSigma`, `prefixSigma_mono`, `prefixSigma_le`, `canonical_isStochasticProcess` |
| (2), p. 223; Ex 8.6a–b, p. 224 | The canonical process is Markov, with stationary transitions | `ex_8_6ab`, `ex_8_6ab_condDistrib` |
| Ex 8.6c, p. 224 | I.i.d. shocks give a stationary process | `hist_const`, `window`, `measurable_window`, `ex_8_6c` |
| Ex 8.7, p. 224 | Coin tossing | `ex_8_7a`, `headsAt`, `ex_8_7b`, `ex_8_7c` |

## §8.3 Iterated integrals

| Source | Claim | Lean |
| --- | --- | --- |
| p. 226 | Stochastic kernels | `IsStochasticKernel`, `isStochasticKernel_iff` |
| Theorem 8.4, p. 226 | `TF` is measurable; corollary for bounded `F` | `theorem_8_4`, `theorem_8_4_cor` |
| Theorem 8.5, p. 228 | The direct product `P₁ × P₂` | `directProd`, `isMarkovKernel_directProd`, `theorem_8_5`, `theorem_8_5_unique` |
| Theorem 8.6, p. 229 | Iterated integral (4); corollary for bounded `F` | `theorem_8_6`, `theorem_8_6_cor` |
| Theorem 8.7, p. 231 | (4) for integrable `F` | `theorem_8_7` |
| Theorem 8.8, p. 232 | `∫ F dμᵗ` as an iterated integral | `iterLInt`, `theorem_8_8`, `iterInt`, `theorem_8_8_integrable` |
| Ex 8.8, p. 233 | `μᵗ` is a stochastic kernel; `Q × μᵗ⁻¹ = μᵗ = μᵗ⁻¹ × Q`; (1a) and (1b) | `ex_8_8a`, `lastState`, `measurable_lastState`, `lastState_cons`, `lastState_snoc`, `nextKernel`, `isMarkovKernel_nextKernel`, `nextKernel_apply`, `hist_succ_lintegral_last`, `ex_8_8b`, `hist_succ_eq_cons`, `ex_8_8c_last`, `ex_8_8c_first` |
| Ex 8.9, p. 233 | Product Measure, Tonelli and Fubini theorems | `ex_8_9a`, `ex_8_9b` |

## §8.4 Transitions defined by stochastic difference equations

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 8.9, p. 234 | `Q(z, A) = μ{w : g(z, w) ∈ A}` is a transition function | `theorem_8_9`, `sdeKernel`, `sdeKernel_apply`, `isMarkovKernel_sdeKernel` |
| Ex 8.10, p. 237 | Continuous `g` gives the Feller property | `ex_8_10` |
| Ex 8.11, p. 237 | Second-order processes as first-order processes on `W × W` | `ex_8_11` |
