# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 11, pp. 256–287. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.DriftRegularity`; names from Mathlib are marked as such. Names
marked "carried" are in the modules copied from the Chapter 1–6 and 8–10 projects (see the
[README](../README.md)). "`ψ`-irreducible" is `IsMaximalIrreducibility P ψ` unless stated
otherwise, and `B⁺(X)` is the class of measurable sets of positive `ψ`-measure. `E_x[τ_A]` is
`meanReturnTime P A x` and `E_x[σ_A]` is `meanHitTime P A x`, both in `[0, ∞]`. "CG" marks a
statement that assumes `B(X)` countably generated. Every place where the Lean statement departs
from the book is listed in [corrections](corrections.md).

## Chapter 11 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 256 | Stationarity as a starting point in time series; two other descriptions of positive recurrence | Not formalised (informal) |
| (11.1), p. 256 | For a ψ-irreducible chain, `C` is regular if `sup_{x ∈ C} E_x[τ_B] < ∞` for every `B ∈ B⁺(X)`; the chain is regular if `X` has a countable cover by regular sets | `IsRegularSet` (includes measurability of `C`), `IsRegularChain`; `IsRegularOn` (a countable union of regular sets covers `S`), `isRegularChain_iff`; `IsRegularSet.subset`, `isRegularSet_empty`, `IsRegularSet.union` |
| p. 256 | With a finite invariant measure and an atom `α ∈ B⁺(X)`, `E_α[τ_α] < ∞` (Theorem 10.2.1) | Kac's theorem `theorem_10_2_2` (carried); used in `theorem_11_1_2_i` |
| (11.2), p. 256 | `ΔV(x) = ∫ P(x, dy) V(y) − V(x) = E_x[V(Φ₁) − V(Φ₀)]` | `drift` (carried: extended-valued, for `V : X → [0, ∞]`), `driftR` (carried: real-valued); (V2) is written without `ΔV`, see `DriftV2` below |
| pp. 256–257 | Drift towards a petite set gives recurrence and Harris recurrence, drift away gives transience (Chapters 8 and 9) | Not formalised here (remark; carried from Chapters 8 and 9) |
| Theorem 11.0.1, (11.3)–(11.4), p. 257 | For a Harris recurrent chain with invariant measure `π`, equivalent: (i) `π(X) < ∞`; (ii) some petite `C` has `sup_{x ∈ C} E_x[τ_C] ≤ M_C < ∞`; (iii) (V2) holds for a petite `C` and some `V` finite at one state | (ii) needs `C ≠ ∅` (see corrections). Corrected: `theorem_11_0_1` (CG; nonzero invariant `π`; (ii) for a non-empty petite `C`; (iii) with `b ≠ ∞` and measurable `V`) |
| p. 257 | When (iii) holds, `V` is finite on a full absorbing set `S` on which the chain is regular, and any sublevel set of `V` satisfies (11.3) | `theorem_11_0_1_sublevel` (CG: `{V < ∞}` is full and absorbing and the chain is regular on it; a sublevel set `{V ≤ ℓ}`, `ℓ < ∞`, in `B⁺(X)` is petite and satisfies (11.3)). The claim for every sublevel set is false: `theorem_11_0_1_counterexample` (`toFalseKernel`) |
| p. 257 | Proof: Theorem 10.4.10 with Theorem 11.1.4; Theorem 11.3.11; Proposition 11.3.13 | In the proof of `theorem_11_0_1`: `exists_regularSet_of_isPositive`, `theorem_11_3_14`, `theorem_10_4_10_ii` (carried), `regV_drift`, `theorem_11_0_1_sublevel` |
| p. 257 | Motivation through §11.2; Dynkin's formula; practical use of (11.4) in §11.4 | Not formalised (informal) |
| (11.5)–(11.6), p. 257 | If `ΔV ≥ 0` off `C` and the increments are bounded in mean, `E_x[τ_C] = ∞` for `x ∈ Cᶜ` | The precise statement, with the further condition (11.44), is Theorem 11.5.1: `theorem_11_5_1` (§11.5.1 below) |
| p. 257 | Structural results through the Nummelin splitting in §11.1 | §11.1 below |

## §11.1 Regular chains

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 11.1.1, p. 258 | For an irreducible chain on a countable space, positive recurrence and regularity are equivalent | `proposition_11_1_1` (countable `X` with measurable singletons, a maximal irreducibility measure charging every state) |
| p. 258 | Proof: regularity implies positivity by Theorem 10.2.2 | `isPositive_of_isRegularSet` (CG; a regular set in `B⁺(X)` makes the chain positive, through `theorem_10_4_10_ii`, carried), `IsRegularChain.isPositiveHarris` (CG), `IsRegularOn.exists_pos` |
| p. 258 | `E_x[τ_x] ≥ ₓPⁿ(x, y) [E_y[τ_x] + n]` "for any fixed states `x, y`" | Fails for `y = x`: `proposition_11_1_1_ineq_counterexample`. Corrected: `proposition_11_1_1_ineq` (`y ≠ x`); for a general set, `tabooProb_mul_le_meanReturnTime` (`y ∉ A`); `add_toENNReal_firstReturn_shift_le` (pathwise `n + τ_A ∘ θⁿ ≤ τ_A` on `{Φₙ ∉ A, τ_A ≥ n}`) |
| p. 258 | Irreducibility gives `ₓPⁿ(x, y) > 0` for some `n`, hence `E_y[τ_x] < ∞` | In the proof of `proposition_11_1_1` |
| (11.7), p. 258 | For a positive chain and `A ∈ B⁺(X)`, `E_x[τ_A] < ∞` for `π`-almost every `x ∈ A`, from (10.32) | `eq_11_7` (CG; for every measurable `A` with `π(A) > 0`, through `theorem_10_4_10_i_forall`, carried) |
| p. 258 | "Almost-regular" sets | Not formalised (remark) |
| Theorem 11.1.2 (i), (11.8), p. 258 | For an accessible atom `α ∈ B⁺(X)` of a positive chain, `X = S ∪ N` with `S` full and absorbing and `Φ` regular on `S` | `theorem_11_1_2_i` (CG; `S = {x : E_x[τ_α] < ∞}` full, absorbing, and the chain regular on it; `IsAccessibleAtom`, carried) |
| Theorem 11.1.2 (ii), (11.9), p. 258 | `Φ` is regular iff `E_x[τ_α] < ∞` for every `x` | `theorem_11_1_2_ii` (CG) |
| p. 258 | Proof: `S` is absorbing; `E_α[τ_α] < ∞` by "Theorem 10.4.10 (ii)"; `S` full by Proposition 4.2.3 | `theorem_10_2_2` (carried) gives `E_a[τ_α] < ∞`; `IsAccessibleAtom.isRegularSet` (an accessible atom with `E_a[τ_α] < ∞` is regular); `S` is the finiteness set of `V_α`, and Proposition 11.3.13 (`proposition_11_3_13`) gives fullness, absorption and regularity on `S` |
| p. 259 | For `B ∈ B⁺(X)`, `B ⊆ αᶜ`: `E_w[τ_B] ≥ _BPⁿ(w, α) E_α[τ_B]`, so `E_α[τ_B] < ∞` | Not needed: `IsAccessibleAtom.isRegularSet` comes from Theorem 11.3.14 (`theorem_11_3_14`), with `IsAtom.isPetite` (a non-empty atom is petite) |
| (11.10), p. 259 | `S_n = {y : E_y[τ_α] ≤ n}` | Replaced by the sublevel sets `{V_α ≤ ℓ}` of Proposition 11.3.13 (`proposition_11_3_13`) |
| (11.11), p. 259 | `E_x[τ_B] ≤ E_x[τ_α] + E_α[τ_B]` | `eq_11_11` (any atom, any `a ∈ α`), `meanReturnTime_le_add_of_forall_le` (`E_x[τ_B] ≤ E_x[τ_A] + sup_{y ∈ A} E_y[τ_B]`, strong Markov property at `τ_A`; `lintegral_shiftAt_firstReturn`, carried), `toENNReal_firstReturn_le_shift` (pathwise `τ_B ≤ t + τ_B ∘ θᵗ`); `IsAtom.meanReturnTime_eq` (`E_y[τ_B]` is constant on `α`) |
| p. 259 | Proof of (ii): under (11.9), `X = S`; the converse is obvious | In the proof of `theorem_11_1_2_ii` |
| (11.12), p. 259 | The chain `P(0, 0) = 1`, `P(j, 0) = β_j > 0`, `P(j, j + 1) = 1 − β_j` is positive and regular on `{0}`, but not regular if `Σ_j Π_{k ≤ j} β_k = ∞`, so `N = {1, 2, …}` | The condition is wrong: `nullSet_example_counterexample` (`β ≡ 1`). Corrected: `nullSet_example` (for `0 < β_j ≤ 1`: positive with invariant probability `δ₀`, `{0}` a regular set in `B⁺`, and if `Σ_j Π_{k ≤ j} (1 − β_k) = ∞` then `E_1[τ_0] = ∞` and the chain is not regular); `nullSetMeas`, `nullSetKernel`, `isMarkovKernel_nullSetKernel`, `lintegral_nullSetKernel`, `nullSet_meanHitTime_ge` (`E_j[σ_0] ≥ Σ_{n<N} Π_{k<n} (1 − β_{j+k})`) |
| p. 259 | The weak form of irreducibility allows such null sets; on a countable space with the usual irreducibility they cannot occur | Not formalised (remark); the countable case is `proposition_11_1_1` |
| Proposition 11.1.3, (11.13), p. 259 | A strongly aperiodic positive chain has `X = S ∪ N` with `S` full and absorbing and `Φ` regular on `S` | `proposition_11_1_3` (CG; a positive chain with a minorization `M : Minorization P`, carried, on a set `C ∈ B⁺(X)`) |
| (11.14), p. 260 | Proof: the split chain is positive (Proposition 10.4.2), `Ě_{xᵢ}[τ_α̌] < ∞` for `π̌`-a.e. `xᵢ`, and Theorem 11.1.2 for `Φ̌` | `exists_regular_of_minorization` (CG: a regular set in `B⁺(X)` exists). The split chain has the invariant probability `π*` (`proposition_10_4_1_ii`, carried); the atom `α̌ = C₁` is regular by Kac's theorem (`theorem_10_2_2`) and Theorem 11.3.14; `V_α̌` solves (V2) for `Φ̌` |
| p. 260 | `E_x[τ_B] ≤ Ě_{x₀}[τ_B̌] + Ě_{x₁}[τ_B̌]`, so the copies `S_n` are regular for `Φ` | `meanReturnTime_le_split` (`B̌ = B × {0, 1}`; `Minorization.splitKernel`, carried); the sets `{x : V_α̌(x₀) ≤ n}` are regular for `Φ`, in the proof of `exists_regular_of_minorization`; the full absorbing set from `proposition_11_3_13` |
| Theorem 11.1.4, (11.15), p. 260 | A ψ-irreducible chain is positive iff `X = S ∪ N` with `S` full and absorbing and `Φ` regular on `S` | `theorem_11_1_4` (CG; no aperiodicity); the key step `exists_regularSet_of_isPositive` (CG: a positive chain has a regular set in `B⁺(X)`) |
| p. 260 | Proof: a Nummelin splitting for some `m`-skeleton (Proposition 5.4.5), then Proposition 11.1.3 for the skeleton | Replaced: Proposition 5.4.5 needs aperiodicity. The lazy chain `K = ½ (I + P)`: `lazyWeights`, `lazyKernel`, `isSamplingDist_lazyWeights`, `isMarkovKernel_lazyKernel`, `lintegral_lazyKernel`, `lazy_pow_succ_apply`, `lazy_pow_ge` (`Kⁿ ≥ 2⁻ⁿ Σ_{j ≤ n} Pʲ`), `lazy_pow_le` (`Kⁿ ≤ Σ_{j ≤ n} Pʲ`), `isPhiIrreducible_of_pow_pos`, `isMaximalIrreducibility_lazy_pow`, `isPositive_lazy_pow`; a small set from `theorem_5_2_2` (carried) gives a minorization for `Kᴹ` |
| p. 260 | `τ_B ≤ m τ_B^m`, so each `S_n` is regular for `Φ` | `meanReturnTime_le_skeleton` (`E_x[τ_B] ≤ m E^{(m)}_x[τ_B]` for `Pᵐ`, `m ≥ 1`), `mem_of_firstReturn_eq`, `firstReturn_le_of_mem`; for the lazy chain, `meanReturnTime_le_lazy` (`E_x[τ_B] ≤ E^K_x[τ_B]`, by the minimality in `theorem_11_3_5_iii`) |
| p. 260 | The absorbing set of the skeleton is absorbing for `Φ` (implicit) | Not needed: the full absorbing set for `Φ` comes from `proposition_11_3_13` applied to `P` |
| p. 260 | Converse: a petite set `C ⊆ S` with `sup_{x ∈ C} E_x[τ_C] < ∞`, and Theorem 10.4.10 | `IsRegularOn.exists_pos` (a regular set in `B⁺(X)` inside the full set `S`), `isPositive_of_isRegularSet`, in the proof of `theorem_11_1_4` |
| p. 260 | Restricting to a regular absorbing set as for Harris sets; the null set on which regularity fails | Not formalised (remark) |

## §11.2 Drift, hitting times and deterministic models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 261 | Deterministic models foreshadow stochastic ones (Chapters 4 and 7) | Not formalised (informal) |
| (DS1), (11.16), p. 261 | `Φ_{k+1} = F(Φ_k)` with `F : X → X` continuous | `F : X → X` with `Continuous F` on a topological space, in `theorem_11_2_1_i`, `theorem_11_2_1_ii`, `theorem_11_2_1_iii` |
| p. 261 | `Pf = f ∘ F`; the chain is Feller but in general not a T-chain | Not formalised; Theorem 11.2.1 is stated for the map `F` directly |
| p. 261 | Recurrence: some compact `C` has `σ_C(x) < ∞` for every `x`; ultimate boundedness: every trajectory eventually enters and remains in a fixed compact `C` | `IsDSRecurrent`, `IsUltimatelyBounded` |
| p. 261 | The analogy between ultimate boundedness and positivity | Not formalised (remark) |
| (DS2), p. 262 | `V ≥ 0`, a compact `C` and `M < ∞` with `V(F(x)) − V(x) ≤ −1` off `C` and `sup_{x ∈ C} V(F(x)) ≤ M` | `DS2` (`V : X → ℝ`, `V ≥ 0`) |
| Theorem 11.2.1 (i), p. 262 | (DS2) implies ultimate boundedness | `theorem_11_2_1_i` (any topological space) |
| p. 262 | Proof: `C* = {Φ(x, i) : x ∈ C, 1 ≤ i ≤ M + 1} ∪ C` is invariant and every trajectory enters `C` | `ds_return` (from `C` the trajectory returns within `⌊M⌋₊ + 1` steps), `ds_hits` (every trajectory enters `C`), `ds_decrease`; the compact set `C ∪ ⋃_{1 ≤ i ≤ ⌊M⌋₊+1} Fⁱ(C)`, in the proof of `theorem_11_2_1_i` |
| Theorem 11.2.1 (ii), p. 262 | A recurrent system satisfies (DS2) | `theorem_11_2_1_ii` (locally compact Hausdorff space) |
| pp. 262–263 | Proof: `V = σ_O` for an open precompact `O ⊇ C₁`, `C = cl O`; `V` is upper semicontinuous (Proposition 6.1.1), hence bounded on compacta | `dsHit` (`σ_O`), in the proof of `theorem_11_2_1_ii` |
| Theorem 11.2.1 (iii), p. 262 | Recurrence and ultimate boundedness are equivalent | `theorem_11_2_1_iii` (locally compact Hausdorff space) |
| p. 263 | Comparison with NSS(F); the time to reach a compact set as the test function; the stochastic analogue | Not formalised (remark) |

## §11.3.1 Mean drift and Dynkin's formula

| Source | Claim | Lean |
| --- | --- | --- |
| p. 263 | (V2) is stronger on `Cᶜ` than (V1) and bounds the drift on `C` | Not formalised (remark) |
| (V2), (11.17), p. 263 | `ΔV(x) ≤ −1 + b 1_C(x)` for some `C`, `b < ∞` and `V : X → [0, ∞]` | `DriftV2` (`PV + 1 ≤ V + b 1_C`), `driftV2_iff_drift` (equal to `drift P V ≤ −1 + b 1_C` in Mathlib's `EReal`; `drift`, carried), `add_one_le_iff_ereal` |
| (11.18)–(11.19), p. 263 | `ΔV ≤ −1` on `Cᶜ`; `ΔV ≤ M` on `C` | `DriftV2.of_notMem` (`PV + 1 ≤ V` off `C`), `DriftV2.le_add` (`PV ≤ V + b`) |
| p. 264 | Foster's conditions for countable chains; the uses of Dynkin's formula in Part III | Not formalised (remark) |
| (11.20), p. 264 | `F_k^Φ = σ{Φ₀, …, Φ_k}`; `Z_k` an adapted sequence, usually `Z(Φ_k)` | `natFilt` (carried), on the path space `ℕ → X` |
| p. 264 | `τⁿ = min{n, τ, inf{k ≥ 0 : Z_k ≥ n}}` | Not used: the comparison theorem is proved in `[0, ∞]` without truncation (`comparison_lintegral`) |
| Theorem 11.3.1, p. 264 | Dynkin's formula: `E_x[Z_{τⁿ}] = E_x[Z₀] + E_x[Σ_{i=1}^{τⁿ} (E[Z_i \| F_{i−1}] − Z_{i−1})]` | `theorem_11_3_1` (any finite measure and filtration; adapted integrable real `Z`; a stopping time bounded by some `N`; the sum is `Σ_{i<τ} (E[Z_{i+1} \| 𝓕_i] − Z_i)`) |
| p. 265 | Proof: telescoping and `{τⁿ ≥ i} ∈ F_{i−1}` | Through Mathlib's Doob decomposition (`martingalePart`, `predictablePart`, Mathlib) and optional stopping (`Submartingale.expected_stoppedValue_mono`, Mathlib), in the proof of `theorem_11_3_1` |
| Proposition 11.3.2, p. 265 | If `E[Z_{k+1} \| F_k] ≤ Z_k − f_k(Φ_k) + s_k(Φ_k)`, then `E_x[Σ_{k<τ} f_k(Φ_k)] ≤ Z₀(x) + E_x[Σ_{k<τ} s_k(Φ_k)]` for every stopping time `τ` | `proposition_11_3_2` (any measure, filtration and adapted `Φ`; `Z_k ≥ 0` and measurable `f_k, s_k ≥ 0`; the drift integrated over every event of `𝓕_k`), `proposition_11_3_2_condExp` (real processes, finite measure, the drift as an a.e. inequality of conditional expectations), `setLIntegral_ofReal_eq` |
| pp. 265–266 | Proof: `f_k ∧ N`, Dynkin's formula for `τⁿ`, monotone convergence | Replaced by `comparison_lintegral` (`∫ Σ_{k<τ} F_k ≤ ∫ Z₀ + ∫ Σ_{k<τ} S_k` from the stepwise inequality on `{n < τ}`), `comparison_partial` (its finite-horizon form); `sumBefore`, `measurable_sumBefore`, `lintegral_sumBefore`, `sumBefore_mono`, `sumBefore_mono_time`, `sumBefore_mono_before`, `sumBefore_eq_of_eq`, `sumBefore_congr`, `sumBefore_const_mul`, `toENNReal_eq_sumBefore_one`, `measurableSet_lt_of_isStoppingTime`, `measurable_toENNReal` |
| p. 265 | The form used later: the comparison theorem for a Markov chain | `comparison_theorem` (`PV_{k+1} + f_k ≤ V_k + s_k` on a set `D` that the chain does not leave before `τ`, under `P_μ`), `comparison_theorem_pathKernel` (time-homogeneous form under `P_x`), `lintegral_coord_zero` |
| Proposition 11.3.3, p. 266 | If `ε_{k+1} ≤ cε_k` on `Aᶜ` and `E[Z_{k+1} \| F_k] ≤ Z_k − ε_k(Φ_k)` for `σ_A > k`, then `E_x[Σ_{i<τ_A} ε_i(Φ_i)] ≤ Z₀(x)` on `Aᶜ` and `≤ ε₀(x) + cPZ₀(x)` everywhere | `proposition_11_3_3` (`Z_k = z_k(Φ_k)`, `P z_{k+1} + ε_k ≤ z_k` off `A`), `lintegral_sumBefore_firstHit_le` (the bound before `σ_A`, every `x`) |
| p. 266 | Proof: Dynkin's formula, monotone convergence, and a restart at time `1` | `firstReturn_eq_firstHit_shift` (`τ_A = 1 + σ_A ∘ θ`), `sumBefore_firstReturn`, `lintegral_shift_one` (Markov property at time `1`), `le_firstHit_iff`, `notMem_of_lt_firstHit`, `withTop_eq_of_forall_le_iff`, `measurableSet_lt_firstHit`, `measurableSet_lt_firstReturn` |
| Theorem 11.3.4, p. 266 | Under (V2), `E_x[τ_C] ≤ V(x) + b 1_C(x)` | `theorem_11_3_4` (measurable `V`, measurable `C`), `meanReturnTime_eq_sumBefore` |
| p. 266 | If `C` is petite and `V` is everywhere finite and bounded on `C`, the chain is positive Harris | `theorem_11_3_4_positiveHarris` (CG; `b ≠ ∞`) |
| p. 267 | Proof: Proposition 11.3.3 with `Z_k = V(Φ_k)`, `ε_k = 1`; `L(x, C) ≡ 1`, Harris by Proposition 9.1.7, positive by Theorem 10.4.10 (ii) | `proposition_11_3_3` with `z_k = V`, `ε_k = 1`, in the proof of `theorem_11_3_4`; for positivity, `nonempty_of_meanReturnTime_ne_top`, `hitProb_eq_one_of_meanReturnTime_ne_top` and `theorem_8_3_6_i` (`C ∈ B⁺(X)`), then `theorem_10_4_10_ii` (positive Harris), all carried |
| p. 267 | Theorem 11.3.11 strengthens this | §11.3.3 below |

## §11.3.2 Hitting times and test functions

| Source | Claim | Lean |
| --- | --- | --- |
| (11.21), p. 267 | `G_A(x, f) = [I + I_{Aᶜ} U_A](x, f) = E_x[Σ_{k=0}^{σ_A} f(Φ_k)]` | `gKernelFn` (the path form), `gKernelFn_eq` (`G_A(x, f) = f(x) + 1_{Aᶜ}(x) U_A(x, f)`); `tabooPotFn` (`U_A(x, f) = E_x[Σ_{k=1}^{τ_A} f(Φ_k)]`), `tabooPotFn_indicator` (`U_A(x, 1_B) = U_A(x, B)`; `tabooPotKernel`, carried), `sumBefore_add_one`, `measurableSet_lt_firstHit_add_one` |
| p. 267 | For `f ≥ 1`, `V = G_C(·, f)` satisfies (V2) and a generalisation used in later chapters | Theorem 11.3.5 (i) is proved for every measurable `f` (`theorem_11_3_5_i`); the drift condition for `G_C(·, f)` with general `f` is not stated separately |
| (11.22), p. 267 | `V_C(x) = G_C(x, X) = 1 + E_x[σ_C]` | `regV`, `gKernelFn_one`, `regV_of_mem` (`V_A = 1` on `A`), `regV_le`, `measurable_regV`; `meanHitTime`, `meanHitTime_of_mem`, `meanHitTime_of_notMem`, `meanHitTime_le_meanReturnTime`, `measurable_meanHitTime`, `measurable_meanReturnTime`, `measurable_toENNReal_firstHit`, `measurable_toENNReal_firstReturn`, `toENNReal_some`, `toENNReal_add_one` |
| Theorem 11.3.5 (i), p. 267 | `P G_A = G_A − I + I_A U_A` | `theorem_11_3_5_i` (as `P G_A(x, f) + f(x) = G_A(x, f) + 1_A(x) U_A(x, f)`, measurable `f`) |
| Theorem 11.3.5 (ii), (11.23), p. 267 | `P V_A(x) = V_A(x) − 1` for `x ∈ Aᶜ` | `theorem_11_3_5_ii` (as `P V_A + 1 = V_A` off `A`) |
| (11.24), p. 267 | `P V_A(x) = E_x[τ_A] − 1` for `x ∈ A` | False: `eq_11_24_counterexample` (`A = X`). Corrected: `P V_A(x) = E_x[τ_A]` on `A` (`theorem_11_3_5_ii`), and everywhere (`lintegral_regV`) |
| p. 267 | Thus if `C ∈ B⁺(X)` is regular, `V_C` solves (11.17) | `regV_drift` (`sup_{x ∈ C} E_x[τ_C] ≤ b` gives `PV_C + 1 ≤ V_C + b 1_C`); for a regular `C ∈ B⁺(X)`, `theorem_11_3_11_ii` |
| Theorem 11.3.5 (iii), (11.25), p. 267 | `V = V_A − 1` is the pointwise minimal solution of `PV ≤ V − 1` on `Aᶜ` | `theorem_11_3_5_iii` (`E_·[σ_A]` solves it, and every measurable `W ≥ 0` solving it has `E_x[σ_A] ≤ W(x)` for every `x`) |
| p. 268 | Proof: `U_A = Σ_k (P I_{Aᶜ})ᵏ P = P G_A`; minimality "exactly as in Theorem 11.3.4" | `lintegral_gKernelFn` (`P G_A = U_A`); `meanReturnTime_eq_one_add` (first-step analysis, `E_x[τ_A] = 1 + ∫ P(x, dy) E_y[σ_A]`); minimality through `lintegral_sumBefore_firstHit_le` |
| Lemma 11.3.6, p. 268 | A solution of (11.17) is finite ψ-a.e. or infinite everywhere | `lemma_11_3_6` (any irreducibility measure, `IsPhiIrreducible`, carried; `b ≠ ∞`) |
| p. 268 | Proof: `PV ≤ V + b`, so `{V < ∞}` is absorbing, and full if non-empty (Proposition 4.2.3) | `isAbsorbing_finite_of_driftV2`; `proposition_4_2_3_i` (carried) |
| Lemma 11.3.7, p. 268 | If `C` is petite, `V_C` is unbounded off petite sets | `lemma_11_3_7` (every sublevel set `{V_C ≤ ℓ}`, `ℓ < ∞`, is petite) |
| p. 268 | Proof: Chebyshev's inequality and Proposition 5.5.4 | `isPetite_meanHitTime_le` (`{x : E_x[σ_C] ≤ ℓ}` is petite), `exists_mem_of_toENNReal_firstHit_lt`, `IsPetite.subset`; `proposition_5_5_4_i` (carried) |
| Proposition 11.3.8, p. 268 | A regular set is petite | `proposition_11_3_8` (CG) |
| p. 268 | Proof: Chebyshev's inequality with a petite `C ∈ B⁺(X)` | `exists_petite_pos` (carried) and `isPetite_meanHitTime_le`, in the proof of `proposition_11_3_8` |

## §11.3.3 Regularity, drifts and petite sets

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 11.3.9, (11.26), p. 269 | Under (V2), `E_x[τ_B] ≤ V(x) + b E_x[Σ_{k<τ_B} 1_C(Φ_k)]` for every `B` | `lemma_11_3_9` (measurable `B`) |
| p. 269 | Proof: Proposition 11.3.2 with `f_k = 1`, `s_k = b 1_C`; Theorem 11.3.4 is the case `B = C` | `comparison_theorem_pathKernel` and `proposition_3_4_4` (carried: `τ_B` is a stopping time), in the proof of `lemma_11_3_9` |
| Lemma 11.3.10, p. 269 | `E_x[Σ_{k<τ_B} K_a(Φ_k, f)] = Σᵢ aᵢ E_x[Σ_{k<τ_B} f(Φ_{k+i})]` | `lemma_11_3_10` (every stopping time, every weight sequence `a`, measurable `f ≥ 0`; `sampledKernel`, carried) |
| p. 269 | Proof: the Markov property and Fubini's theorem | `lintegral_sampledKernel_eq` (`K_a(y, f) = Σᵢ aᵢ Pⁱf(y)`), `setLIntegral_pow_coord` (`E_x[Pⁱf(Φ_k); k < τ] = E_x[f(Φ_{k+i}); k < τ]`) |
| Theorem 11.3.11 (i), p. 270 | If (V2) holds for a petite `C`, every `B ∈ B⁺(X)` has `c(B) < ∞` with `E_x[τ_B] ≤ V(x) + c(B)`; if `V` is bounded on `A`, `A` is regular | `theorem_11_3_11_i` (CG; `b ≠ ∞`), `theorem_11_3_11_i_regular` (CG; every measurable `A` on which `V` is bounded) |
| (11.27), p. 270 | `1_C(x) ≤ ψ_a(B)⁻¹ K_a(x, B)` for a `ψ_a`-petite `C`, with `Σ i aᵢ < ∞` by Proposition 5.5.6 | A `ψ_b`-petite form from `proposition_5_5_5_i` (carried) and a finite window of weights `1_{[0, K)}`, in the proof of `theorem_11_3_11_i` |
| p. 270 | `E_x[Σ_{k<τ_B} 1_B(Φ_{k+i})] ≤ i + 1` | `sumBefore_firstReturn_shift_le` |
| Theorem 11.3.11 (ii), p. 270 | A regular `C ∈ B⁺(X)` is petite, and `V_C` satisfies (V2) and is bounded on every regular set | `theorem_11_3_11_ii` (CG; `b ≠ ∞`) |
| p. 270 | Regular measures: `E_μ[τ_B] < ∞` for every `B ∈ B⁺(X)` | `IsRegularMeasure` (any measure, `E_μ[τ_B] = ∫ μ(dx) E_x[τ_B]`) |
| Theorem 11.3.12 (i), p. 271 | If (V2) holds for a petite `C` and `μ(V) < ∞`, `μ` is regular | `theorem_11_3_12_i` (CG; `μ` a probability) |
| Theorem 11.3.12 (ii), p. 271 | If `μ` is regular and a regular `C ∈ B⁺(X)` exists, some `V` satisfies (V2) with `μ(V) < ∞` | `theorem_11_3_12_ii` (`μ` finite; `V = V_C`) |
| p. 271 | The proof is identical to that of Theorem 11.3.11 and omitted | Proved: in the proofs of `theorem_11_3_12_i` and `theorem_11_3_12_ii` |
| Proposition 11.3.13, p. 271 | If a regular `C ∈ B⁺(X)` exists, the sets `C_V(ℓ) = {V_C ≤ ℓ}` are regular, and `S_C = {V_C < ∞}` is full and absorbing with `Φ` regular on it | `proposition_11_3_13` (CG) |
| p. 271 | Proof: `C` is petite, (V2) for `V_C` by Theorem 11.3.11 (ii), Lemma 11.3.6 | `theorem_11_3_11_ii`, `theorem_11_3_11_i_regular`, `lemma_11_3_6`, in the proof of `proposition_11_3_13` |
| Theorem 11.3.14, p. 271 | For a ψ-irreducible chain, `C` is petite with `sup_{x ∈ C} E_x[τ_C] < ∞` iff `C` is regular and `C ∈ B⁺(X)` | Needs `C ≠ ∅`: `theorem_11_3_14_counterexample`. Corrected: `theorem_11_3_14` (CG; `C` petite, non-empty, with bounded mean return times) |
| p. 271 | Proof of (i) ⇒ (ii): Theorem 11.3.5 and 11.3.11; `C` Harris recurrent, so `C ∈ B⁺(X)` by Proposition 8.3.1 (ii) | `regV_drift`, `theorem_11_3_11_i_regular`; `C ∈ B⁺(X)` from `theorem_8_3_6_i` (carried; non-empty petite `C` with `L(·, C) ≡ 1` on `C`), in the proof of `theorem_11_3_14` |
| Theorem 11.3.15, pp. 271–272 | Equivalent: (i) `Φ` regular; (ii) (V2) for a petite `C` and an everywhere finite `V`; (iii) some petite `C` has `E_x[τ_C]` finite for every `x` and bounded on `C` | `theorem_11_3_15` (CG; as (i) ⇔ (ii) and (i) ⇔ (iii)); `exists_pos_of_iUnion_eq_univ` (a countable cover has a member in `B⁺(X)`) |
| p. 272 | Proof: "by (11.24)"; "from Theorem 11.3.15" | `regV_drift` (the corrected (11.24)), `proposition_11_3_8`, `theorem_11_3_11_ii` and `theorem_11_3_11_i_regular`, in the proof of `theorem_11_3_15` |

## §11.4.1 Some straightforward applications

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 11.4.1, p. 272 | Random walk on a half line with finite mean increment `β < 0` is regular, and every compact set is regular | `proposition_11_4_1` (`E\|W\| < ∞`, ψ-irreducible; `halfLineWalkKernel`, carried) |
| p. 272 | Proof: (11.18) as in Proposition 8.5.1, and (11.19) | `V(x) = x/ε` with `C = [0, x₀]` from the drift (8.54) (`halfLine_drift_neg`, carried) and `halfLine_isPetite_Iic` (carried); `halfLine_integrable_max`, `halfLine_integrable_coe`, `halfLine_integral_coe`; `theorem_11_3_11_i_regular` |
| p. 272 | Transient for `β > 0`, recurrent for `β = 0`; not regular for `β = 0` | The last claim is Proposition 11.5.3 (`proposition_11_5_3`); the others are carried from Chapters 8 and 9 |
| (11.28)–(11.29), p. 273 | For the forward recurrence time chain and `V(x) = x`, `PV(x) = V(x) − 1` for `x ≥ 1` and `PV(0) = Σ_y p(y) y` | `fwdRec_drift` (on `ℤ₊` with renewal state `0`, `fwdRecKernel`, carried: `PV(x) + 1 = x` for `x ≥ 1`, `PV(0) = Σₙ p(n)(n − 1)`), `lintegral_fwdRec_zero`, `fwdRecKernel_pos` |
| p. 273 | The chain is positive if `Σ_y p(y) y < ∞`; since `E_0[τ_0] = Σ_y p(y) y` the drift condition is also necessary, and (11.19) cannot be omitted | `fwdRec_drift` (`E_j[σ_0] = j`, `E_0[τ_0] = Σₙ n p(n)`, and (V2) for `V(x) = x`, `C = {0}` with finite `b` iff `Σₙ n p(n) < ∞`) |
| Proposition 11.4.2, p. 273 | For the simple linear model with non-singular `W`, `E log(1 + \|W\|) < ∞` and `\|α\| < 1`, every compact set is regular and the chain is regular | `proposition_11_4_2` (`ar1Kernel`, carried; ψ-irreducibility and the petiteness of compact sets as hypotheses) |
| p. 273 | Proof: Proposition 6.3.5 for ψ-irreducibility and the T-chain property | Taken as hypotheses (see corrections) |
| (11.30)–(11.31), p. 273 | `V(x) = log(1 + ε\|x\|)` is subadditive, and `V(x) − V(\|α\|x) → log(\|α\|⁻¹)` | `logAbs_add_le`, `logAbs_contract` (for `0 < ρ < 1`, `log(1 + ερ\|x\|) ≤ log(1 + ε\|x\|) + ½ log ρ` for large `\|x\|`) |
| p. 273 | `E V(W) ≤ ¼ log(\|α\|⁻¹)` for small `ε`, so (V2) holds with `C = {\|x\| ≤ r}` | `exists_small_logAbs`, in the proof of `proposition_11_4_2` with `ρ = max(\|α\|, ½)` |
| p. 274 | Comparison with §9.5.1; geometric drift in Chapter 15 | Not formalised (remark) |

## §11.4.2 The GI/G/1 queue with re-entry

| Source | Claim | Lean |
| --- | --- | --- |
| p. 274 | Arrivals at `0 = T₀ < T₁ < ⋯` with i.i.d. interarrival times (mean `1/λ`), i.i.d. service times (mean `1/μ`), independent; after service a customer leaves with probability `r` and re-enters with probability `1 − r` | Interarrival law `G` and service law `H` on `ℝ≥0`, re-entry law `exitLaw r`, `isProbabilityMeasure_exitLaw`, `lintegral_exitLaw` |
| p. 274 | The effective arrival rate `λ_r = λ/r` | Not stated separately; it enters through the load condition `E S / r < E T` |
| p. 274 | `Φₙ = (Nₙ, Rₙ)` at `Tₙ−`, `Nₙ` waiting customers, `Rₙ` residual service, is a Markov chain on `ℤ₊ × ℝ₊` | The chain as a random recursion: `QConfig`, `nextC`, `QConfig.IsFinal`, `cstep`, `qinit`, `qout`, `QNoise`, `qcfg`, `gig1rStep`, `gig1rNoise`, `gig1rKernel`, `isProbabilityMeasure_gig1rNoise`, `isMarkovKernel_gig1rKernel`, `lintegral_gig1rKernel`; `gig1r_isMarkovChain` (a recursion driven by i.i.d. innovations independent of `Φ₀` is a Markov chain with this kernel; `isMarkovChain_of_iid`, carried). The identification with a queue built from global sequences is not formalised |
| p. 274 | (Implicit) each interval ends | `exists_isFinal_or`, `cstep_of_isFinal`, `cstep_of_not_isFinal`, `qcfg_of_isFinal`, `qcfg_succ`, `qcfg_zero_fst`, `qcfg_zero_snd`, `gig1rStep_eq`; `sum_le_of_not_final`, `measure_sum_bdd_eq_zero`, `gig1rNoise_not_final` (every interval ends almost surely when `H[ε, ∞) > 0` for some `ε > 0`); measurability: `measurable_cstep`, `measurable_qinit`, `measurable_qout`, `measurable_qcfg`, `measurableSet_isFinal`, `measurable_gig1rStep` |
| (11.32), p. 274 | The load condition `ρ_r = λ_r/μ < 1` | `E S / r < E T` (`hload`) in `proposition_11_4_3` and `proposition_11_4_4` |
| (11.33), p. 274 | For each `x`, `P_x{Φ_m = [0]} > 0` for large `m`: with positive probability each of the first `m` interarrival times exceeds each of the first `m` service times by `δ`, and none of the first `m` customers re-enters | `exists_good_constants` (`a, δ > 0` with `H[0, a) > 0`, `G(a + δ, ∞) > 0`, from `E S < E T`), `goodNoise`, `goodNoise_eq`, `measurableSet_goodNoise`, `goodProb`, `gig1rNoise_goodNoise`, `goodProb_pos`, `qpot` (`Ψ(N, R) = R + N a`), `cpot`, `good_step`, `gig1r_reach_zero` (`P^{k+1}(x, [0]) ≥ Π_{i ≤ k} goodProb(n + i)` on `{N ≤ n, Ψ ≤ kδ}`), `gig1r_exists_reach` |
| p. 275 | `P_x(Φ_m = [0]) ≤ P_y(Φ_m = [0])` for `x ≥ y` | Not formalised; the uniform bound of `gig1r_reach_zero` replaces it |
| Proposition 11.4.3, p. 275 | Under (11.32), `Φ` is `δ_{[0]}`-irreducible and aperiodic, and every compact subset of `X` is petite | `proposition_11_4_3` (`0 < r ≤ 1`, finite means; also strongly aperiodic, with `maxIrrMeasure` of `δ_{[0]}` maximal; `IsStronglyAperiodic`, `IsAperiodic`, carried) |
| p. 275 | `W_n`, the work in the system at `T_n+`; `V(x) = E_x[W₀]`, `V(x) = E[W_n \| Φ_n = x]`, `PⁿV(x) = E_x[W_n]` | `qworkV` (`V(N, R) = (N + 1) m/r` if the server is free, `R + (N + 2 − r) m/r` otherwise, `m = E S`), `qworkV_nonneg`, `measurable_qworkV`, `qworkV_le`. `W_n` itself is not defined, since the queue on one probability space is not built |
| (11.34), p. 275 | For some `k > 0`, `E_x[W_k] ≤ E_x[W₀] − 1` off `A` and `sup_{x ∈ A} E_x[W_k] < ∞`; this gives (V2) for the `k`-skeleton, and regularity as in Theorem 11.1.4 | With `k = 1` for `V` scaled by `1/c`: `proposition_11_4_4` |
| Proposition 11.4.4, p. 275 | If `ρ_r < 1`, (11.34) holds for a compact `A` and some `k`, and `Φ` is regular | `proposition_11_4_4` (`0 < r ≤ 1`, finite means, `E S > 0`; a compact `A` and `c > 0` with (11.34) for `V/c` and `k = 1`; regular and positive Harris for `maxIrrMeasure` of `δ_{[0]}`) |
| p. 275 | The sets `A_m = {\|x\| ≤ m}` are compact; `k` with `(k/λ)(1 − ρ_r) ≥ 2` | Not used: one step suffices once `V` is scaled; the compact set comes from `gig1r_drift` |
| (11.35), p. 275 | `W_k = W₀ + Σᵢ Σⱼ S(i, j) − ζ_k`, `ζ_k` the busy time in `[0, T_k]` | In expectation, for one interval: `lintegral_qworkV_add_busy` (`E_x[V(Φ₁)] + E[busy time] ≤ V(x) + m/r`), through `qwork`, `cwork`, `measurable_cwork`, `cwork_nonneg`, `qworkV_qout_add_busyfin`, `integral_const_add_mul_nnreal`, `lintegral_cwork_cstep`, `cKernel`, `measurable_orbit_cstep`, `lintegral_cwork_cKernel_pow`, `lintegral_cwork_orbit`, `lintegral_cwork_qcfg` (the expected work plus busy time is preserved by each event); `busyfin`, `measurable_busyfin`, `gig1rBusy`, `gig1rBusy_eq`, `measurable_gig1rBusy` |
| pp. 275–276 | `E_x[ζ_k] ≥ E_x[T_k] − 1` off `A_m`; `λ_r/λ` is the mean number of visits per customer; `E_x[W_k] ≤ E_x[W₀] − (k/λ)(1 − ρ_r) + 1` | `gig1rBusy_ge` (busy time `≥ min(τ, R + s₁ + ⋯ + s_N)`), `tendsto_integral_posPart_sub`, `ae_sum_unbounded`, `measure_half_mean_le_pos`, `gig1r_drift` (a compact `A` and `c > 0` with `E_x[V(Φ₁)] ≤ V(x) − c` off `A`, and `E_x[V(Φ₁)] ≤ V(x) + m/r` everywhere) |

## §11.4.3 Regularity of the scalar SETAR model

| Source | Claim | Lean |
| --- | --- | --- |
| p. 276 | `Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)` for `Xₙ₋₁ ∈ R_j`; a Lebesgue-irreducible T-chain (Proposition 6.3.6) | `setarKernel` (carried), `setarKernel_eq_map`, `setarRegime_of_gt`, `setarRegime_of_le`; `proposition_6_3_6` (carried) |
| p. 276 | Transience in the exterior (Proposition 9.5.4); the margins in §11.5.2 | Not formalised here (Chapter 9 remark); the margins are below |
| (11.36)–(11.40), p. 276 | The interior of the parameter space | The hypothesis `hint` of `proposition_11_4_5` (`θ 0` is `θ(1)`, `θ (Fin.last m)` is `θ(M)`) |
| Proposition 11.4.5, p. 276 | Under (SETAR1)–(SETAR2) the chain is regular in the interior | `proposition_11_4_5` (noise integrable with mean zero; also every compact set regular; `ψ` is Lebesgue measure) |
| (11.41), p. 276 | `∫ P(x, dy) V(y) ≤ V(x) − 1` for `\|x\| > R` | `regular_of_real_drift` (with `PV` bounded on `[−R, R]`, `V ≥ 0` bounded on compacta and compact sets petite: every compact set is regular and the chain is regular) |
| pp. 276–277 | Under (11.36), "straightforward to calculate" positive `a, b` with `1 > θ(1) > −b/a`, `1 > θ(M) > −a/b`, and `V(x) = ax` for `x > 0`, `b\|x\|` for `x ≤ 0` | `setar_interior_slopes`, `pwLin` (`V = a x⁺ + b x⁻`), `pwLin_lipschitz`, `pwLin_nonneg`, `pwLin_le_abs`, `measurable_pwLin`, `pwLin_mul_of_nonneg`, `pwLin_mul_of_nonpos`, `contract_slope` |
| p. 277 | Under (11.37), (11.38), (11.39), piecewise linear test functions with slopes from `φ(1)`, `φ(M)` | `setar_top_drift`, `setar_bot_drift` (the drift at `±∞` for a contracting end or a unit-slope end pushed inwards by its constant), `setar_pwLin_step`, `integral_pwLin_shift_pos`, `integral_pwLin_shift_neg`, `exists_tail_posPart_le`, `setar_regular_of_ends`, `setar_regular_36_39` |
| pp. 277–278 | Under (11.40), the two-step kernel `P²` with `V(x) = ax` / `b\|x\|`, `R(k, j)` and `ζ(k, x)` | Replaced by one step with `max(x + c, d − bx)`, `b = −θ(1)`: `setar_regular_eq_11_40`, `kinkV`, `kinkV_eq_top`, `kinkV_eq_bot`, `integrable_posPart_affine` |
| p. 278 | `φ(M) + θ(M)φ(1) > 0` and `φ(1) + θ(1)φ(M) < 0` give (11.41) for `P²`, hence regularity of the one-step chain | Not needed (one step suffices) |

## §11.5.1 A drift criterion for non-positivity

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 11.5.1, (11.42)–(11.44), p. 278 | If `V ≥ 0` has `ΔV ≥ 0` on `Cᶜ`, `sup_x ∫ P(x, dy) \|V(x) − V(y)\| < ∞`, and `V(x₀) > V(x)` for every `x ∈ C`, then `E_{x₀}[τ_C] = ∞` | `theorem_11_5_1` (real measurable `V`; (11.42) as `V(x) ≤ ∫ V dP(x, ·)` off `C`; (11.43) as `∫⁻ P(x, dy) ‖V(y) − V(x)‖ₑ ≤ B` with `B ≠ ∞`); `integrable_of_increments` |
| pp. 278–279 | Proof: if `E_{x₀}[τ_C] < ∞`, Fubini gives `E_{x₀}[V_{τ_C}] ≥ V(x₀)`, contradicting `V_{τ_C} < V(x₀)` | In the proof of `theorem_11_5_1`; `pathKernel_map_pair`, `lintegral_pair`, `integral_pair`, `setLIntegral_pair`, `setIntegral_pair` (the Markov property for one transition), `mem_of_firstHit_eq` |
| Theorem 11.5.2, p. 279 | For a ψ-irreducible chain, if `V` satisfies (11.42)–(11.43) with `C ∈ B⁺(X)` and `C⁺ = {x : V(x) > sup_{y ∈ C} V(y)} ∈ B⁺(X)`, the chain is non-positive | `theorem_11_5_2` (CG; `C⁺` is `{x : V(y) < V(x) for all y ∈ C}`; the conclusion is `IsNull`, carried) |
| p. 279 | Proof: Theorem 11.1.4 | `theorem_11_5_1` and `theorem_11_1_4`, in the proof of `theorem_11_5_2` |
| p. 279 | In practice `C` is a sublevel set of `V` | Not formalised (remark) |
| p. 279 | Without (11.43) the result fails: on `ℤ₊`, `P(0, i) = 2⁻ⁱ`, `P(i, 0) = P(i, k(i)) = ½` with `k(i) > 2i`, positive Harris with `P₀(τ₀ ≥ n + 1) ≤ 2⁻ⁿ`, and `ΔV(i) = k(i)/2 − i > 0` for `V(i) = i` | `theorem_11_5_2_counterexample` (`k(i) = 2i + 1`; `ΔV(i) = ½`, `C = {0}` and `C⁺ = {i ≥ 1}` in `B⁺`, the chain positive, and (11.43) fails); `escMeas`, `escKernel`, `isMarkovKernel_escKernel`, `tsum_inv_two_pow_succ_eq_one`, `lintegral_escKernel_zero`, `lintegral_escKernel_pos` |
| p. 279 | `k(i)` can give any value of `ΔV(i)` | Not formalised (remark) |
| — | (11.43) is needed only off `C` | `theorem_11_5_1_off`, `theorem_11_5_2_off` (CG), `integrable_of_increment_le` |

## §11.5.2 Applications to random walk and SETAR models

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 11.5.3, p. 279 | Random walk on a half line is regular iff `β < 0` | `proposition_11_5_3` (`E\|W\| < ∞`, ψ-irreducible) |
| pp. 279–280 | Proof: Proposition 11.4.1; for `β ≥ 0`, `V(x) = x` gives (11.42), and homogeneity gives (11.43) | `proposition_11_4_1`; `theorem_11_5_2` with `C = [0, c]`, and `(c, ∞) ∈ B⁺` from `halfLine_pos_Ioi` (through `halfLine_pow_climb`, `Pⁿ(x, [nδ, ∞)) ≥ Γ(δ, ∞)ⁿ`); `halfLine_pos_Ioi_zero` (if `Γ(0, ∞) = 0` and `β ≥ 0` the walk is not ψ-irreducible) |
| p. 280 | The SETAR model is recurrent but not positive on the margins | Propositions 11.5.4 and 11.5.5 below |
| (11.45)–(11.49), p. 280 | The margins of the parameter space | The hypothesis `hreg` of `proposition_11_5_4` and `proposition_11_5_5_all` |
| p. 280 | Test functions `log(u + ax)`; Lemmas 8.5.2, 8.5.3, 9.4.3 and 9.4.4; (SETAR3) | `log_hinge_pointwise`, `log_hinge_drift` (one second-order bound in place of the four lemmas); (SETAR3) as `E W(1)² < ∞` and `E W(M)² < ∞` |
| Proposition 11.5.4, p. 280 | Under (SETAR1)–(SETAR3), the chain is recurrent on the margins | `proposition_11_5_4` (Harris recurrent and recurrent on each of (11.45)–(11.49); `IsHarris`, `IsRecurrentChain`, carried) |
| (11.50), p. 280 | `V(x) = log(u + ax)` for `x > R`, `log(v − bx)` for `x < −R`, `0` on `[−R, R]` | `marginL` (`L(y) = max(u + ay, v − by)`, `V = log L`, `u, v ≥ 1`), `measurable_marginL`, `one_le_marginL`, `marginL_le`, `marginL_neg`; `hinge`, `measurable_hinge`, `hinge_of_le`, `hinge_le`, `max_eq_add_max_sub`, `marginL_eq_hinge_right`, `marginL_eq_hinge_left`, `one_le_hinge_right`, `one_le_hinge_left` |
| p. 280 | `k(x) = φ(M) + θ(M)x`, `h(x) = φ(1) + θ(1)x` | The regime maps inside `setarKernel_eq_map` and `marginL_right_end`, `marginL_left_end` |
| pp. 280–281 | Recurrence on (11.45) and (11.46), in the style of §9.5 | `proposition_11_5_4`, through `setar_harris_of_ends` |
| (11.51)–(11.53), p. 281 | (11.45) with `0 ≤ θ(1) < 1`, `a = b = u = v = 1`, `x > R`: `V₁, …, V₅` and `E_x[V(X₁)] ≤ V(x)` | `marginL_right_end` (random-walk end `θ = 1`, `φ ≤ 0`), `log_hinge_drift`, `log_le_tangent`, `integrable_of_abs_le_affine`, `abs_marginL_add_le`, `abs_log_marginL_add_le` |
| p. 281 | `θ(1) = 0`: `E_x[V(X₁)]` is constant for `x < −R` | `marginL_left_end` (contracting end `0 ≤ θ < 1`) |
| (11.54)–(11.56), pp. 281–282 | `0 < θ(1) < 1`, `x < −R`: `V₆, …, V₁₀` and `E_x[V(X₁)] ≤ V(x)` | `marginL_left_end` (contracting end, through `E L(Y) ≤ L(x)` and `log_le_tangent`) |
| p. 282 | `θ(M) = 1`, `φ(M) = 0`, `θ(1) < 0`: `a = −bθ(M)`, `v − u = aφ(1)`, `log(u + ah(x)) = log(v − bx)` | The slope is wrong: `proposition_11_5_4_slope_correction`. Corrected: `a = −b/θ(1)`; the proof of `proposition_11_5_4` uses `b = 1`, `a = −1/θ(1)`, `u = 1`, `v = max(1, 1 + aφ(1))` |
| (11.57), p. 282 | `E_x[V(X₁)] ≤ V(x)` for `x < −R` | `marginL_left_end` (jumping end `θ < 0`, `b = −aθ`, `u + aφ − v ≤ 0`); `map_mul_noise`, `map_mul_Iio_pos` (the noise `βW`) |
| p. 283 | (11.46) by symmetry | Proved: the mirror choice of constants in `proposition_11_5_4` |
| p. 283 | (11.47) with `a = b = u = v = 1`, using `1 − h(x) ≤ 1 − x`; (11.48) by symmetry | Both proved in `proposition_11_5_4` with `a = b = u = v = 1` |
| (11.58), p. 283 | (11.49): `v − u = bφ(M) = aφ(1)`, `b = −aθ(1) = −a/θ(M)`, `V₁₂`, and `E_x[V(X₁)] ≤ V(x)` for `x > R` | `marginL_right_end` (jumping end `θ < 0`, `a = −bθ`, `v − bφ − u ≤ 0`); in `proposition_11_5_4`, `b = 1`, `a = −θ(M)`, `u = max(1, 1 − φ(M))`, `v = u + φ(M)` |
| p. 283 | The test functions are coercive, (V1) holds off `[−R, R]`, and Theorem 9.1.8 gives recurrence | `setar_harris_of_ends` (Harris recurrence), through `theorem_9_1_8` and `proposition_6_3_6` (carried) |
| Proposition 11.5.5, p. 283 | Under (SETAR1)–(SETAR3) the chain is non-positive on the margins | `proposition_11_5_5_all` (all five margins; only (SETAR1)–(SETAR2) with integrable mean-zero noise; `IsNull` for Lebesgue measure) |
| p. 283 | Proof for `φ(1) < 0`, `φ(1)φ(M) = 1`, `θ(1)φ(M) + θ(M) ≤ 0` | With `φ` and `θ` exchanged (see corrections): `proposition_11_5_5` (`θ(1) < 0`, `θ(1)θ(M) = 1`, `φ(M) + θ(M)φ(1) ≤ 0`, which contains (11.49)) |
| p. 284 | Positive `a, b` with `φ(1) = −b/a`, `φ(M) = −a/b` | With `a = 1`: `b = −θ(1)` in `kinkV` |
| (11.59), p. 284 | `V = V_{cd} + I_{kR}` with `V_{cd}(x) = ax + c` for `x > 0`, `b\|x\| + d` for `x ≤ 0` | `kinkV` (`max(y + c, d − by)`, no bump `I_{kR}`), `measurable_kinkV`, `kinkV_le`, `kinkV_nonneg`, `kinkV_lipschitz` |
| p. 284 | `∫ P(x, dy) \|V(x) − V(y)\| ≤ aE\|W₁\| + bE\|W_M\| + 2(a\|θ(1)\| + b\|θ(M)\|) + 2\|d − c\|`; `V` coercive | `kink_top_incr`, `kink_bot_incr`, `kink_mid_incr`, `kink_K_le`, `kink_K_le'`, `kink_K_le''`, in the proof of `proposition_11_5_5` |
| (11.60)–(11.63), pp. 284–285 | `∫ P(x, dy) V(y)` on `R_M` and on `R_1` | `kinkV_eq_top`, `kinkV_eq_bot` (the two affine minorants), `integral_affine_zeroMean` |
| (11.64)–(11.66), p. 285 | `aθ(1) ≥ d − c ≥ bθ(M)`, `R ≥ max(\|θ(1)\|, \|θ(M)\|)`, `k ≥ (a + b) max(\|θ(1)\|, \|θ(M)\|)`, so `PV ≥ V` for large `\|x\|` | The choice of `d − c` in the proof of `proposition_11_5_5`; no `k`, `R` are needed without the bump; `theorem_11_5_2` then applies |
| p. 283 | The other margins (11.45)–(11.48) (stated, not proved) | `proposition_11_5_5_margins`, through `setar_null_of_top_unit` (`θ(M) = 1`, `φ(M) ≥ 0`, `V = x⁺`) and `setar_null_of_bot_unit` (`θ(1) = 1`, `φ(1) ≤ 0`, `V = x⁻`), with `theorem_11_5_2_off` |

## §11.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 285–287 | History: Kac, Feller, Chung, Çinlar, Isaac, Cogburn, Nummelin; Foster's criterion, Lamperti, Tweedie, Kalashnikov; Pakes' lemma and Foster's two-equation form; Moustafa, Mauldon, Malyšhev and Men'šikov; non-positivity (Tweedie, Doob, Fayolle et al.); applications to time series and queues (Meyn and Down, Sigman, Borovkov); the SETAR papers; the redundancy of (SETAR3); Chapters 15, 16 and 19 | Not formalised (commentary) |
