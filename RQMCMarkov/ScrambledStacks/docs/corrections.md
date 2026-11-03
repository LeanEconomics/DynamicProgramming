# Corrections and conventions

This file lists the places where a Lean statement differs from post #3 of the discourse thread
"Simulating a Markov chain: MC, QMC, RQMC" (topic 687) about codes (ii) and (iii), one Sobol
sequence per state with a random digital shift or with Owen scrambling, or from post #2 as applied
to them: a claim corrected, a claim made precise, a hypothesis made explicit, or a convention
chosen. Three claims are false as stated. Each is refuted in Lean, and a corrected statement is
proved: the spells of exactly `8` periods, the asymptotic law of the error, and the contrast
between the digital shift and Owen scrambling. Further claims are true under one reading, and the
reading is fixed and proved. The posts are paraphrased and cited by paragraph as in the
[source map](source-map.md). The last section lists what is not formalised.

## Claims corrected

| Where | Post | Lean |
| --- | --- | --- |
| 1. Spells of exactly 8, #3 ¶12 | Balancing the departures ((ii)–(iv)) makes the path too regular: in the two-state chain "every spell lasts exactly 8 periods", rather than being geometric with mean `8`. | False for the first spell in each state. For codes (ii) and (iii) on the two-state chain with stay probability `7/8` (`stackChain78`), on the good event (probability one): a departure from `0` leaves iff the first three scrambled digits of its stack point are `111`, from `1` iff they are `000` (`stay78_iff`), and these digits depend only on the departure index mod `8`, so departure `k` from `i` leaves iff `k ≡ r_i (mod 8)` for one residue `r_i < 8` (`exists_leaveResidue78`). Hence every spell in `i` after the first lasts exactly `8` periods, and the first lasts `r_i + 1` periods (`spells_stackChain78`). Under both randomisations `r_i` is uniform on `{0, …, 7}` (`owen_firstSpell78`, `shift_firstSpell78`): for a chain started in `i` the first spell has length `r + 1` with probability `1/8` for each `r < 8` (`owen_runLength_first78`, `shift_runLength_first78`), so it lasts `8` periods with probability `1/8` only, and its mean is `9/2`. The corrected claim: *every spell except the first in each state lasts exactly `8` periods; the first lasts a uniform number of periods in `{1, …, 8}`.* For rotors, (iv), `MarkovDriving` proves the same pattern (`rotor78_spells_not_geometric` there). |
| 2. The asymptotic law, #3 ¶12 | "As in the i.i.d. case, the RQMC estimators are typically not normally distributed", but in the five-state chain "normality cannot be rejected" for (ii) and (iii). | Neither randomisation has a limit law along all `T` in the chains studied, and both are normal along suitable times. (a) If every cumulative transition probability lies in `2^{-L} ℕ` (`DyadicCumProb`), then on the good event `\|N_s(T) − T π_s\| ≤ 2M + n V(h) L` for every `T` (`abs_occCount_dyadic_sub_le`, `ae_abs_occCount_dyadic_owen_le`, `ae_abs_occCount_dyadic_shift_le`). The error takes finitely many values, so for every normalisation `(N_s(T) − T π_s − b_T)/a_T` has no limit law without atoms (`not_tendstoInDistribution_of_card_le`, `not_tendstoInDistribution_occCount_owen`, `not_tendstoInDistribution_occCount_shift`), in particular no normal limit (`not_tendstoInDistribution_occCount_owen_gaussian`). For the post's 7/8 chain, `\|N_0(T) − T/2\| ≤ 28` for all `T` and the error lies in `{k/2 : \|k\| ≤ 56}` (`abs_occCount_stackChain78_le`, `occCount_stackChain78_mem`, `not_tendstoInDistribution_stackChain78_owen`, `not_tendstoInDistribution_stackChain78_shift`). (b) For the symmetric two-state chain with any stay probability `p ∈ [0,1)`, dyadic or not, the error is bounded along `T = 2^k` for every flip table (`abs_occCount_symChain_pow_two_le`), so for any randomisation no normalisation converges along all `T` to a law without atoms (`not_tendstoInDistribution_symChain`, `not_tendstoInDistribution_symChain_owen`, `not_tendstoInDistribution_symChain_shift`, `not_tendstoInDistribution_symChain_twoThirds_owen`). (c) What holds, for two states: if `p₀₁ > 0`, `p₁₁ > 0`, `T_k → ∞` and `Var(N₀(T_k) − T_k π₀) ≥ κ ⌊log₂ T_k⌋` eventually, then `(N₀(T_k) − T_k π₀)/√Var ⇒ N(0,1)` (`IsPathCoinModel.tendstoInDistribution_occErr`, `tendstoInDistribution_occErr_owen`, `tendstoInDistribution_occErr_shift`). The hypothesis holds for stay probability `2/3` along `T_k = 2 Σ_{a<k} 16^a`, where `Var ≥ k/12` (`IsPathCoinModel.eventually_variance_occErr_example_ge`, `occErr_example_tendstoInDistribution_owen`, `occErr_example_tendstoInDistribution_shift`). By (b) the same chain has bounded error along `T = 2^k`. So "normality cannot be rejected" is a property of the times at which one looks, not of the randomisation. |
| 3. Digital shift versus Owen scrambling, #2 ¶6 with #3 ¶12 | In the i.i.d. case a digital net with a digital random shift is not normal, while with Owen scrambling "a standard CLT applies"; post #3 says the stacks behave "as in the i.i.d. case". | For Markov stacks the contrast does not carry over. For one threshold per state (two-state chains), the path coins of Owen scrambling are i.i.d. fair coins with the law of the digital-shift flips (`map_owenPathCoins`); both randomisations are path-coin models (`isPathCoinModel_owen`, `isPathCoinModel_shift`), the main term of the error is the same function of the path coins (`IsPathCoinModel.mainTerm_eq`), and the CLT of correction 2 (c) holds for the digital shift exactly as for Owen scrambling (`tendstoInDistribution_occErr_shift`). Along all `T` neither is normal (correction 2). The two differ once a row has two thresholds: for the three-state chain with rows `(1/4, 1/2, 1/4)` started in `0`, "stay in `0`, then move to `1`" has probability `1/8` under Owen scrambling, the Markov value `p₀₀ p₀₁`, and `1/4` under the digital shift (`owenMeasure_stayThenMove`, `shiftMeasure_stayThenMove`, `owen_ne_shift_stayThenMove`). |

## Claims made precise

| Where | Post | Lean |
| --- | --- | --- |
| 4. Counts "almost exactly right", #3 ¶7 and ¶12 | Stacks balance the departures, so the transition counts are almost exactly right and the empirical matrix converges "faster than `O(1/√T)`". | For every realisation of either randomisation, not only on average: for every flip table, `\|N_ij(T) − p_ij N_i(T)\| ≤ 2 (⌊log₂ T⌋ + 1)` (`abs_transCount_scrambled_sub_le`, `abs_transCount_owen_sub_le`, `abs_transCount_shift_sub_le`), `\|N_s(T) − T π_s\| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` (`abs_occCount_scrambled_sub_le`, `abs_occCount_owen_sub_le`, `abs_occCount_shift_sub_le`), and the frequencies are within `O(log T / T)` (`occFreq_scrambled_isBigO`). These are the constants of the unscrambled van der Corput stacks (`abs_transCount_vdc_sub_le`, `abs_occCount_vdc_sub_le`). For dyadic cumulative probabilities, on the good event, `\|N_ij(T) − p_ij N_i(T)\| ≤ 2L` for every `T` (`abs_transCount_dyadic_sub_le`). |
| 5. The rate, #3 ¶5 and ¶7, #2 ¶7 | Stacks converge faster than MC's `O(1/√T)`. | For two states with `p₀₁ > 0` and `p₁₁ > 0`, under both randomisations and for every `T`, `E[(N₀(T) − T π₀)²] ≤ 10 (⌊log₂ T⌋ + 1)/q² + 2 anscBound(T)²` (`IsPathCoinModel.integral_sq_occErr_le`), so the occupation frequency has RMSE `O(√log T / T)` (`IsPathCoinModel.isBigO_meanSq_occFreq`). Together with the lower bound on the variance along `exampleTime`, the CLT scale is `√Var ≍ √log T` there. The MC rate `O(1/√T)` is the post's; it is not proved here. |
| 6. Requirement (i), #2 ¶1 | Each RQMC point is marginally uniform. | Every stack point is `U[0,1)` under Owen scrambling and under the digital shift (`map_scrambledStack_owen`, `map_scrambledStack_shift`). The points lie in `[0, 1]` for every flip table (`scrambledVdc_mem_Icc`), and in the open interval, and off the dyadic rationals, on the good event (`scrambledStack_mem_Ioo`, `scrambledStack_ne_dyadic`). |

## Hypotheses and conventions

* **The scramble of all digits.** A flip table flips digit `j + 1` of point `k` by
  `f j (k mod 2^j)`, also beyond the bit length of `k` (`scrambledDigit`, `scrambledVdc`), so the
  scramble is not truncated at a finite depth and has no uniform remainders. Owen's measure puts
  independent fair coins on the triples (state, depth, node); nodes `p ≥ 2^j` are unused. The
  digital shift is the special table `shiftTable e`. Everything is in base `2`.
* **The good event.** Realisation-wise statements hold for every flip table where they can
  (`StackNet`, `StackPowerOfTwo`, `CltAnscombe`, the CLT), and otherwise on `IsGoodTable`, which
  has probability one (`ae_isGoodTable_owen`, `ae_isGoodTable_shift`): the dyadic bounds and the
  spells need that no stack point is a dyadic rational.
* **Hypotheses of the CLT.** Two states, `p₀₁ > 0` and `p₁₁ > 0`: the thresholds `p₀₀` and `p₁₀`
  then lie in `[0, 1)`, where their binary digits are defined (`threshDigit`), and `q > 0`. The
  variance hypothesis is stated along the given times (`∀ᶠ k`), with `⌊log₂ T_k⌋` (`Nat.log 2`).
  The error is divided by its standard deviation without centring: it is within `anscBound` of a
  centred main term (`abs_occErr_sub_mainTerm_le`, `IsPathCoinModel.integral_mainTerm`).
* **The law equivalence.** What is proved for two states is the equality of the laws of the path
  coins (`map_owenPathCoins`) and hence of the main term (`IsPathCoinModel.mainTerm_eq`,
  `IsPathCoinModel.variance_mainTerm`). The occupation error is within `anscBound = O(log log T)`
  of the main term for every flip table, and the CLT is proved for every path-coin model. An
  identity of the full path laws of (ii) and (iii) is not stated.
* **Normalisations.** "No limit law" means: for every pair of sequences `a_T`, `b_T`, the variables
  `(error − b_T)/a_T` do not converge in distribution to any law without atoms, `N(0,1)` included.
  Lean's division by `a_T = 0` gives `0`, a point mass, which is also excluded.
* **Notation.** `occErr P x₀ f T = N₀(T) − T π₀` with `π₀ = p₁₀/(p₀₁ + p₁₀)` (`piZero`);
  `chainSumErr` is `Σ_{t<T} g(x_t) − T π(g)` and equals `(g 0 − g 1) occErr` (`chainSumErr_eq`);
  `segErr u x N L = #{N ≤ k < N + L : u k ≤ x} − L x`.

## Not formalised

* **The CLT for `n ≥ 3` states.** With several jumps in a row the jump paths share flips down to
  their common binary prefix, and the two randomisations give different path laws
  (`owen_ne_shift_stayThenMove`). The realisation-wise and dyadic bounds hold for every finite
  chain; the CLT, the variance bounds and the RMSE are for two states.
* **Variance lower bounds in general**: only for `exampleChain` along `exampleTime`.
* **Base `b > 2`**, and scrambled stacks of digital nets in `s ≥ 2` dimensions.
* **The five-state Farmer–Toda chain** of the post, and the codes' empirical results: the
  normality tests, the simulated errors and spell lengths. The numerical checks quoted in some
  module docstrings are not formalised either.
* **The full path law of (ii) and (iii) for two states** (see the conventions above), and the MC
  rate `O(1/√T)` at the root-mean-square scale for Markov chains.
