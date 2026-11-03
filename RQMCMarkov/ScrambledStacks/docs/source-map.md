# Source map

Robert Kirkby, "Simulating a Markov chain: MC, QMC, RQMC", VFI Toolkit discourse, topic 687,
posts #2 and #3 (28 October 2026),
<https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687>. The claims are
those of post #3 about its codes (ii), one Sobol sequence per state with a random digital shift,
and (iii), one Sobol sequence per state with Owen scrambling, together with post #2's description
of the two randomisations and of their asymptotic laws. The module docstrings cite Owen (1997) for
the nested uniform scramble and Niederreiter (1992, Ch. 4) for its net property; the full
references to Owen (1995, 1997a) and Loh (2003) are in the
[OwenScrambling source map](../../OwenScrambling/docs/source-map.md), and those of post #3 in the
[MarkovDriving source map](../../MarkovDriving/docs/source-map.md). The probabilistic tools are
classical: the Lindeberg CLT, Bernstein's big-block / small-block method for dependent sums,
Anscombe's random-index theorem, Slutsky's theorem and the portmanteau theorem.

The posts are cited by paragraph as in the MarkovDriving and OwenScrambling source maps: "#3 ¶12"
is the twelfth paragraph of post #3, counting the displayed transition matrix with the text around
it. Each claim is quoted by a few words at most and otherwise paraphrased. The "Reading" is the
precise statement that the Lean results prove. Lean names are relative to
`RQMCMarkov.ScrambledStacks`; names from other projects are marked with the project.

Notation. States are `Fin n`, `0`-indexed, and time starts at `0`, as in `MarkovDriving`. A flip
table is `f : Fin n → ℕ → ℕ → Bool` (state, depth, node); stack `i` is `scrambledStack f i`, with
point `k` equal to `scrambledVdc (f i) k`. Owen scrambling is `owenTable ω` under `owenMeasure n`,
the digital shift is `shiftFlips ω` under `shiftMeasure n`. The driven path is
`stackPath P x₀ (scrambledStack f)`; `N_i(T) = occCount`, `N_ij(T) = transCount`. `h` solves
Poisson's equation `h − Ph = 1_{s} − π_s` with `|h| ≤ M`, and `V(h) = stateVariation h`. For two
states, `q = p₀₁ + p₁₀`, `π₀ = piZero P`, the occupation error `N₀(T) − T π₀` is `occErr`, and the
error `Σ_{t<T} g(x_t) − T π(g)` is `chainSumErr`. The good event `IsGoodTable f` has probability
one. Every place where a Lean statement departs from the posts is listed in
[corrections](corrections.md).

## Post #3: codes (ii) and (iii)

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| #3 ¶7 | One QMC sequence per state, the `k`-th visit to state `i` using point `k` of stack `i` | The stack rule with one scrambled van der Corput stack per state | `stackPath`, `stackDrive_succ`, `departureIndex` (`Driving`, copied); `scrambledStack` (`StackDefs`) |
| #3 ¶7 | "The departures from each state are balanced", so the empirical transition matrix converges "faster than `O(1/√T)`" | For every flip table, Owen and shift alike: `\|N_ij(T) − p_ij N_i(T)\| ≤ 2 (⌊log₂ T⌋ + 1)` and `\|D_i(g, T)\| ≤ V(g) (⌊log₂ T⌋ + 1)` | `abs_transCount_scrambled_sub_le`, `abs_departureDiscrepancy_scrambled_le`, `abs_transCount_owen_sub_le`, `abs_transCount_shift_sub_le` (`StackNet`) |
| #3 ¶9 | (Stacks have occupation error) "`O(log T / T)`" | For every flip table, `\|N_s(T) − T π_s\| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`, so the frequencies are within `O(log T / T)` | `abs_occCount_scrambled_sub_le`, `occFreq_scrambled_isBigO`, `abs_occCount_owen_sub_le`, `abs_occCount_shift_sub_le` (`StackNet`); unscrambled stacks: `abs_occCount_vdc_sub_le`, `occFreq_vdc_isBigO` (`StackBound`, copied) |
| #3 ¶11 | Codes (ii): "one Sobol sequence per state + random digital shift" | Base-2 van der Corput stacks; digit `j + 1` of every point flipped by one fair coin per state and depth | `shiftTable`, `scrambledDigit_shiftTable`, `shiftMeasure`, `shiftFlips`, `scrambledDigit_shiftFlips` (`StackDefs`) |
| #3 ¶11 | Codes (iii): "one Sobol sequence per state + Owen scrambling" | Owen's nested scramble of all digits: digit `j + 1` of point `k` flipped by the fair coin at the node `k mod 2^j`, no truncation; stacks of different states independent | `scrambledDigit`, `scrambledVdc`, `scrambledVdc_eq_tsum`, `fairCoin`, `owenMeasure`, `owenTable`, `scrambledDigit_owenTable`, `owen_coord_injective` (`StackDefs`) |
| #3 ¶12 | Balancing the departures ((ii)–(iv)) gets the transition counts "almost exactly right" | (ii), (iii): the bound of #3 ¶7 for every realisation; for dyadic cumulative probabilities, on the good event, `\|N_ij(T) − p_ij N_i(T)\| ≤ 2L` for every `T`. (iv), rotors: `MarkovDriving` | `abs_transCount_scrambled_sub_le` (`StackNet`); `DyadicCumProb`, `abs_transCount_dyadic_sub_le` (`StackDyadic`) |
| #3 ¶12 | In the two-state chain "every spell lasts exactly 8 periods", not geometric with mean `8` | Codes (ii) and (iii), stay probability `7/8`, good event: every spell after the first in each state lasts exactly `8`; the first spell in state `i` lasts `r_i + 1` periods, `r_i` uniform on `{0, …, 7}` under both randomisations. Rotors: `MarkovDriving` | `stackChain78` (`StackDyadic`); `stay78_iff`, `exists_leaveResidue78`, `spells_stackChain78`, `owen_firstSpell78`, `shift_firstSpell78`, `owen_runLength_first78`, `shift_runLength_first78` (`StackSpells`); `rotor78_spells_not_geometric` (`MarkovDriving`); see corrections |
| #3 ¶12 | "As in the i.i.d. case, the RQMC estimators are typically not normally distributed" | For dyadic chains the occupation error is bounded and takes finitely many values, so no normalisation converges to a law without atoms; for the 7/8 chain `\|N_0(T) − T/2\| ≤ 28`. For the symmetric two-state chain with any `p ∈ [0,1)` the error is bounded along `T = 2^k`, so there is no limit law along all `T` | `abs_occCount_dyadic_sub_le`, `not_tendstoInDistribution_occCount_owen`, `not_tendstoInDistribution_occCount_shift`, `abs_occCount_stackChain78_le`, `occCount_stackChain78_mem`, `not_tendstoInDistribution_stackChain78_owen`, `not_tendstoInDistribution_stackChain78_shift` (`StackDyadic`); `abs_occCount_symChain_pow_two_le`, `not_tendstoInDistribution_symChain`, `not_tendstoInDistribution_symChain_twoThirds_owen` (`StackPowerOfTwo`); see corrections |
| #3 ¶12 | "In the five-state chain normality cannot be rejected" for (ii) and (iii) | For `p₀₁ > 0`, `p₁₁ > 0` and times `T_k → ∞` with `Var(N₀(T_k) − T_k π₀) ≥ κ ⌊log₂ T_k⌋`, the error divided by its standard deviation is asymptotically `N(0,1)`, under both randomisations, also for `Σ g(x_t) − T π(g)` with `g 0 ≠ g 1`. Non-vacuous: for stay probability `2/3` and `T_k = 2 Σ_{a<k} 16^a`, `Var ≥ k/12`. For any number `n` of states, with Poisson data for every target and `Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k`, the same CLT, by separate proofs for the digital shift and Owen's scramble, also for transition counts; non-vacuous for the uniform chains on `n` states, `n` not a power of two, in particular three and five states. The post's Farmer–Toda probabilities are not checked | `IsPathCoinModel.tendstoInDistribution_occErr`, `tendstoInDistribution_occErr_owen`, `tendstoInDistribution_occErr_shift`, `IsPathCoinModel.tendstoInDistribution_chainSumErr`, `occErr_example_tendstoInDistribution_owen`, `occErr_example_tendstoInDistribution_shift` (`CltStacks`); `exampleChain`, `exampleTime`, `IsPathCoinModel.eventually_variance_occErr_example_ge` (`CltVariance`); `occCount_sub_eq_boundary_add_cuts`, `abs_occErrN_sub_mainTermN_le`, `mainTermN_eq_levelSumN` (`CltNDecomp`); `tendstoInDistribution_occErrN_shift` (`CltNShift`); `measurePreserving_owenRelabel`, `pathCoin_owenTable_eq_relabel` (`CltNOwenTree`); `tendstoInDistribution_occErrN_owen` (`CltNOwen`); `eventually_variance_occErrN_uniform_shift_ge`, `eventually_variance_occErrN_uniform_owen_ge`, `occErrN_example_tendstoInDistribution_owen`, `occErrN_five_tendstoInDistribution_owen` (`CltNExample`); `tendstoInDistribution_transErrN_owen` (`CltNTrans`); see corrections |
| #3 ¶5, ¶7 | MC converges at `O(1/√T)`; stacks faster | For two states and both randomisations, `E[(N₀(T) − T π₀)²] = O(log T)` for every `T`, so the occupation frequency has RMSE `O(√log T / T)`. The MC rate is not proved here | `IsPathCoinModel.integral_sq_occErr_le`, `IsPathCoinModel.isBigO_meanSq_occFreq` (`CltStacks`) |
| #3 ¶11–¶12 | The codes report the simulated errors and normality tests, for a two-state and a five-state Farmer–Toda chain | Empirical | Not formalised |

## Post #2: the two randomisations

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| #2 ¶1 | (i) each RQMC point is marginally uniform | Every stack point is `U[0,1)` under Owen scrambling and under the digital shift; its first `m` scrambled digits are uniform | `map_binaryVal_xor_eq_uniformIco`, `map_scrambledStack_owen`, `map_scrambledStack_shift`, `owen_digitPrefix_eq`, `shift_digitPrefix_eq` (`StackDefs`) |
| #2 ¶1 | (ii) the points keep their low-discrepancy structure | For every flip table, each aligned block of `2^m` points has one point in each dyadic cell of length `2^{-m}` (a `(0,1)`-sequence in base `2`); block errors `≤ 1`, segment errors `≤ 2⌊log₂ L⌋ + 3`, initial segments `≤ ⌊log₂ N⌋ + 1` | `image_digitPrefix_scrambledDigit_block`, `card_filter_digitPrefix_block`, `abs_segErr_scrambledVdc_block_le`, `abs_segErr_scrambledVdc_log_le`, `abs_segErr_scrambledVdc_zero_le` (`StackNet`) |
| #2 ¶4 | The digital shift is a "random diagonal shift in base 2"; Owen scrambling is a "nested uniform scramble" | The shift is the flip table constant on each level; Owen's table has an independent flip at each node | `shiftTable`, `scrambledDigit` (`StackDefs`) |
| #2 ¶4 | Owen scrambling is "more powerful" than the digital shift | For one threshold per state (two-state chains) the path coins of Owen scrambling are i.i.d. fair, with the law of the shift flips, so the main term of the error has the same law under both. With two thresholds in a row (three states) a cylinder probability differs: `1/8` under Owen, the MC value `p₀₀ p₀₁`, against `1/4` under the shift | `pathCoin`, `owenMeasure_pathCoins_cylinder`, `map_owenPathCoins`, `pathCoin_shiftTable` (`CltPathBits`); `IsPathCoinModel`, `isPathCoinModel_owen`, `isPathCoinModel_shift`, `IsPathCoinModel.mainTerm_eq` (`CltVariance`); `threeChain`, `StayThenMove`, `owenMeasure_stayThenMove`, `shiftMeasure_stayThenMove`, `owen_ne_shift_stayThenMove` (`CltThreeState`) |
| #2 ¶6 | A digital net with a digital random shift is not normal; with Owen scrambling "a standard CLT applies" | For the Markov stacks of two-state chains the two randomisations satisfy the same CLT, at the scale `√Var ≍ √log T` and along times with growing variance; along all `T` neither has a limit law. The i.i.d. results are in `OwenScrambling` and `PointSets` | As in #3 ¶12; i.i.d.: `tendstoInDistribution_owenNet` (`OwenScrambling`), `hasLaw_scaled_error_digitalShift_id` (`PointSets`); see corrections |
| #2 ¶7 | RQMC has faster rates than MC | For the stacks: `O(log T / T)` for every realisation, RMSE `O(√log T / T)` for two states | As in #3 ¶9 and #3 ¶5, ¶7 |

## The literature

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| Owen 1995, 1997 | The nested uniform scramble keeps the net property of a `(t,m,s)`-net | For the van der Corput sequence: every flip table maps aligned blocks of `2^m` points onto the `2^m` dyadic cells, so the scrambled sequence is a `(0,1)`-sequence in base `2` | `mod_eq_of_digitPrefix_scrambledDigit_eq`, `digitPrefix_scrambledDigit_mod`, `injOn_digitPrefix_scrambledDigit`, `image_digitPrefix_scrambledDigit_block` (`StackNet`) |
| Owen 1995 | Each scrambled point is uniform | Under both randomisations, for every stack point | `map_scrambledStack_owen`, `map_scrambledStack_shift` (`StackDefs`) |
| Owen 1997a | The variance of scrambled net quadrature through the pair law | Not used: the variance of the stack error is computed from the path coins | `variance_coinTerm`, `abs_covariance_coinTerm_le`, `variance_coinSum_le`, `variance_coinSum_pattern_ge` (`CltVariance`) |
| Loh 2003 | Scrambled-net quadrature is asymptotically normal | The CLT for Markov stacks is a different theorem: the error at a random number of stack points, a sum over binary levels of locally dependent bounded terms, proved without Stein's method | `tendstoInDistribution_of_truncations` (`CltMDependent`); `IsPathCoinModel.tendstoInDistribution_occErr` (`CltStacks`) |
| Lindeberg | CLT for triangular arrays | Bounded form, copied; restated under sequential independence | `tendstoInDistribution_sum_of_bounded` (`Owen1DLindeberg`, copied); `tendstoInDistribution_sum_range_of_bounded` (`CltMDependent`) |
| Bernstein | Big-block / small-block CLT for dependent sums | Independent bounded blocks plus a remainder of negligible variance; truncation at depth `L = 2(⌊log₂ K⌋ + 1)`, blocks of length `L³` | `IsLocal`, `IsLocal.indepFun`, `charFun_map_sum_range_eq_prod`, `tendstoInDistribution_of_blocks`, `tendstoInDistribution_of_truncations` (`CltMDependent`) |
| Anscombe | A CLT survives a random index | Deterministic form: for every flip table the random indices `N_i(T)` may be replaced by `⌊T π_i⌋` at a cost `O(log log T)` | `abs_segErr_sub_segErr_le`, `abs_occErr_sub_mainTerm_le` (`CltAnscombe`); `anscBound_le_log`, `tendsto_anscBound_sq_div` (`CltStacks`) |
| Slutsky | A perturbation of order `o(σ)` does not change the limit | For a bounded perturbation `b_k` with `b_k² = o(Var)` | `tendstoInDistribution_of_abs_sub_le` (`CltStacks`) |
| (Portmanteau) | A limit law without atoms charges intervals continuously | Variables with at most `K` values almost surely have no limit without atoms | `continuous_cdf_of_noAtoms`, `exists_cdf_eq`, `not_tendstoInDistribution_of_card_le`, `not_tendstoInDistribution_of_abs_sub_le` (`StackDyadic`) |

## Supporting results

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| (Background) | The good event | No stack point has eventually constant digits, so none is a dyadic rational; probability one under both randomisations | `NotEventuallyConst`, `binaryVal_ne_dyadic`, `IsGoodTable`, `scrambledStack_ne_dyadic`, `ae_isGoodTable_owen`, `ae_isGoodTable_shift` (`StackDefs`) |
| (Background) | Segment lemma | Model-free: a sequence with aligned-block increments bounded by `B` varies by at most `B (2⌊log₂ L⌋ + 3)` over a segment of length `L` | `segErr`, `abs_segErr_prefix_le`, `abs_segErr_le_of_block` (`StackNet`); `AlignedBlockBound`, `abs_sub_alignedPrefix_le`, `abs_sub_le_log`, `abs_sub_zero_le_log` (`CltBlocks`) |
| (Background) | Per-block jump formula | One point per dyadic cell gives `#{x ≤ c} = ⌊2^m c⌋ + 1{x* ≤ c}` over an aligned block | `card_le_add_frac_eq`, `alignedBlockBound_of_cells` (`CltBlocks`); `card_block_le_eq` (`CltPathBits`) |
| (Background) | Discrete Koksma inequality for threshold counts | Error `≤ V(g) D` when every threshold count has error `≤ D` | `abs_sum_step_sub_le_of_count`, `abs_sum_step_scrambledVdc_segment_le` (`StackNet`) |
| (Background) | Two-state identity | `\|q (N₀ − T π₀) − D₀(N₀) − D₁(N₁)\| ≤ 1` for any stacks in `[0,1]` | `step_two_eq_zero_iff`, `abs_two_state_identity`, `abs_occErr_le` (`CltAnscombe`) |
| (Background) | Level decomposition | The local discrepancy at `c` is a sum over the binary digits of `N` of level terms, each a function of the path coins from that level on; truncated tie cascades | `threshDigit`, `binaryVal_le_iff_lexLeFrom`, `tie_iff_mod_eq_pathPrefix`, `segErr_scrambledVdc_eq_sum_level`, `levelVal_eq_trunc_of_not_tie`, `levelValTrunc_congr`, `levelInd_iff_binaryVal_le` (`CltPathBits`); `measureReal_levelTie`, `integral_levelVal` (`CltVariance`) |
| (Background) | Self-consistent bound | `c d ≤ A + B ⌊log₂ d⌋` bounds `d` | `exists_le_of_mul_le_log` (`StackPowerOfTwo`) |
