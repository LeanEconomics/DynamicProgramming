# Markov chains driven by scrambled Sobol stacks, in Lean

This is the `RQMCMarkov/ScrambledStacks` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It
formalises what post #3 of Robert Kirkby, "Simulating a Markov chain: MC, QMC, RQMC", VFI Toolkit
discourse, topic 687 (October 2026),
<https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687>, reports for two of
its codes: (ii) one Sobol sequence per state with a random digital shift, and (iii) one Sobol
sequence per state with Owen scrambling. The post says these get the transition counts "almost
exactly right", that in the two-state chain "every spell lasts exactly 8 periods", and that
normality of the estimators "cannot be rejected" in the five-state chain. It also uses post #2's
contrast between the two randomisations: Owen scrambling gives a CLT, the digital shift does not.
[RQMCMarkov/MarkovDriving](../MarkovDriving/README.md) proved the stack bounds for unscrambled van
der Corput stacks and left the randomisations open; [RQMCMarkov/OwenScrambling](../OwenScrambling/README.md)
proved the CLT for scrambled nets of i.i.d. type. Run the commands below from this directory.
[Return to the library index](../../README.md).

In one dimension the Sobol sequence is the base-2 van der Corput sequence: point `k` has binary
digit `j + 1` equal to bit `j` of `k`. A *flip table* `f : ℕ → ℕ → Bool` scrambles it: digit
`j + 1` of point `k` is flipped by `f j (k mod 2^j)`, the flip at the node of the binary tree given
by the original digits `1, …, j` (`scrambledDigit`, `scrambledVdc`). Every digit is scrambled,
also those beyond the bit length of `k`, so this is Owen's nested uniform scramble of all digits,
with no truncation. A *digital shift* is the table with one flip per digit, `f j p = e j`
(`shiftTable`). Under `owenMeasure n` the flips are i.i.d. fair coins indexed by state, depth and
node (`owenTable`); under `shiftMeasure n` they are indexed by state and depth (`shiftFlips`). Each
state `i` has its own stack `scrambledStack f i`, and the chain is driven by the stack rule of
post #3: the `k`-th departure from `i` uses point `k` of stack `i` through the inverse-CDF update
`step P i u` (`stackPath`). Everything is in base `2`.

The library contains **507 theorems** (609 audited declarations) in 21 modules. Twelve modules
(325 theorems) are new. Nine are copied, with the namespace and imports renamed and otherwise
unchanged, and each says so in its docstring: `MonteCarlo`, `Unbiased`, `Driving`,
`OccupationDiscrepancy`, `Discrepancy`, `Koksma`, `VanDerCorput` and `StackBound` from
[RQMCMarkov/MarkovDriving](../MarkovDriving/README.md) (178 theorems; `MonteCarlo`, `Unbiased`,
`Discrepancy`, `Koksma` and `VanDerCorput` are originally from
[RQMCMarkov/PointSets](../PointSets/README.md)), and `Owen1DLindeberg` from
[RQMCMarkov/OwenScrambling](../OwenScrambling/README.md) (4 theorems).

## The main theorem: bounded for dyadic chains, normal at the scale `√log T` along some times

Write `N_s(T)` for the number of periods `t < T` spent in state `s`, `π` for the stationary
distribution and `N_s(T) − T π_s` for the occupation error. Its behaviour depends on the chain and
on the times `T`, not on the randomisation:

| Chain and times | Occupation error `N_s(T) − T π_s` | Limit law of the normalised error | Lean |
| --- | --- | --- | --- |
| Any finite chain, any `T` | `\|·\| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` for every flip table | — | `abs_occCount_scrambled_sub_le`, `abs_occCount_owen_sub_le`, `abs_occCount_shift_sub_le` |
| Dyadic cumulative probabilities `cs_{ij} ∈ 2^{-L} ℕ`, any `T` | `\|·\| ≤ 2M + n V(h) L` almost surely, uniformly in `T`, so it takes finitely many values | None: no normalisation `(error − b_T)/a_T` converges to any law without atoms | `ae_abs_occCount_dyadic_owen_le`, `not_tendstoInDistribution_occCount_owen`, `not_tendstoInDistribution_occCount_shift` |
| Symmetric two-state chain, any stay probability `p ∈ [0,1)`, along `T = 2^k` | Bounded, for every flip table | None along all `T`, for any randomisation | `abs_occCount_symChain_pow_two_le`, `not_tendstoInDistribution_symChain` |
| Two states with `p₀₁ > 0`, `p₁₁ > 0`, along `T_k → ∞` with `Var ≥ κ ⌊log₂ T_k⌋` | `E[error²] = O(log T)`, so `√Var ≍ √log T` | `N(0,1)` after dividing by `√Var`, for Owen scrambling and for the digital shift | `IsPathCoinModel.tendstoInDistribution_occErr`, `tendstoInDistribution_occErr_owen`, `tendstoInDistribution_occErr_shift`, `IsPathCoinModel.integral_sq_occErr_le` |
| `p₀₀ = p₁₁ = 2/3`, `T_k = 2 Σ_{a<k} 16^a` | `Var ≥ k/12` eventually, hence `Var ≥ ⌊log₂ T_k⌋/60` | `N(0,1)`, for both randomisations | `IsPathCoinModel.eventually_variance_occErr_example_ge`, `IsPathCoinModel.eventually_variance_example`, `occErr_example_tendstoInDistribution_owen`, `occErr_example_tendstoInDistribution_shift` |

Here `h` solves Poisson's equation `h − Ph = 1_{s} − π_s`, `|h| ≤ M`, and `V(h)` is its variation
over the states (`stateVariation`). The first row is the QMC rate of `MarkovDriving`, now for
every realisation of either randomisation. The post's two-state chain, with stay probability
`7/8` in both states, is dyadic with `L = 3`: on an event of probability one,
`|N_0(T) − T/2| ≤ 28` for every `T` (`abs_occCount_stackChain78_le`). The chain with stay
probability `2/3` is `symChain (2/3)` in row 3 and `exampleChain` in row 5: along `T = 2^k` its error is bounded, along
`T_k = 2 Σ_{a<k} 16^a` it is asymptotically normal. So the law of the error does not converge
along all `T`, and whether normality "cannot be rejected" depends on the times at which one looks.

## What is proved

* **The model** (`StackDefs`). Binary expansions `binaryVal`, their first `m` digits
  `digitPrefix`, and the closed dyadic cell of each point (`binaryVal_eq_digitPrefix_add`,
  `digitPrefix_div_le_binaryVal`, `binaryVal_le_digitPrefix_add_one_div`). Every scrambled point
  lies in `[0, 1]` for every flip table (`scrambledVdc_mem_Icc`). The *good event*
  `IsGoodTable f` says that no stack point has eventually constant digits, so none is a dyadic
  rational (`scrambledStack_ne_dyadic`); it has probability one under both randomisations
  (`ae_isGoodTable_owen`, `ae_isGoodTable_shift`). Every stack point is uniform on `[0,1)` under
  both (`map_scrambledStack_owen`, `map_scrambledStack_shift`), which is requirement (i) of
  posts #1–#2. The path coordinates and the counts are random variables
  (`measurable_stackPath_of`, `measurable_occCount_of`, `measurable_transCount_of`).
* **The QMC rate for every realisation** (`StackNet`). For every flip table the first `m`
  scrambled digits of point `k` depend only on `k mod 2^m` and determine it, so every aligned
  block of `2^m` points puts exactly one point in each dyadic cell of length `2^{-m}`
  (`image_digitPrefix_scrambledDigit_block`): the scrambled sequence is a `(0,1)`-sequence in base
  `2`. The counting error of an aligned block is at most `1` (`abs_segErr_scrambledVdc_block_le`).
  A segment lemma bounds every segment of length `L` by `2⌊log₂ L⌋ + 3`
  (`abs_segErr_le_of_block`, `abs_segErr_scrambledVdc_log_le`) and every initial segment of
  length `N` by `⌊log₂ N⌋ + 1` (`abs_segErr_scrambledVdc_zero_le`). A discrete Koksma inequality
  passes this to the chain: `|N_ij(T) − p_ij N_i(T)| ≤ 2 (⌊log₂ T⌋ + 1)`
  (`abs_transCount_scrambled_sub_le`), `|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)` for the departure
  discrepancy (`abs_departureDiscrepancy_scrambled_le`), the occupation bound of the table above
  (`abs_occCount_scrambled_sub_le`), and occupation frequencies within `O(log T / T)`
  (`occFreq_scrambled_isBigO`). The constants are those of `StackBound` for unscrambled van der
  Corput stacks (`abs_transCount_vdc_sub_le`, `abs_occCount_vdc_sub_le`): no realisation of
  either randomisation is worse than plain QMC. The Owen and shift versions are
  `abs_transCount_owen_sub_le`, `abs_transCount_shift_sub_le`, `abs_occCount_owen_sub_le` and
  `abs_occCount_shift_sub_le`.
* **Dyadic transition probabilities** (`StackDyadic`). If every cumulative sum `cs_{ij}` lies in
  `2^{-L} ℕ` (`DyadicCumProb`, `dyadicCumProb_of_entries`), then on the good event an aligned
  block of length `2^m ≥ 2^L` has counting error exactly `0` at every threshold
  (`segErr_scrambledVdc_block_dyadic`), and every initial segment has error at most `L`
  (`abs_segErr_scrambledVdc_dyadic_le`). Hence, for every `T`,
  `|N_ij(T) − p_ij N_i(T)| ≤ 2L` (`abs_transCount_dyadic_sub_le`),
  `|D_i(g, T)| ≤ V(g) L` (`abs_departureDiscrepancy_dyadic_le`) and
  `|N_s(T) − T π_s| ≤ 2M + n V(h) L` (`abs_occCount_dyadic_sub_le`), almost surely under both
  randomisations (`ae_abs_occCount_dyadic_owen_le`, `ae_abs_occCount_dyadic_shift_le`). Random
  variables that take at most `K` values almost surely do not converge in distribution to any
  law without atoms (`not_tendstoInDistribution_of_card_le`), so no normalisation of the
  occupation error has such a limit (`not_tendstoInDistribution_occCount_owen`,
  `not_tendstoInDistribution_occCount_shift`), in particular not `N(0,1)`
  (`not_tendstoInDistribution_occCount_owen_gaussian`). For the post's chain `stackChain78`,
  `h = (2, −2)` (`poisson78`, `poisson78_spec`), `|N_0(T) − T/2| ≤ 28`
  (`abs_occCount_stackChain78_le`), the error lies in the fixed set `{k/2 : |k| ≤ 56}`
  (`occCount_stackChain78_mem`), and there is no limit law without atoms
  (`not_tendstoInDistribution_stackChain78_owen`, `not_tendstoInDistribution_stackChain78_shift`).
* **Spells of the 7/8 chain** (`StackSpells`). On the good event a departure from state `0` leaves
  iff the first three scrambled digits of its stack point are `111`, and from state `1` iff they
  are `000` (`stay78_iff`). These digits depend only on `k mod 8`, so there is one residue
  `r_i < 8` with departure `k` from `i` leaving iff `k ≡ r_i (mod 8)`
  (`exists_leaveResidue78`). A stay uses consecutive entries of one stack
  (`stackPath_stay_iff`), and a later spell starts right after a leaving departure
  (`not_stay_prev_of_spellStart`). Hence, for every good flip table, start and state `i`
  (`spells_stackChain78`): the first spell in `i` lasts exactly `r_i + 1` periods and every later
  spell in `i` lasts exactly `8` periods (for spells that end before the horizon `T`). Under both
  randomisations `r_i` is uniform on `{0, …, 7}` (`owen_firstSpell78`, `shift_firstSpell78`), so
  the first spell is uniform on `{1, …, 8}`; for a chain started in `i`,
  `P(first spell = r + 1) = 1/8` (`owen_runLength_first78`, `shift_runLength_first78`).
* **Powers of two** (`StackPowerOfTwo`). For the symmetric two-state chain `symChain p` with any
  `p ∈ [0, 1)`, dyadic or not, and every flip table, `|N_0(2^k) − 2^k/2| ≤ C` with `C`
  independent of the table, the start and `k` (`abs_occCount_symChain_pow_two_le`). The proof is
  a self-consistent bound: the two transition counts are threshold counts
  (`transCount_zero_one_eq`, `transCount_one_zero_eq`) that differ by at most one, each half of
  `2^k` is one aligned block, and the remainder is a segment of length `d = |N_0 − 2^k/2|`, so
  `2(1 − p) d ≤ 9 + 4⌊log₂ d⌋`, which bounds `d` (`exists_le_of_mul_le_log`). A limit along all
  `T` would be one along `T = 2^k` (`tendstoInDistribution_comp_pow_two`), so for any random flip
  table, any normalisation and any law without atoms there is no limit along all `T`
  (`not_tendstoInDistribution_symChain`, `not_tendstoInDistribution_symChain_owen`,
  `not_tendstoInDistribution_symChain_shift`); for `p = 2/3`, no `N(0,1)` limit
  (`not_tendstoInDistribution_symChain_twoThirds_owen`).
* **The two-state identity and a deterministic Anscombe theorem** (`CltAnscombe`, `CltBlocks`).
  In a two-state chain the `0 → 1` and `1 → 0` transitions alternate, so for every pair of stacks
  in `[0, 1]`, `|q (N₀(T) − T π₀) − D₀(N₀(T)) − D₁(N₁(T))| ≤ 1`, with `q = p₀₁ + p₁₀` and `D_i`
  the local discrepancy of stack `i` at its threshold (`abs_two_state_identity`). The random
  indices `N_i(T)` can be replaced by `⌊T π_i⌋`: the occupation error `occErr` differs from the
  main term `mainTerm = (D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋))/q` by at most
  `anscBound = (7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q = O(log log T)`, for every flip table
  (`abs_occErr_sub_mainTerm_le`, `anscBound_le_log`).
* **Path coins** (`CltPathBits`). For a threshold `c ∈ [0,1)`, the only flips that matter for
  `#{k < N : x_k ≤ c}` are the *path coins* `e_j = f j α_j` at the nodes on the path of `c`
  (`pathPrefix`, `pathCoin`, `tie_iff_mod_eq_pathPrefix`). In an aligned block of `2^m` points the
  count is `⌊2^m c⌋` plus one indicator (`card_block_le_eq`), and the local discrepancy is a sum
  over the binary digits of `N` of level terms, each a function of the path coins from that level
  on (`segErr_scrambledVdc_eq_sum_level`, `levelTerm`). Truncating the tie cascades at depth `L`
  changes a level term only on the tie event (`levelVal_eq_trunc_of_not_tie`), which has
  probability `2^{-L}` under fair coins (`measureReal_levelTie`), and makes it a function of the
  coins at levels `[m, m + L)` (`levelValTrunc_congr`). Under Owen's measure the path coins of all states, one threshold per
  state, are i.i.d. fair coins, with the law `shiftMeasure n` of the digital-shift flips
  (`owenMeasure_pathCoins_cylinder`, `map_owenPathCoins`); for the digital shift the path coins
  are the flips themselves (`pathCoin_shiftTable`).
* **Three states** (`CltThreeState`). With two thresholds in a row the equivalence fails. For the
  chain `threeChain` with every row `(1/4, 1/2, 1/4)`, started in `0`, the event "stay in `0`, then
  move to `1`" (`StayThenMove`) has probability `1/8 = p₀₀ p₀₁` under Owen scrambling
  (`owenMeasure_stayThenMove`) and `1/4` under the digital shift (`shiftMeasure_stayThenMove`), so
  the path laws of codes (ii) and (iii) differ (`owen_ne_shift_stayThenMove`).
* **The variance** (`CltVariance`). On the fair-coin space the level terms are centred Bernoulli
  variables (`integral_levelVal`, `variance_coinTerm`); terms of different states are uncorrelated
  (`covariance_coinTerm_eq_zero`), and terms of one state at levels `m < m'` have covariance at
  most `2^{-(m'−m)}` (`abs_covariance_coinTerm_le`). Hence `Var ≤ 5K` for `K` levels
  (`variance_coinSum_le`), and `Var ≥ 8k/45` when both indices are `Σ_{i<k} 16^i` and the
  fractional parts `{2^m c}` stay in `[1/3, 2/3]` (`variance_coinSum_pattern_ge`). A
  randomisation whose path coins are i.i.d. fair is an `IsPathCoinModel`; Owen scrambling and the
  digital shift both are (`isPathCoinModel_owen`, `isPathCoinModel_shift`). For such a model the
  main term is the same function of the path coins, centred, with the same variance
  (`IsPathCoinModel.mainTerm_eq`, `IsPathCoinModel.integral_mainTerm`,
  `IsPathCoinModel.variance_mainTerm`), and the standard deviations of the error and of the main
  term differ by at most `anscBound` (`IsPathCoinModel.abs_sqrt_variance_occErr_sub_le`). On
  `exampleChain` (stay probability `2/3`) at `exampleTime k = 2 Σ_{i<k} 16^i`, the main term has
  variance `≥ 2k/5` (`IsPathCoinModel.variance_mainTerm_example_ge`) and the occupation error
  `≥ k/12` eventually (`IsPathCoinModel.eventually_variance_occErr_example_ge`).
* **The CLT** (`CltStacks`). For a two-state chain with `p₀₁ > 0` and `p₁₁ > 0`, any path-coin
  model, any start and any times `T_k → ∞` with `Var(N₀(T_k) − T_k π₀) ≥ κ ⌊log₂ T_k⌋`
  eventually, `(N₀(T_k) − T_k π₀)/√Var ⇒ N(0,1)` (`IsPathCoinModel.tendstoInDistribution_occErr`;
  code (iii): `tendstoInDistribution_occErr_owen`; code (ii): `tendstoInDistribution_occErr_shift`).
  The proof applies the dependent CLT below to the coin sums (`tendstoInDistribution_coinSum`),
  transfers it through the path coins (`TendstoInDistribution.comp_measurePreserving`), and
  removes the `O(log log T)` Anscombe term by Slutsky's theorem
  (`tendstoInDistribution_of_abs_sub_le`, `tendsto_anscBound_sq_div`). The same holds for the
  error `Σ_{t<T} g(x_t) − T π(g)` of every `g` with `g 0 ≠ g 1` (`chainSumErr_eq`,
  `IsPathCoinModel.tendstoInDistribution_chainSumErr`). The hypothesis is met on the concrete
  sequence (`IsPathCoinModel.eventually_variance_example`), so the CLT holds there
  (`occErr_example_tendstoInDistribution`, `occErr_example_tendstoInDistribution_owen`,
  `occErr_example_tendstoInDistribution_shift`). The mean-square error is
  `E[(N₀(T) − T π₀)²] ≤ 10 (⌊log₂ T⌋ + 1)/q² + 2 anscBound(T)²` for every `T`
  (`IsPathCoinModel.integral_sq_occErr_le`), so the occupation frequency has RMSE
  `O(√log T / T)` (`IsPathCoinModel.isBigO_meanSq_occFreq`), against the `O(1/√T)` of MC.
* **Model-free tools** (`CltMDependent`, `CltBlocks`, `Owen1DLindeberg`). Functions of disjoint
  sets of coordinates of a product measure are independent (`IsLocal`, `IsLocal.indepFun`). The
  bounded Lindeberg CLT of `OwenScrambling` (`tendstoInDistribution_sum_of_bounded`) is restated
  for sequentially independent terms (`tendstoInDistribution_sum_range_of_bounded`), and gives a
  CLT for sums of independent bounded blocks plus a remainder of negligible variance
  (`tendstoInDistribution_of_blocks`). The dependent CLT is
  `tendstoInDistribution_of_truncations`: if bounded terms `Y n m`, `m < K n`, are approximated in
  `L²` to within `C 2^{-L}` by terms that depend only on coordinates of levels `[m, m + L)`, and
  `Var(Σ_m Y n m) ≥ κ K n` with `K n → ∞`, then the normalised sums are asymptotically `N(0,1)`.
  The proof is Bernstein's big-block / small-block method with truncation depth
  `L = 2(⌊log₂ K⌋ + 1)` and blocks of length `L³`. `CltBlocks` proves the segment lemma for any
  sequence whose increments over aligned dyadic blocks are bounded (`AlignedBlockBound`,
  `abs_sub_le_log`, `abs_sub_zero_le_log`) and the per-block jump formula for sequences with one
  point per dyadic cell (`card_le_add_frac_eq`, `alignedBlockBound_of_cells`).

## Corrections

Three claims are false as stated. Each is refuted in Lean, and a corrected statement is proved.

* **Not every spell lasts 8 periods.** For codes (ii) and (iii) on the 7/8 chain, every spell
  after the first in each state lasts exactly `8` periods, but the first spell in state `i` lasts
  `r_i + 1` periods with `r_i` uniform on `{0, …, 7}` (`spells_stackChain78`,
  `owen_runLength_first78`, `shift_runLength_first78`). It lasts `8` periods with probability
  `1/8` only.
* **No CLT along all `T`.** For dyadic chains, the post's two-state chain included, the
  occupation error is bounded and takes finitely many values, so no normalisation has a limit
  without atoms, for either randomisation (`not_tendstoInDistribution_occCount_owen`,
  `not_tendstoInDistribution_occCount_shift`). For the symmetric two-state chain with any
  `p ∈ [0, 1)` the error is bounded along `T = 2^k`, so there is no limit law along all `T`
  (`not_tendstoInDistribution_symChain`). Normality holds at the scale `√log T` along times with
  `Var ≥ κ log₂ T` (`IsPathCoinModel.tendstoInDistribution_occErr`).
* **The digital shift is normal too.** Post #2's contrast between the randomisations (Owen
  normal, digital shift not) does not carry over to two-state Markov stacks: the path coins of
  both have the same law (`map_owenPathCoins`), and the CLT holds for both
  (`tendstoInDistribution_occErr_owen`, `tendstoInDistribution_occErr_shift`). For three states
  the path laws differ (`owen_ne_shift_stayThenMove`).

See [corrections](docs/corrections.md), which also lists the claims made precise, the
hypotheses made explicit and the conventions.

## What is not formalised

* **The CLT for `n ≥ 3` states.** With several jumps in a row the jump paths share flips down to
  their common prefix, and for three states Owen scrambling and the digital shift give different
  path laws (`owen_ne_shift_stayThenMove`), so the two-state law equivalence is not available.
  The realisation-wise and dyadic bounds hold for every finite chain.
* **Lower bounds on the variance in general.** The variance hypothesis of the CLT is verified on
  one explicit sequence of times for one chain (`exampleChain`, `exampleTime`), not for general
  chains or times.
* **Other bases and dimensions**: base `b > 2`, and scrambled stacks of digital nets in `s ≥ 2`
  dimensions (for example to drive two-step transitions).
* **The five-state Farmer–Toda chain** of the post specifically, and the post's empirical tests
  (the normality tests and the simulated errors). The numerical checks quoted in some module
  docstrings are not formalised either.
* **The full path law of (ii) and (iii) for two states.** The law equivalence is proved for the
  path coins and hence for the main term; the occupation error itself is within `anscBound` of
  the main term for every flip table. An identity of the two path laws is not stated.
* **The MC comparison**: the `O(1/√T)` RMSE of MC for Markov chains is the post's rate and is not
  proved here; `MarkovDriving` proves the almost-sure LIL rate.

All names are in the namespace `RQMCMarkov.ScrambledStacks`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MonteCarlo](ScrambledStacks/MonteCarlo.lean) | 16 | Copied from `MarkovDriving` (originally `PointSets`): the uniform laws on `[0,1)` and `[0,1)^s`, the sample mean, MC unbiasedness, variance `σ²/n`, RMSE and CLT |
| [Unbiased](ScrambledStacks/Unbiased.lean) | 22 | Copied from `MarkovDriving` (originally `PointSets`): marginally uniform points are unbiased, the shift modulo 1, strata and stratum maps |
| [Driving](ScrambledStacks/Driving.lean) | 44 | Copied from `MarkovDriving`: the inverse-CDF update, driven paths, stacks and departure indices, occupation and transition counts, flow balance, spells and run lengths |
| [OccupationDiscrepancy](ScrambledStacks/OccupationDiscrepancy.lean) | 11 | Copied from `MarkovDriving`: the discrepancy-to-occupation inequality by telescoping Poisson's equation, departure discrepancies of stack paths |
| [Discrepancy](ScrambledStacks/Discrepancy.lean) | 21 | Copied from `MarkovDriving` (originally `PointSets`): counting functions, local and star discrepancy, the midpoint rule |
| [Koksma](ScrambledStacks/Koksma.lean) | 21 | Copied from `MarkovDriving` (originally `PointSets`): Koksma's inequality in one dimension |
| [VanDerCorput](ScrambledStacks/VanDerCorput.lean) | 22 | Copied from `MarkovDriving` (originally `PointSets`): the base-2 van der Corput sequence, its net property, `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n` |
| [StackBound](ScrambledStacks/StackBound.lean) | 21 | Copied from `MarkovDriving`: `\|N_ij − p_ij N_i\| ≤ 2 N D*_N`, the discrete Koksma inequality, van der Corput stacks at `O(log T / T)` |
| [StackDefs](ScrambledStacks/StackDefs.lean) | 57 | Binary expansions and digit prefixes, flip tables, the scrambled van der Corput point, digital shifts, stacks, the Owen and shift measures, the good event of probability one, each stack point uniform, measurability of paths and counts |
| [StackNet](ScrambledStacks/StackNet.lean) | 33 | Segment errors, the aligned-block property for every flip table, the segment lemma, the discrete Koksma inequality for threshold counts, the QMC bounds on transition counts, departure discrepancies and occupation for every realisation of both randomisations |
| [CltAnscombe](ScrambledStacks/CltAnscombe.lean) | 8 | The two-state identity for any stacks in `[0,1]`, `\|N₀ − T π₀\| = O(log T)`, the main term at deterministic indices and the deterministic Anscombe bound `O(log log T)` |
| [CltBlocks](ScrambledStacks/CltBlocks.lean) | 8 | Model-free: sequences with bounded aligned-block increments, prefix and segment bounds, the per-block jump formula for one point per dyadic cell |
| [Owen1DLindeberg](ScrambledStacks/Owen1DLindeberg.lean) | 4 | Copied from `OwenScrambling`: the Lindeberg CLT for bounded independent triangular arrays |
| [CltMDependent](ScrambledStacks/CltMDependent.lean) | 22 | Model-free: local functions and their independence, the bounded Lindeberg CLT under sequential independence, the CLT from independent bounded blocks, the CLT for sums of truncatable locally dependent terms |
| [CltPathBits](ScrambledStacks/CltPathBits.lean) | 39 | Threshold digits, lexicographic comparison, path prefixes and path coins, the per-block jump formula, the level decomposition of the local discrepancy, truncated tie cascades, the Owen path coins i.i.d. fair with the law of the digital-shift flips |
| [CltVariance](ScrambledStacks/CltVariance.lean) | 68 | Covariance tools, moments of the level terms, `Var ≤ 5K`, the lower bound `8k/45` on a digit pattern, path-coin models (Owen and shift), the main term as a coin sum, the example chain and times with `Var ≥ k/12` |
| [CltStacks](ScrambledStacks/CltStacks.lean) | 19 | Convergence in distribution through measure-preserving maps, the CLT for coin sums, Slutsky for a bounded perturbation, the CLT for two-state chains under Owen and shift, for every function of the state, on the example sequence, and the mean-square error `O(log T)` |
| [CltThreeState](ScrambledStacks/CltThreeState.lean) | 12 | The three-state chain with rows `(1/4, 1/2, 1/4)`, the cylinder "stay, then move", probability `1/8` under Owen and `1/4` under the digital shift |
| [StackDyadic](ScrambledStacks/StackDyadic.lean) | 27 | No limit without atoms for variables with finitely many values, dyadic thresholds with zero block error, bounded transition and occupation errors for dyadic chains, no CLT, the 7/8 chain with error at most `28` |
| [StackPowerOfTwo](ScrambledStacks/StackPowerOfTwo.lean) | 13 | The symmetric two-state chain, transition counts as threshold counts, the self-consistent bound along `T = 2^k`, no limit law along all `T` |
| [StackSpells](ScrambledStacks/StackSpells.lean) | 19 | The leaving digits `111` and `000` of the 7/8 chain, the leaving residue mod `8`, stays and spell starts in stack paths, the first spell `r + 1` and later spells `8`, the uniform law of `r` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (609 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
