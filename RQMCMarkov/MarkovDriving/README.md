# Driving a Markov chain by MC, QMC and RQMC sequences, in Lean

This is the `RQMCMarkov/MarkovDriving` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It
formalises the mathematical claims of post #3 of Robert Kirkby, "Simulating a Markov chain: MC,
QMC, RQMC", VFI Toolkit discourse, topic 687 (October 2026),
<https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687>, together with the
results from the literature that the post relies on: Chentsov (1967) and Owen and Tribble (2005)
on completely uniformly distributed (CUD) driving sequences, Holroyd and Propp (2010) on rotor
walks, Euler's theorem on Eulerian trails, and Meyn and Tweedie, Chapter 17, for the Monte Carlo
rate. Wherever post #3 says "theory tells us" or "theory shows" a convergence speed, the speed is
made precise and proved. It is the second project of the plan in
[PROPOSAL-RQMCMarkov.md](../../PROPOSAL-RQMCMarkov.md) (§2); posts #1–#2 are covered by
[RQMCMarkov/PointSets](../PointSets/README.md). Run the commands below from this directory.
[Return to the library index](../../README.md).

Post #3 simulates a chain with `n` states and transition matrix `P` by the inverse-CDF rule: from
state `i` with a uniform `u`, go to the smallest `j` with `u ≤ p_{i1} + ⋯ + p_{ij}`. A sequence of
uniforms then "drives" the chain. The post compares five ways of choosing the uniforms or the
path: MC (i.i.d. uniforms), QMC with one low-discrepancy sequence for the whole path, QMC with
one sequence per state (a *stack* for each state), conditional MC (a uniformly random path with
prescribed transition counts), and rotors (a fixed cycle of next states for each state), with
stratified spell lengths as a last refinement. The state space is finite throughout, as in the
post.

The library contains **621 theorems** (733 audited declarations) in 33 modules. Twenty-two modules
(447 theorems) are new. Eleven are carried, with the namespace renamed: `MonteCarlo`,
`Unbiased`, `Discrepancy`, `Koksma` and `VanDerCorput` from
[RQMCMarkov/PointSets](../PointSets/README.md) (102 theorems), and the six `MCRate…` modules
of the Hartman–Wintner law of the iterated logarithm (LIL) from
[StochasticStability/LimitTheorems](../../StochasticStability/LimitTheorems/README.md)
(72 theorems; generic lemma names prefixed `lil_`).

## The main theorem: one inequality ranks MC, QMC stacks and rotors

Post #3 ranks the methods by how fast the occupation frequencies `N_s(T)/T` (the fraction of
the first `T` periods spent in state `s`) and the empirical transition matrix approach their
targets: MC at `O(1/√T)`, per-state QMC stacks faster, rotors at `O(1/T)`, "better than QMC's
`O(log T / T)`". All of these come from one deterministic inequality, valid for **every** path.

For a test function `g` on the states, the *departure discrepancy* of state `i` up to time `T`
is `D_i(g, T) = Σ_{t < T, x_t = i} (g(x_{t+1}) − (Pg)(i))`. It is the error of the departures
from `i`, viewed as a sample from row `i` of `P` (`departureDiscrepancy`). Let `h` solve
Poisson's equation `h − Ph = 1_{s} − π_s` (it exists for every irreducible `P`, periodic or not,
`exists_poisson`), and `|h| ≤ M`. Telescoping `h` along the path gives

`|N_s(T) − T π_s| ≤ 2M + Σ_i |D_i(h, T)|`  (`abs_occCount_sub_le`):

the occupation error is at most a boundary term plus the departure discrepancies. The transition
counts satisfy the exact identity `N_ij(T) − p_ij N_i(T) = D_i(1_{j}, T)`
(`transCount_sub_eq_departureDiscrepancy`). In a stack path the departures from `i` are the first
`N_i(T)` points of stack `i`, so each `D_i` is an ordinary one-dimensional sampling error. The
three methods bound it differently, and the ranking theorem `occupation_error_ranking_driven`
collects the results for the post's own constructions:

| Driving | Occupation error `\|N_s(T) − T π_s\|` | Frequency error | Lean |
| --- | --- | --- | --- |
| MC, one i.i.d. uniform sequence | `≤ K + C √(2 T log log T)` almost surely | `O(√(log log T / T))` | `ae_abs_occCount_driven_le` |
| QMC, van der Corput stacks | `≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` | `O(log T / T)` | `abs_occCount_vdc_sub_le`, `occFreq_vdc_isBigO` |
| Rotors (Holroyd–Propp) | `≤ 2M (1 + Σ_i (L_i − 1))`, for every `T` | `O(1/T)` | `abs_occCount_rotorWalk_sub_le`, `occFreq_rotorWalk_isBigO` |

Here `V(h)` is the variation of `h` over the states (`stateVariation`) and `L_i` is the length of
the cycle of state `i`. The MC rate is sharp for the transition counts: if `π_i > 0`, the lower
half of the LIL shows that, almost surely, `N_ij(T) − p_ij N_i(T)` exceeds
`(σ − ε) √(2 N log log N)` infinitely often, with `N = N_i(T)` and `σ = √(p_ij (1 − p_ij))`
(`ae_frequently_transCount_driven_ge`), so for `0 < p_ij < 1` the MC error is not
`o(√(N log log N))` (`ae_not_tendsto_transCount_driven`). For the occupation counts only the
upper half is proved. The bounds for stacks and rotors are upper bounds; no lower bound for
stacks is proved.

## What is proved

* **Inverse-CDF driving gives the right chain** (`Driving`, `DrivingMC`, `MCRateDriven`). The
  update `step P i u` goes to `j` exactly when `u` lies in `j`'s interval of row `i`
  (`step_eq_iff`), and that interval has probability `p_ij` (`uniformIco_step_eq`). Post #3's
  worked example (`u = 0.79` with row `[0.2, 0.6, 0.2]`) is `step_post3_example`. Under i.i.d.
  uniforms the path has the Markov-chain law
  `P(x_0 = s_0, …, x_T = s_T) = 1{s_0 = x₀} ∏_t p_{s_t s_{t+1}}`, both for one driving sequence
  (`iidUniform_drivenPath_cylinder`) and for i.i.d. stacks (`iidUniform_stackPath_cylinder`).
  The two representations have the same path law, for every horizon
  (`map_drivenPath_eq_map_stackPath`) and as measures on whole paths
  (`map_drivenPath_eq_map_stackPath_path`).
* **The discrepancy-to-occupation inequality** (`OccupationPoisson`, `OccupationDiscrepancy`).
  For a finite irreducible `P`: a harmonic function is constant (maximum principle,
  `eq_of_mulVec_eq_self_of_irreducible`), the stationary distribution exists, is unique and
  positive (`existsUnique_isStationaryDistribution`, `IsStationaryDistribution.pos`), and
  Poisson's equation has a solution, unique up to a constant (`exists_poisson`,
  `poisson_sub_eq`). Aperiodicity is never assumed. The inequality itself is
  `abs_occCount_sub_le`, with the transition identity
  `transCount_sub_eq_departureDiscrepancy` and its consequence `abs_transCount_sub_le`. For stack
  paths, `departureDiscrepancy_stackDrive` writes `D_i` as a sum over the first `N_i(T)` stack
  points.
* **Stacks balance the departures** (`StackBound`). For any stacks with points in `[0,1)`,
  `|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(stack i)`, with `N = N_i(T)` and `D*_N` the star
  discrepancy (`abs_transCount_stackPath_sub_le`). A discrete Koksma inequality gives
  `|D_i(g, T)| ≤ V(g) N D*_N` (`abs_sum_step_sub_le`, `abs_departureDiscrepancy_stackPath_le`).
  With a copy of the van der Corput sequence (the one-dimensional Sobol sequence) for each state,
  `|N_ij(T) − p_ij N_i(T)| ≤ 2 (⌊log₂ T⌋ + 1)` (`abs_transCount_vdc_sub_le`), the empirical
  transition matrix is within `O(log T / T)` of `P` (`empiricalTrans_vdc_isBigO`), and so are the
  occupation frequencies of `π` (`occFreq_vdc_isBigO`).
* **Rotors** (`RotorRouter`). A balanced cycle for state `i` lists `j` exactly `p_ij L_i` times
  (`IsRotorCycle`, which needs rational `P`). The rotor walk sends the `k`-th departure from `i`
  to entry `k` of `i`'s cycle, from offsets `θ` (`rotorWalk`). The transition counts are within
  one cycle of `p_ij N_i(T)` (`abs_transCount_rotorWalk_sub_le`), and equal to it whenever
  `L_i` divides `N_i(T)` (`transCount_rotorWalk_eq_of_dvd`). The Holroyd–Propp bound
  `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L_i − 1))` holds for every `T` and every offsets
  (`abs_occCount_rotorWalk_sub_le`). With uniformly random offsets (post #3's randomized rotor)
  each single departure has law `P(i, ·)` (`card_offset_eq`), and the expected occupation is
  within the same constant of `T π_s` (`abs_expected_occCount_rotorWalk_sub_le`).
* **The MC rate** (`MCRate`, `MCRateDriven`, the carried `MCRateLIL…` modules). With i.i.d.
  uniform stacks the departures from `i` are i.i.d. draws from row `i`, so `D_i(g, T)` is a
  random-index partial sum, and the Hartman–Wintner LIL applies (`hasLIL_mcDepartureSum`). For
  the post's construction, one i.i.d. sequence driving the whole path: almost surely
  `|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij (1 − p_ij)) + ε) √(2 T log log T)`
  (`ae_abs_transCount_driven_le`); the occupation error is `≤ K + C √(2 T log log T)`
  (`ae_abs_occCount_driven_le`); and the lower half quoted above
  (`ae_frequently_transCount_driven_ge`, `ae_not_tendsto_transCount_driven`). The ranking
  theorem is `occupation_error_ranking_driven` (one driving sequence) and
  `occupation_error_ranking` (any i.i.d. stacks, with the every-path inequality as part 0).
* **Conditional MC** (`ConditionalMC`). A path's MC probability is
  `1{s_0 = x₀} ∏_{i,j} p_ij^{N_ij}`, so it depends only on its start and its transition counts
  (`pathProb_eq_of_transCount_eq`). Hence MC conditional on the start and the counts is the
  uniform law on the paths with that start and those counts (`cond_mcLaw_countClass`): post
  #3's "exactly MC conditional on the counts". **Euler's theorem**: counts balanced from `x₀` to
  `y` (out-count minus in-count `1{x₀} − 1{y}` at every state), whose support is reachable from
  `x₀`, are the counts of a path from `x₀` to `y` (`exists_path_of_balanced`), and conversely
  (`exists_path_iff`).
* **Rounding the expected counts** (`ConditionalMCRounding`, `ConditionalMCRoundingOpen`). The
  matrix `T π_i p_ij` is a circulation with total `T` (`isCirculation_expectedCounts`). Every
  real circulation has an integer circulation rounding `⌊x_ij⌋ ≤ n_ij ≤ ⌈x_ij⌉`
  (`exists_int_circulation_rounding`, `exists_rounding_expectedCounts`), and for irreducible `P`
  it is realised by a closed path (`exists_closed_path_of_rounding`). Its total can differ from
  `T`. Balanced "allowing for the first and last states", the rounding can always have total
  exactly `T` (`exists_open_rounding`), and it is realised by a path of exactly `T` transitions
  (`exists_path_exact_length`). In both versions post #3's conditional MC is well defined: the
  conditioning event has positive MC probability and the conditional law is uniform
  (`conditionalMC_wellDefined`, `conditionalMC_exact_wellDefined`).
* **Spells and stratified spell lengths** (`SpellStratified`). Under MC, after any history
  ending in state `i`, the remaining stay in `i` is geometric with stay probability `p_ii`
  (`iidUniform_spell_after_history`, `iidUniform_runLength_eq`). The geometric inverse CDF
  `geomQuantile p` reproduces this law (`uniformIco_geomQuantile_eq_firstSpell`), with mean
  `1/(1 − p)` and variance `p/(1 − p)²` (`integral_geomQuantile_id`, `variance_geomQuantile`).
  Post #3's stratified spell lengths, one draw in each of `K` equal intervals, are unbiased for
  the mean spell length (`integral_stratifiedSpell`), with variance at most that of `K` i.i.d.
  spell lengths (`variance_stratifiedSpell_le_iid`), explicitly `≤ p/((1 − p)² K)`
  (`variance_stratifiedSpell_le`).
* **Rotor spells are too regular** (`RotorSpells`). If the cycle of `i` contains a state other
  than `i` (as a balanced cycle does when `p_ii < 1`), every rotor spell in `i` lasts at most
  `L_i` periods, while for `p_ii > 0` the geometric law gives probability `p_ii^{L_i} > 0` to
  longer spells (`rotor_spells_not_geometric`). For the two-state
  chain with stay probability `7/8` and the cycle "seven stays, then a switch": with zero offsets
  every spell lasts exactly `8` periods (`rotorWalk78_canonical`); with any offsets, the walk is
  this canonical walk after some `τ ≤ 16` (`rotorWalk78_eventually_canonical`,
  `runLength_rotorWalk78`). At most `16` spells ever differ from `8`, while the geometric law
  gives a spell of length `8` probability below `1/16` (`rotor78_spells_not_geometric`).
* **CUD sequences** (`CUDDefs`, `CUDVanDerCorput`, `CUDExistence`). Uniform distribution in
  `[0,1)^d` (`IsUD`) and complete uniform distribution: every `d`-tuple of consecutive terms is
  uniformly distributed (`IsCUD`). A sequence with finitely many values, in particular a periodic
  one, is not CUD (`not_isCUD_of_finite_range`, `not_isCUD_of_periodic`). The van der Corput
  sequence is uniformly distributed (`isUD_vanDerCorput`) but not CUD: consecutive terms always
  fall in different halves of `[0,1)` (`not_isCUD_vanDerCorput`). It fails as a driving sequence:
  for the chain with rows `(1/2, 1/2)` and `(1, 0)`, whose stationary distribution is
  `(2/3, 1/3)`, the driven path alternates from time `3` on, so state `1` gets frequency `1/2`
  instead of `1/3` (`tendsto_occFreq_twoState_vanDerCorput`,
  `not_tendsto_occFreq_twoState_vanDerCorput`), whereas every CUD sequence gives `1/3`
  (`tendsto_occFreq_twoState_of_isCUD`). CUD sequences exist: an i.i.d. uniform sequence is CUD
  almost surely (`ae_isCUD_iidUniform`, `exists_isCUD`).
* **Chentsov's theorem** (`ChentsovConsistency`, `ChentsovEntropy`, `ChentsovGeneral`,
  `ChentsovIrreducible`). For **every** stochastic matrix on a finite state space with a unique
  stationary distribution `π`, the path driven through the inverse-CDF update by any CUD sequence,
  from any start, has `N_j(T)/T → π_j` and time averages `(1/T) Σ_t g(x_t) → Σ_j π_j g(j)`
  (`tendsto_occFreq_of_isCUD_general`, `tendsto_timeAvg_of_isCUD_general`). The proof takes a
  limit point of the empirical joint frequencies along an ultrafilter and shows, by an entropy
  argument (data processing and Gibbs' inequality), that the limit state is independent of the
  next input, hence stationary (`chentsov_entropy_stationary`). The irreducible case, periodic
  chains included, is `tendsto_occFreq_of_isCUD_irreducible` and
  `tendsto_timeAvg_of_isCUD_irreducible`; since i.i.d. uniforms are CUD almost surely, it contains
  the MC ergodic theorem for the inverse-CDF chain (`ae_tendsto_occFreq_iidUniform_irreducible`).
  The coupling form of the literature (Owen and Tribble 2005), under a box of inputs that sends
  every state to one state, is `tendsto_occFreq_of_isCUD`, with sufficient conditions
  `hasCouplingBox_of_col_pos` and `hasCouplingBox_of_pos`.

## Corrections

Five claims of post #3 and its codes are false as stated. Each is refuted in Lean, and a
corrected statement is proved.

* Chentsov's consistency needs a condition on the chain: for the identity matrix on two states
  the frequencies depend on the start whatever the driving sequence
  (`not_tendsto_occFreq_identity`). Uniqueness of the stationary distribution suffices
  (`tendsto_occFreq_of_isCUD_general`).
* The codes' "CUD sequence (a full-period linear congruential generator)" cannot be CUD, since a
  periodic sequence takes finitely many values (`not_isCUD_of_periodic`).
* MC does not converge at `O(1/√T)` almost surely. The almost-sure rate of the transition
  counts is `√(T log log T)`, and of the empirical matrix `√(log log T / T)`, by the LIL
  (`ae_abs_transCount_driven_le`, `ae_not_tendsto_transCount_driven`). `1/√T` is right at the
  root-mean-square scale, exactly: `E[(N_ij(T) − p_ij N_i(T))²] = p_ij(1 − p_ij) E[N_i(T)]`
  (`integral_sq_transCount_sub_driven`), the occupation frequency has RMSE `O(1/√T)`
  (`integral_sq_occFreq_sub_driven_le`) and no better for non-degenerate chains
  (`eventually_integral_sq_occCount_sub_driven_ge_of_irreducible`, instance
  `occCount_mse_twoStateStay78`), and in distribution:
  `(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))`
  (`tendstoInDistribution_transCount_driven_of_irreducible`).
* Rotors do not give "the same exact expected number of transitions" as conditional MC, since
  `T π_i p_ij` need not be an integer (`not_transCount_eq_target`); they give counts within one
  cycle of `p_ij N_i(T)`.
* The randomized rotor, listed among the RQMC methods, is not exactly unbiased for the occupation
  counts, even from a stationary start (`expected_occCount_ne`).

Four more claims are made precise. "Every spell lasts exactly 8 periods" holds exactly for the
rotor with zero offsets, and after `τ ≤ 16` periods for any offsets
(`rotorWalk78_eventually_canonical`). Rotor spells are never geometric, in every state with
`0 < p_ii < 1` (`rotor_spells_not_geometric`). Driving by one van der Corput (Sobol)
sequence gives the wrong frequencies (`not_tendsto_occFreq_twoState_vanDerCorput`). The stack
rate "faster than `O(1/√T)`" is `O(log T / T)`, and "rotors better than QMC" is a comparison of
upper bounds. Two technical points are not corrections to the post: the coupling-box hypothesis
of the literature's proof is not implied by irreducibility and aperiodicity
(`not_hasCouplingBox_fourState`), but it is not needed; and a closed balanced rounding of
`T π_i p_ij` cannot always have total `T` (`not_exists_rounding_flipChain_total_three`), so the
post's open-path wording is the right one (`exists_open_rounding`). See
[corrections](docs/corrections.md), which also lists the hypotheses made explicit.

## What is not formalised

* **The BEST theorem**: counting the Eulerian trails with given counts by spanning trees, and the
  exact sampler built on a random spanning tree. Euler's theorem (existence of a path with given
  counts) is proved.
* **The CLT for the MC occupation counts** `N_s(T)` (the CLT for the transition counts is proved,
  `MCRateCLT`), and the degenerate case `π_i = 0`.
* **The heuristic of approach (vii)**: "adjusting" the stratified spell lengths so that they add
  up to the time spent in the state, and the random order of the spells. The stratified lengths
  themselves are formalised.
* **Empirical claims** of the post and its codes: (a) "fails badly", "almost exactly right"
  counts for (ii)–(iv), the spell-length accuracy of (v)–(vii), "CUD (i) improves on MC", the
  normality tests, and "the best performing approach in our codes". The "exactly 8" spells are
  proved for rotors, not for the Sobol stacks (ii)–(iii).
* **Other constructions**: Sobol stacks with a random digital shift or Owen scrambling, two-step
  counts (vi), Array-RQMC (PPPS), burn-in (PS; the bounds above hold for every start), and the
  MEP application (post #4 is a placeholder).
* **Lower bounds** for stacks: the post's "better than QMC's `O(log T / T)`" is proved for the
  upper bounds only.
* Identification of the driven path law with Mathlib's `Kernel.traj` (the finite-dimensional laws
  are proved); "rotors are the RQMC version of conditional MC", which is informal.

All names are in the namespace `RQMCMarkov.MarkovDriving`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MonteCarlo](MarkovDriving/MonteCarlo.lean) | 16 | Carried from `PointSets`: the uniform laws on `[0,1)` and `[0,1)^s`, the sample mean, MC unbiasedness, variance `σ²/n`, RMSE and CLT |
| [Unbiased](MarkovDriving/Unbiased.lean) | 22 | Carried from `PointSets`: marginally uniform points are unbiased, the shift modulo 1, strata and the stratum maps `(i + u)/n` used for stratified spell lengths |
| [Discrepancy](MarkovDriving/Discrepancy.lean) | 21 | Carried from `PointSets`: counting functions, local and star discrepancy, the QMC estimate, the midpoint rule |
| [Koksma](MarkovDriving/Koksma.lean) | 21 | Carried from `PointSets`: Koksma's inequality in one dimension |
| [VanDerCorput](MarkovDriving/VanDerCorput.lean) | 22 | Carried from `PointSets`: the base-2 van der Corput sequence, its net property, `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n` |
| [Driving](MarkovDriving/Driving.lean) | 44 | Post #3's inverse-CDF update and its intervals, the worked example, driven paths, stacks and departure indices, occupation and transition counts, flow balance, spells and run lengths |
| [DrivingMC](MarkovDriving/DrivingMC.lean) | 21 | The i.i.d. uniform measure, cylinder probabilities for one driving sequence and for i.i.d. stacks, the path probability, equal laws of `(x_0, …, x_T)` for the two representations |
| [ConditionalMC](MarkovDriving/ConditionalMC.lean) | 18 | Path probability as a function of the counts, MC conditional on start and counts is uniform, balanced counts, Euler's theorem by splicing closed trails, realisable count matrices |
| [ConditionalMCRounding](MarkovDriving/ConditionalMCRounding.lean) | 22 | Circulations and the cut identity, fractional cycles, integer circulation rounding, `T π_i p_ij` as a circulation, closed paths with the rounded counts, conditional MC well defined, the flip-chain counterexample to total `T` |
| [ConditionalMCRoundingOpen](MarkovDriving/ConditionalMCRoundingOpen.lean) | 16 | Simple cycles of fractional arcs, pushes along circulations, the discrete intermediate value theorem, open rounding with total exactly `T`, paths of exactly `T` transitions, conditional MC with exact length |
| [SpellStratified](MarkovDriving/SpellStratified.lean) | 24 | MC spell lengths geometric after any history, the geometric inverse CDF, its mean `1/(1 − p)` and variance `p/(1 − p)²`, stratified spell lengths unbiased with variance `≤ p/((1 − p)² K)` |
| [OccupationPoisson](MarkovDriving/OccupationPoisson.lean) | 21 | Stationary distributions, the maximum principle, existence, uniqueness and positivity of `π` for irreducible `P`, Poisson's equation and the uniqueness of its solution up to a constant |
| [OccupationDiscrepancy](MarkovDriving/OccupationDiscrepancy.lean) | 11 | Departure discrepancies, the telescoping identity, the discrepancy-to-occupation inequality, the transition identity, departures of stack paths |
| [StackBound](MarkovDriving/StackBound.lean) | 21 | Departures as a QMC sample of the row, `\|N_ij − p_ij N_i\| ≤ 2 N D*_N`, the discrete Koksma inequality, van der Corput stacks: transition counts within `2 (⌊log₂ T⌋ + 1)`, occupation and empirical transition errors `O(log T / T)` |
| [RotorRouter](MarkovDriving/RotorRouter.lean) | 24 | Balanced cycles, the rotor walk and its shift property, transition counts within one cycle and exact at full cycles, the Holroyd–Propp bound and `O(1/T)`, the randomized rotor, the counterexamples to exact counts and exact unbiasedness |
| [RotorSpells](MarkovDriving/RotorSpells.lean) | 15 | Rotor spells bounded by the cycle length and never geometric, the `7/8` chain: spells of exactly `8` with zero offsets and after `τ ≤ 16` for any offsets |
| [MCRateKolmogorovAnscombe](MarkovDriving/MCRateKolmogorovAnscombe.lean) | 6 | Carried from `LimitTheorems`: Kolmogorov's inequality, the random-index step |
| [MCRateLILAnalysis](MarkovDriving/MCRateLILAnalysis.lean) | 26 | Carried from `LimitTheorems`: the LIL scale `√(2 n log log n)`, Kronecker's lemma, geometric index sequences |
| [MCRateLILExponential](MarkovDriving/MCRateLILExponential.lean) | 8 | Carried from `LimitTheorems`: exponential bounds, the exponential maximal inequality, block independence |
| [MCRateLILUpper](MarkovDriving/MCRateLILUpper.lean) | 12 | Carried from `LimitTheorems`: the upper half of the Hartman–Wintner LIL by truncation |
| [MCRateLILLower](MarkovDriving/MCRateLILLower.lean) | 13 | Carried from `LimitTheorems`: the lower half of the LIL by blocks, the CLT and the second Borel–Cantelli lemma |
| [MCRateIIDLIL](MarkovDriving/MCRateIIDLIL.lean) | 7 | Carried from `LimitTheorems`: the Hartman–Wintner LIL for i.i.d. sequences, in `ε`-form and as `limsup`/`liminf` |
| [MCRate](MarkovDriving/MCRate.lean) | 21 | i.i.d. uniform stacks, the departure sums and row variances, the LIL for the departures, MC upper and lower rates for transition and occupation counts, the ranking theorems |
| [MCRateDriven](MarkovDriving/MCRateDriven.lean) | 17 | Equal path laws on `ℕ → Fin n` for one driving sequence and i.i.d. stacks, transfer of almost-sure path events, the MC rates and the ranking theorem for the post's single-sequence MC |
| [MCRateRMSE](MarkovDriving/MCRateRMSE.lean) | 40 | The time-filtration martingale of the post's MC (one i.i.d. driving sequence), orthogonal increments, `E[(N_ij − p_ij N_i)²] = p_ij(1 − p_ij) E N_i(T)`, the second moment of the departure sums, two-sided bounds on the occupation mean-square error, `E N_s(T)/T → c`, RMSE of exact order `1/√T` for non-degenerate (irreducible) chains, the 7/8 instance |
| [MCRateCLT](MarkovDriving/MCRateCLT.lean) | 11 | i.i.d. departure increments, the CLT at a deterministic index, the random-index (Anscombe) step, `(N_ij − p_ij N_i)/√T ⇒ N(0, π_i p_ij (1 − p_ij))` for the driven path, the 7/8 instance `N(0, 7/128)` |
| [CUDDefs](MarkovDriving/CUDDefs.lean) | 26 | Box indicators, uniform distribution, windows and CUD, boxes with arbitrary sides, step functions and Weyl's criterion for them, finitely many values or a period exclude CUD |
| [CUDVanDerCorput](MarkovDriving/CUDVanDerCorput.lean) | 19 | Discrepancy `→ 0` gives uniform distribution, van der Corput uniformly distributed but not CUD, the two-state chain on which it drives the wrong frequencies, CUD driving consistent on that chain |
| [CUDExistence](MarkovDriving/CUDExistence.lean) | 13 | Interleaved averages, uniform distribution from grid boxes, window frequencies of i.i.d. uniforms by the strong law, i.i.d. uniforms CUD almost surely, CUD sequences exist |
| [ChentsovConsistency](MarkovDriving/ChentsovConsistency.lean) | 33 | Window maps and multistep probabilities, coupling boxes, Chentsov's theorem in coupling form, sufficient conditions, the identity-chain counterexample, the four-state chain without a coupling box |
| [ChentsovEntropy](MarkovDriving/ChentsovEntropy.lean) | 10 | Gibbs' inequality with its equality case, the log-sum inequality, data processing for the Kullback–Leibler sum, the entropy lemma: a stationary chain driven by i.i.d. inputs is independent of the next input |
| [ChentsovGeneral](MarkovDriving/ChentsovGeneral.lean) | 16 | Products of step functions, the cells of the inverse-CDF update, Chentsov's theorem for every finite chain with a unique stationary distribution, the four-state chain is consistent |
| [ChentsovIrreducible](MarkovDriving/ChentsovIrreducible.lean) | 4 | Uniqueness of `π` for irreducible chains, Chentsov's theorem for irreducible chains, the MC ergodic theorem as a corollary |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (733 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
