# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 8, "Additional Applications" (pp. 247–293), with the Appendix A results the chapter uses.
Result, equation and exercise numbers are the book's; page numbers are book pages. Lean names are
relative to `SargentStachurski.AdditionalApplications`. Where the Lean statement adds a
hypothesis the book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 | `GloballyStable`, contractions |
| `SupContraction`, `MarkovOperator` | Volume 2, Chapter 1 | `bX` as a set, Markov operators |
| `OrderTheory`, `ADP`, `Algorithms`, `Minimization` | Volume 2, Chapter 2 | ADPs, optimality, VFI/OPI/HPI, min-optimality and Corollary 2.2.10 |
| `Pospace`, `MetricADP`, `BoundedMeasurable`, `MinPospace` | Volume 2, Chapter 3 | Theorem 3.1.5, `bX` as a Banach lattice (`BM`) |
| `BanachLattice`, `OrderContraction`, `BMOperators`, `DuTheorem`, `L1Operators` | Volume 2, Chapter 4 | Theorems 4.1.3, 4.1.8, 4.1.10–4.1.11; operators on `L¹(ψ)` |
| `Conjugacy`, `Semiconjugacy`, `FactoredDP` | Volume 2, Chapter 5 | FDPs, Theorem 5.2.13 |
| `Correspondences`, `LDP`, `LDPOptimality`, `Feller` | Volume 2, Chapter 6 | Theorem A.3.3 for intervals, `bcX` |
| `UniqueMax`, `RDP`, `BoundedRDP`, `WeightedRDP`, `SolutionProperties` | Volume 2, Chapter 7 | RDPs, Proposition 7.2.2, Lemma 7.1.2, Lemma A.2.6 |

## Appendix A and outside results used in Chapter 8

| Book | Claim | Lean |
| --- | --- | --- |
| Prop A.5.20, p. 380 | Fixed point comparison (for contractions on complete ordered metric spaces) | `fixedPoint_ge_of_le` |
| Prop A.5.34, p. 391 | Monotone likelihood ratio implies first order stochastic dominance (for densities) | `IsMLR`, `TwoDensities`, `TwoDensities.proposition_A_5_34` |
| §A.5.5, p. 390 | First order stochastic dominance; mean-preserving spreads | `FOSDle`, `IsMPS`, `integral_max_le_of_isMPS` |
| Lemma A.5.19 (as used in Thm 8.3.6) | An order preserving map whose orbits are eventually equal is order stable | `orderStable_of_iterate_eq` |
| Clausen and Strub (2020) | The differentiable sandwich (concave case) | `hasDerivAt_of_concave_sandwich` |
| §8.2.2 | Kreps–Porteus power means | `pmean`, `PosBdd`, `pmean_mono`, `pmean_const`, `pmean_smul`, `pmean_add_ge`, `pmean_add_le`, `pmean_concave`, `pmean_convex`, `convexOn_rpow_of_neg` |

## §8.1.1 The basic model (pp. 247–250)

| Book | Claim | Lean |
| --- | --- | --- |
| Assumption 8.1.1, (8.1)–(8.3) | The iid model | `JobSearch.iid`, `JobSearch.iid_Pop_coeFn` |
| Ex 8.1.1, p. 248 | `T_σ` is a self-map with a unique fixed point | `JobSearch.wellPosed`, `JobSearch.proposition_8_1_1` |
| Exs 8.1.2–8.1.3, p. 248 | The policy (8.5) is greedy; the Bellman operator (8.6) | `JobSearch.exercise_8_1_2_3` |
| §8.1.1.2, (8.4) | Bounded offers | `BoundedSearch.cont`, `BoundedSearch.T`, `BoundedSearch.T_apply`, `BoundedSearch.cont_mono`, `BoundedSearch.adp`, `BoundedSearch.accept` |
| Ex 8.1.4, p. 248 | `(bW, 𝕋)` is an ADP, (8.7), `T` preserves `bcW`, `ibcW`, `ibcW₊` | `BoundedSearch.exercise_8_1_4`, `BoundedSearch.exercise_8_1_4_bellman`, `BoundedSearch.exercise_8_1_4_counterexample` |
| Ex 8.1.5, (8.8), p. 249 | An RDP with `Γ(w) = {0, 1}` | `BoundedSearch.Bagg`, `BoundedSearch.exercise_8_1_5` |
| Prop 8.1.1, p. 249 | Optimality with iid offers | `JobSearch.proposition_8_1_1` |

## §8.1.2 Rearranging the Bellman equation (pp. 250–254)

| Book | Claim | Lean |
| --- | --- | --- |
| (8.9)–(8.14) | Continuation values, `g` | `gfun`, `integrable_max_wage`, `hstar`, `hstar_eq`, `hstar_unique`, `wstar` |
| Ex 8.1.6, (8.15), p. 251 | `g` is a contraction | `exercise_8_1_6`, `gfun_contracting`, `gfun_mono` |
| Ex 8.1.7, p. 251 | `g` maps `[0, K]` into itself | `exercise_8_1_7` |
| §8.1.2.1, (8.12)–(8.13) | `v* = max{e, h*}`, the reservation wage policy is optimal | `JobSearch.section_8_1_2_1` |
| §8.1.2.2, p. 252 | The FDP; its primary ADP; `g` is the subordinate Bellman operator; (8.16) is optimal | `JobSearchFDP.eL`, `JobSearchFDP.G`, `JobSearchFDP.G_coeFn`, `JobSearchFDP.fdp`, `JobSearchFDP.isOrderPreserving`, `JobSearchFDP.Gsup_coeFn`, `JobSearchFDP.ADP.ext_T`, `JobSearchFDP.section_8_1_2_2` |
| Example 8.1.1, p. 253 | `h*` increases with `c` | `example_8_1_1` |
| Ex 8.1.9, p. 254 | `w*` increases with `c`; `h*` increases with `β` | `example_8_1_1`, `exercise_8_1_9` |
| (8.17), Ex 8.1.10, p. 254 | `w*` increases with `β` when `c ≤ w̄` | `ffun`, `ffun_contracting`, `ffun_mono`, `wstar_eq_fixedPoint`, `exercise_8_1_10` |
| Ex 8.1.11, p. 254 | The mean first passage time increases with `c` | `accept_iff`, `firstPassage`, `firstPassage_mono`, `exercise_8_1_11` |
| Ex 8.1.12, p. 254 | First order stochastic dominance raises `w*` | `FOSDle`, `exercise_8_1_12` |
| Ex 8.1.13, (8.18), p. 254 | Mean-preserving spreads raise `w*` | `IsMPS`, `integral_max_le_of_isMPS`, `exercise_8_1_13` |

## §8.1.3 Correlated wage draws (pp. 255–261)

| Book | Claim | Lean |
| --- | --- | --- |
| Assumption 8.1.2, (8.19) | Markov offers on `L¹(φ)`; `T_σ v = r_σ + K_σ v` | `StopPolicy`, `polInd`, `polCont`, `acceptWhere`, `acceptWhere_apply`, `JobSearch`, `JobSearch.Pop`, `JobSearch.D`, `JobSearch.efun`, `JobSearch.e`, `JobSearch.cconst`, `JobSearch.rσ`, `JobSearch.Kσ`, `JobSearch.adp`, `JobSearch.T_coeFn` |
| Ex 8.1.14, p. 255 | `T_σ` is order preserving | `JobSearch.exercise_8_1_14` |
| Ex 8.1.15, (8.20)–(8.21), p. 255 | The greedy policy; the Bellman operator | `JobSearch.accept`, `JobSearch.T_accept_coeFn`, `JobSearch.exercise_8_1_15`, `JobSearch.regular` |
| Ex 8.1.16, p. 256 | `T_σ` is order continuous | `L1.tendsto_of_monotone_isLUB`, `JobSearch.exercise_8_1_16` |
| Ex 8.1.17, (8.22), p. 256 | `v_σ` is the Neumann series | `JobSearch.exercise_8_1_17`, `JobSearch.iterate_T_zero` |
| Prop 8.1.2, p. 256 | Optimality by Theorem 4.1.8 | `JobSearch.isAdditive`, `JobSearch.specRad_D_lt_one`, `JobSearch.isGloballyStable`, `JobSearch.proposition_8_1_2` |
| Exs 8.1.18–8.1.20, p. 256 | The interval `[0, v̄]`; finite HPI | `JobSearch.Sbar`, `JobSearch.vbar`, `JobSearch.exercise_8_1_18`, `JobSearch.adpV`, `JobSearch.exercise_8_1_19`, `JobSearch.exercise_8_1_20` |
| §8.1.3.3, (8.23)–(8.28) | Persistent and transient components | `PersistentSearch`, `PersistentSearch.Φσ`, `PersistentSearch.adp`, `PersistentSearch.T_eq` |
| Exs 8.1.21–8.1.22, (8.29), p. 260 | The greedy policy; the Bellman operator | `PersistentSearch.accept`, `PersistentSearch.exercise_8_1_21_22`, `PersistentSearch.regular` |
| Ex 8.1.23, p. 260 | `T̂` is a contraction | `PersistentSearch.That`, `PersistentSearch.exercise_8_1_23`, `PersistentSearch.That_contracting` |
| p. 260 | Optimality by Theorem 4.1.8 | `PersistentSearch.section_8_1_3_3` |
| Ex 8.1.24, p. 260 | `h*` increases with `c` | `PersistentSearch.withC`, `PersistentSearch.exercise_8_1_24` |

## §8.2 Extensions (pp. 261–272)

| Book | Claim | Lean |
| --- | --- | --- |
| §8.2.1, p. 261 | Nonlinear discounting; `β(x) = b(1 − e^{−λx})` | `NLDiscount`, `bexp`, `bexp_properties`, `NLDiscount.vbar`, `NLDiscount.H` |
| Ex 8.2.1, p. 262 | `H` is an order preserving self-map of `V` | `NLDiscount.exercise_8_2_1` |
| Ex 8.2.2, p. 262 | `H` satisfies Du's conditions; the fixed point `e` | `NLDiscount.concaveOn_H`, `NLDiscount.exercise_8_2_2`, `NLDiscount.e`, `NLDiscount.H_e` |
| Ex 8.2.3, p. 263 | `T_σ` maps `V` into itself | `NLDiscount.cont`, `NLDiscount.Tfun`, `NLDiscount.exercise_8_2_3` |
| Ex 8.2.4, p. 263 | Optimality by Theorem 4.1.11 | `NLDiscount.adp`, `NLDiscount.accept`, `NLDiscount.regular`, `NLDiscount.concaveOn_T`, `NLDiscount.exercise_8_2_4` |
| §8.2.2, Ex 8.2.5, p. 264 | The Kreps–Porteus operator `R` | `KPSearch`, `KPSearch.Rf`, `KPSearch.exercise_8_2_5` |
| §8.2.2, p. 264 | The `ε` bounds; optimality for every `γ ≠ 1` | `KPSearch.vbar`, `KPSearch.Tfun`, `KPSearch.adp`, `KPSearch.regular`, `KPSearch.section_8_2_2` |
| §8.2.3.1, Assumption 8.2.1, (8.32) | Learning: two densities, Bayes' rule, `φ_π` | `TwoDensities`, `TwoDensities.φ`, `TwoDensities.κ`, `TwoDensities.κ_mem`, `LearningSearch`, `LState` |
| Ex 8.2.6, p. 266 | The greedy policy | `LearningSearch.contR`, `LearningSearch.T`, `LearningSearch.adp`, `LearningSearch.accept`, `LearningSearch.exercise_8_2_6` |
| Ex 8.2.7, (8.33), p. 266 | The Bellman equation | `LearningSearch.exercise_8_2_7`, `LearningSearch.regular`, `LearningSearch.optimality` |
| (8.34)–(8.36) | The reservation wage operator `T̂`; `v* = max{w, ω*(π)}/(1 − β)` | `LearningSearch.That`, `LearningSearch.That_eq`, `LearningSearch.ωstar`, `LearningSearch.vOf`, `LearningSearch.contR_vOf`, `LearningSearch.bellman_eq_iff` |
| Ex 8.2.8, p. 267 | `T̂` is a contraction of modulus `β` on `b[0, 1]` | `LearningSearch.exercise_8_2_8`, `LearningSearch.That_contracting` |
| Ex 8.2.9, p. 267 | `T̂` maps `bc[0, 1]` into itself | `TwoDensities.continuous_κ`, `LearningSearch.exercise_8_2_9`, `LearningSearch.continuous_ωstar` |
| Prop 8.2.1, p. 269 | Under MLR, `ω*` is increasing | `TwoDensities.κ_mono_prior`, `TwoDensities.κ_mono_offer`, `TwoDensities.integral_mul_φ`, `LearningSearch.That_monotone`, `LearningSearch.proposition_8_2_1` |
| Ex 8.2.10, p. 269 | Mixtures are ordered by `⪯_F` | `exercise_8_2_10` |
| Ex 8.2.11, (8.38), p. 269 | Beta(4, 2) and Beta(2, 4) have the MLR property | `betaF`, `betaG`, `exercise_8_2_11` |
| §8.2.4, (8.39)–(8.42) | Separation; (8.41); the ADP | `eq_8_41`, `Separation`, `Separation.h`, `Separation.γ`, `Separation.T`, `Separation.adp` |
| (8.43) | The greedy policy | `Separation.accept`, `Separation.accept_isGreedy`, `Separation.regular` |
| Ex 8.2.12, p. 271 | `T_σ` is a contraction of modulus `β ∨ γ` | `Separation.exercise_8_2_12` |
| Prop 8.2.2, p. 271 | Optimality | `Separation.proposition_8_2_2` |
| Ex 8.2.13, (8.44)–(8.46), p. 272 | `v*_u` and `v*_e` | `Separation.bellman_apply`, `Separation.bellman_contracting`, `Separation.exercise_8_2_13` |

## §8.3.1 Coase meets Bellman (pp. 273–281)

| Book | Claim | Lean |
| --- | --- | --- |
| §8.3.1.1, (8.47) | The production chain; firm boundaries | `ProductionChain`, `boundary` |
| Def 8.3.1, p. 275 | Equilibrium | `IsChainEquilibrium` |
| (8.48), Prop 8.3.1, p. 275 | `T` maps `𝒫` into itself, has a unique fixed point, and `Tᵏp → p*` | `ProductionChain.exists_η`, `ProductionChain.toNeg`, `ProductionChain.proposition_8_3_1` |
| (8.49)–(8.50), Prop 8.3.2, p. 276 | `n*` is finite and `(p*, A*)` is an equilibrium | `ProductionChain.proposition_8_3_2` |
| §8.3.1.2, (8.52)–(8.53) | Negative discounting; the threshold `η` | `NegDiscount`, `NegDiscount.η_spec_of_eq`, `NegDiscount.k0` |
| p. 279 | The policy set `Σ`; `V`; `T_σ` | `NegDiscount.Policy`, `NegDiscount.Policy.le_max_sub`, `NegDiscount.Policy.abs_sub_le`, `NegDiscount.Policy.continuousOn`, `NegDiscount.ση`, `NegDiscount.Val`, `NegDiscount.T`, `NegDiscount.T_apply`, `NegDiscount.adp` |
| Ex 8.3.1, (8.54), p. 279 | The iterates of `T_σ` | `NegDiscount.exercise_8_3_1` |
| Lemma 8.3.3, (8.55), p. 280 | `T_σᵏ v = v_σ` for `k ≥ k₀` | `NegDiscount.Policy.iterate_eq_zero`, `NegDiscount.iterate_k0_eq`, `NegDiscount.lemma_8_3_3`, `NegDiscount.isOrderStable` |
| Lemma 8.3.4, Ex 8.3.2, p. 280 | The min-greedy policy lies in `Σ` | `NegDiscount.InV0`, `NegDiscount.g`, `NegDiscount.unique_min`, `NegDiscount.greedyFun_monotoneOn`, `NegDiscount.greedyFun_effort`, `NegDiscount.greedyFun_eq_zero_iff`, `NegDiscount.greedy`, `NegDiscount.lemma_8_3_4`, `NegDiscount.exercise_8_3_2` |
| Lemma 8.3.5, Ex 8.3.3, p. 280 | `T` maps `V₀` into itself; `Tᵏv = v̄` for `k ≥ k₀` | `NegDiscount.V0`, `NegDiscount.T_greedy_mem`, `NegDiscount.bellman`, `NegDiscount.bellman_iterate_agree`, `NegDiscount.lemma_8_3_5`, `NegDiscount.exercise_8_3_3` |
| Thm 8.3.6, p. 280 | Fundamental min-optimality; `v̄ = v▿*`; the optimal policy is unique | `NegDiscount.theorem_8_3_6` |

## §8.3.2 Optimal harvests (pp. 281–284)

| Book | Claim | Lean |
| --- | --- | --- |
| §8.3.2.1, (8.56)–(8.57) | The model, `r` and `f` | `Harvest`, `Harvest.f`, `Harvest.r` |
| §8.3.2.2 | `F`, `G_σ` | `Harvest.F`, `Harvest.G`, `Harvest.G_apply`, `Harvest.harvestWhere`, `Harvest.fdp` |
| Ex 8.3.4, p. 283 | An order-preserving FDP whose primary ADP is the harvest ADP; `T̂_σ` | `Harvest.isOrderPreserving`, `Harvest.exercise_8_3_4` |
| p. 283 | Compute `ŵ*`, then an argmax policy is optimal (Theorem 5.2.13) | `Harvest.primary_contraction`, `Harvest.G_eq_Gsup_iff`, `Harvest.section_8_3_2_2` |

## §8.3.3 Euler equation methods (pp. 284–290)

| Book | Claim | Lean |
| --- | --- | --- |
| (8.58)–(8.59), Assumption 8.3.1 | The growth model | `Growth`, `Growth.Γ`, `Growth.cont`, `Growth.B`, `Growth.brdp`, `Growth.isBlackwell`, `Growth.hasMaxSelections` |
| Ex 8.3.5, p. 285 | `u'(c) → 0` | `Growth.exercise_8_3_5` |
| Ex 8.3.6, p. 285 | Continuity of `B` (corrected: `v ∈ bcX`); false for `v ∈ bX` | `Growth.exercise_8_3_6`, `Growth.indPos`, `Growth.exercise_8_3_6_false`, `Growth.not_regular` |
| Prop 8.3.7, Ex 8.3.7, p. 285 | Fundamental optimality, `v* ∈ bcX`, VFI | `Growth.proposition_8_3_7` |
| Lemma 8.3.8, Ex 8.3.8, p. 286 | `v*` increasing, concave, continuous; unique optimal policy | `Growth.ICC`, `Growth.isClosed_ICC`, `Growth.cont_concave`, `Growth.B_concave`, `Growth.bellman_mem_ICC`, `Growth.strictConcaveOn_B`, `Growth.lemma_8_3_8`, `Growth.exercise_8_3_8` |
| Prop 8.3.9, (8.60), p. 286 | Envelope condition for `Tv` (corrected) | `hasDerivAt_of_concave_sandwich`, `Growth.argmax_pos`, `Growth.proposition_8_3_9`, `Growth.proposition_8_3_9_not_interior` |
| Cor 8.3.10, (8.61), p. 286 | Envelope condition for `v*` | `Growth.corollary_8_3_10` |
| (8.62)–(8.63), `Σ𝒞` | The Euler equation | `Growth.SigmaC`, `Growth.eulerIntegrand`, `Growth.SolvesEuler`, `Growth.SatisfiesEuler` |
| Ex 8.3.9, p. 287 | The sequential Euler equation | `Growth.exercise_8_3_9` |
| `K`, p. 287 | The Coleman–Reffett operator: uniqueness of `Kσ(y)` | `Growth.eulerIntegrand_mono`, `Growth.solvesEuler_unique` |
| Ex 8.3.10, p. 288 | `K` is order preserving | `Growth.exercise_8_3_10` |
| Ex 8.3.12, p. 293 | `K_b σ ≤ K_a σ` for `β_a ≤ β_b` (the comparison step) | `Growth.exercise_8_3_12_step` |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Ex 8.1.8, §8.1.3.2, Figures 8.1–8.12 | Numerical work | Numerical. |
| §8.3.2.3 | The converse implication | A discussion; Proposition 5.2.14 is restated in `FactoredDP`. |
| Existence of `Kσ(y)`, p. 288 | The Euler equation has a solution in `(0, y)` | The integral term need not be finite (`u'` is unbounded near `0`); see corrections. |
| §8.3.3.4–8.3.3.5 | Time iteration and the endogenous grid method | Algorithms; their convergence rests on Proposition 8.3.13. |
| Lemma 8.3.11, Props 8.3.12–8.3.13, Ex 8.3.11, Ex 8.3.12 (conclusion) | The conjugacy of `T` and `K` | Not established as printed; see corrections. |
| §8.4 | Chapter notes | Not mathematical claims. |
