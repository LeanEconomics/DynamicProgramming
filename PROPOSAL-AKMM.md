# Proposal: Azzimonti, Krusell, McKay and Mukoyama, *Macroeconomics*, in Lean

**Source.** Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama (with
Boppart, Corsetti, Dedola, Hassler, Hatchondo, Heathcote, Hornstein, Klenow, Lloyd, Martinez,
Mitman, Olovsson, Piazzesi, Quadrini, Ravn, Rogerson, Ríos-Rull, Şahin, Schneider, Storesletten
and Violante), *Macroeconomics — away from complete*, draft of December 2025: 909 pages, 25
chapters in three parts (I Foundations, Ch 1–8; II Tools, Ch 9–10; III Applications, Ch 11–25),
chapter appendices 3.A–24.A. The PDF in `~/Dropbox/Papers_and_Textbooks/Various Textbooks/`
has a text layer (the filename spells the first author "Azimotti"). Citations give the draft's
section, equation number and page. Nothing from the book is reproduced in the repository.

**Character.** This is a graduate textbook built around derivations, not theorems: about 21
numbered results in the whole book (Proposition 4.4, Theorems 6.1–6.2, the equilibrium
definitions of Chapter 5 and Definition 16 in 7.A, Definition 15.1, Assumptions and Proposition 19.x, the Uzawa theorems and two
appendix theorems on balanced growth and dynamic efficiency) and **no exercises**. Like Miao's
Chapters 14 and 18, its mathematical content is in the derivations: first-order conditions,
equilibrium definitions and their equivalences, steady states, closed forms, log-linear systems,
comparative statics, welfare comparisons. The proposal formalises those, and lists empirical,
narrative and numerical material as not formalised.

**Surveys.** Four survey agents read every chapter and appendix (2026-11-11). Their notes —
section tables, formalisable inventories with reuse tags, obstacles and printed errors with the
checks behind them — are in `notes/survey_chNN.md`, with `notes/summary.tsv` and the check
scripts in `notes/scratch/`. Estimated **≈1,000 new theorems** across 24 chapter projects, and
**≈140 printed errors** found (about 100 substantive), each checked by hand algebra, a numeric
script or a rendered PDF page.

**Target.** `LeanEconomics/DynamicProgramming`, in a top-level folder `AKMM/` alongside the Miao
(`EconomicDynamics/`), Stokey–Lucas–Prescott, Sargent–Stachurski and Meyn–Tweedie projects.

Status: decisions settled 2026-11-11 (§4); Phase 0 scaffold and Chapters 2–17 done 2026-11-12.

---

## 1. Layout and conventions

Same conventions as the Miao, Galí–Woodford and Obstfeld–Rogoff programmes:

- **One independent Lean 4 / Mathlib v4.34.0 project per chapter**, built one chapter at a time,
  each with a README library map, `docs/source-map.md`, `docs/corrections.md`,
  `proof-manifest.json` and the `scripts/verify.py` audit (build, fresh concatenated
  elaboration, axiom audit allowing only `propext`, `Classical.choice`, `Quot.sound`); a CI
  matrix entry; a row in the root README.
- **Folder and namespace** `AKMM/<Project>` and `AKMM.<Project>`.
- **Docstrings** cite the book: `/-- AKMM, (4.17), p. 101: ... -/`; every numbered result, every
  numbered equation the text derives and every precise claim it makes appears in the source map,
  formalised or listed with a reason.
- **What is formalised.** Every derivation the text carries out, stated in the book's setting
  and proved: equilibrium conditions, the equivalence of equilibrium concepts and of
  decentralisations with planner problems, existence/uniqueness/formulas of steady states,
  closed-form solutions, log-linear systems (as exact derivatives along paths through the steady
  state, the Galí/Obstfeld–Rogoff pattern), comparative statics with explicit sign hypotheses,
  welfare statements. Data, stylised facts, figures, calibrated numbers, Dynare/Matlab code and
  simulations are listed as not formalised; claims that rest only on figures are omitted in the
  first pass and listed as deferred (decision 7).
- **Corrections.** Where the book is false or imprecise as printed, the corrected statement is
  proved, with a Lean counterexample to the printed one when it is false. The surveys already
  record ≈140 such points (§3).
- **Non-vacuity.** No Prop-valued hypothesis structure without a proved concrete instance; a
  result the book cites but does not prove may enter as a hypothesis only with a proved instance
  where it holds (the Miao rule).
- **Dependencies, not copies.** A chapter project uses existing material by depending on it: a
  Lake `require` with a `path` for projects in this repository (e.g. Miao `EconomicDynamics/*`,
  SLP `RecursiveMethods/*`, earlier `AKMM/*` chapters) and a `git` require pinned to a commit for
  the other LeanEconomics repositories (EconomicGrowth, InternationalEconomics,
  MonetaryEconomics). Only the chapter's own modules are listed in its `proof-manifest.json` and
  audited; imported modules from dependencies are treated as library imports by `verify.py`.
  All dependencies must pin the same Mathlib (v4.34.0).
- **Branches** `akmm-chN-<name>`, stacked in book order; committed only after `verify.py`
  passes; never pushed by the assistant.
- **Worktree and build cache.** The programme runs in its own worktree of DynamicProgramming
  under `~/.cache/lean-builds/worktrees/`, cut from `origin/main`; builds in
  `~/.cache/lean-builds/`, `packages/` symlinked to the shared Mathlib.

---

## 2. Chapter projects

"Reuse" names the closest existing material (abbreviations: **DP** = LeanEconomics/
DynamicProgramming, with Miao `EconomicDynamics/*`, SLP `RecursiveMethods/*`, Sargent–Stachurski
(SS) `FiniteStates/*`, `GeneralStates/*`, Meyn–Tweedie; **EG** = EconomicGrowth; **IE** =
InternationalEconomics (Obstfeld–Rogoff); **ME** = MonetaryEconomics (Galí, Woodford, Cochrane
tracks); **LE** = the LeanEconomics research repository). Theorem counts are survey estimates of
new theorems, excluding material used from dependencies.

| Ch | Project | Content to formalise | Est. | Difficulty | Reuse | Main obstacle |
| ---: | --- | --- | ---: | --- | --- | --- |
| 1 | — | Narrative history of macroeconomics; no formal content | 0 | — | — | none: no project |
| 2 | `Framework` | Growth accounting, the detrended dynamic system, input shares, KPR/Boppart–Krusell preferences consistent with balanced growth | 15 | low | EG SolowSwan DiscreteTime | "only if" halves of the preference characterisations (not proved in the book) |
| 3 | `Solow` | Steady state, dynamics, balanced growth, convergence speed, impulse responses; App 3.A Uzawa theorems | 30 | low | EG SolowSwan DiscreteTime, Uzawa | discrete-time Uzawa (EG's is continuous) |
| 4 | `DynamicOptimization` | Finite/infinite-horizon sequential problems, Euler and transversality, Prop 4.4, Bellman equation, value-function properties, functional Euler equation, NGM dynamics; App 4.A | 60 | medium | DP SLP DeterministicDP (Thm 4.15 = Prop 4.4), DeterministicDynamics, Extensions/EulerTransversality | no Kuhn–Tucker in Mathlib (use concavity sufficiency); saddle-path existence (stable manifold, reusable from SLP Ch 6) |
| 5 | `CompetitiveEquilibrium` | Arrow–Debreu, sequential and recursive equilibrium (endowment, labour, NGM), their equivalence, steady state and dynamics, OLG economies; App 5.A aggregation | 45 | medium | DP Miao CompleteMarkets, OverlappingGenerations; SLP EquilibriumApplications | continuum of agents (measurable choices, integrals) |
| 6 | `Welfare` | First Welfare Theorem (Thm 6.1), Pareto frontier/Negishi, inefficiencies (taxes, externalities, borrowing constraints, commitment, market power), OLG efficiency (Thm 6.2, dynamic inefficiency), optimal policy | 45 | medium–high | DP SLP ParetoOptimaEquilibria, Miao CompleteMarkets, OverlappingGenerations | general Balasko–Shell/Cass criterion (cited, not proved; decision 5) |
| 7 | `Uncertainty` | Markov chains, AR processes, linear stochastic difference equations, expected utility and portfolio choice, the stochastic growth model (sequential, recursive, linearised), competitive trade under uncertainty, an incomplete-markets economy; App 7.A | 40 | medium | DP Miao RationalExpectations, MarkovProcesses, CompleteMarkets, Applications; SLP StochasticDP; IE InternationalFinancialMarkets | infinite event trees; MA(∞) of AR(1) in L² |
| 8 | `QuantitativeMethods` | Identification algebra, SVAR/Cholesky, VARs vs local projections, the fiscal-policy model and its multiplier, likelihood, calibration identities; App 8.A | 30 | low–medium | DP Miao PartialInformation (Kalman), StructuralEstimation, NeoclassicalGrowth | multivariate Gaussian conditioning; Cholesky uniqueness |
| 9 | `ContinuousTime` | Continuous-time tools, the maximum principle, continuous-time Solow and NGM (saddle path, decentralisation), Poisson uncertainty; App 9.A | 35 | medium | EG Solow1956, RamseyCassKoopmans; DP Extensions/EulerTransversality, SS ContinuousTime | no Pontryagin in Mathlib (prove Mangasarian/Arrow sufficiency; decision 6); no Poisson process |
| 10 | `ComputationalTools` | The theorems behind interpolation, bisection and Newton convergence, golden-section search, Tauchen and Rouwenhorst (moment identities), value-function iteration, linearisation and Blanchard–Kahn | 35 | low–medium | DP Miao NumericalMethods, DifferenceEquations; Bellman contraction; LE Bisection | Rouwenhorst binomial invariant law; Newton convergence |
| 11 | `Consumption` | Autarky and full insurance, risk-sharing tests' algebra, partial insurance, income fluctuation problems (deterministic, PIH, borrowing constraints, precautionary saving, wealth bounds), Huggett and Aiyagari economies | 52 | medium–high | LE Aiyagari/Huggett, IncomeFluctuationCarrollKimball; DP Miao IncompleteMarkets, Applications | mean-preserving spreads (Rothschild–Stiglitz); continuity of the stationary distribution in r |
| 12 | `LaborSupply` | Static and dynamic labour supply, Frisch/Marshall/Hicks elasticities, balanced-growth preferences, taxation across countries, indivisible labour and lotteries, intensive/extensive margins; App 12.A | 50 | low–medium | DP Miao NeoclassicalGrowth (KPR/GHH/indivisible labour) | balanced-growth "only if" (functional equation); continuous-time bang-bang results |
| 13 | `Growth` | Investment-specific technical change (BGP, planner, transitional dynamics), endogenous growth with expanding varieties and quality ladders; App 13.A | 62 | medium | IE GlobalGrowth (AK, Romer); EG RamseyCassKoopmans, Uzawa, golden rule | continuous-time optimality without Pontryagin; Poisson quality ladders with a continuum law of large numbers |
| 14 | `RealBusinessCycles` | HP and band-pass filters as matrix/linear-algebra facts, the simple and core RBC models, extensions (indivisible labour, adjustment costs, utilisation), business-cycle accounting wedges; App 14.A | 45 | low–medium | DP Miao NeoclassicalGrowth | spectral analysis of stationary processes (not in Mathlib; decision 5) |
| 15 | `FiscalPolicy` | Distortionary taxes in the long run, incidence, tax reform, the Laffer curve, theories of G, Ricardian equivalence, Ramsey taxation (primal approach, time consistency), OLG debt and pensions, redistribution; App 15.A | 70 | low–medium | IE LifeCycleFiscalPolicy; DP Miao NeoclassicalGrowth; ME Cochrane FiscalConstraints | figure-read monotonicity/convexity claims; unstated Ramsey sign conditions |
| 16 | `AssetPrices` | The stochastic endowment economy, two-period and dynamic asset trading, no-arbitrage and state prices, spanning, the lognormal model, the equity-premium and excess-volatility puzzles | 55 | medium | DP Miao CompleteMarkets, RecursiveUtility; SS StochasticDiscounting; IE InternationalFinancialMarkets | existence of an optimal portfolio under no-arbitrage; infinite-tree equivalence |
| 17 | `Money` | Money in OLG and dynastic models, the Friedman rule, fiscal theory of the price level, multiple currencies (Kareken–Wallace), missing assets, money as a medium of exchange | 85 | medium | DP Miao OverlappingGenerations, IncompleteMarkets; ME Galí Ch 2, Cochrane FTPL/Monetarism | global classification of nonlinear equilibrium difference equations; Kiyotaki–Wright only verbal |
| 18 | `NominalFrictions` | Calvo pricing and the New Keynesian model, the Phillips curve, monetary policy strategies and the Taylor principle, sticky wages; App 18.A | 30 | low (with reuse) | ME Galí Ch 3–6; DP Miao NewKeynesian | little; the IV orthogonality argument and sticky-wage variant are new |
| 19 | `CreditFrictions` | Financial frictions in firm and household problems, Assumptions 19.4.x, Proposition 19.1 (Modigliani–Miller indeterminacy), the two-period and general models; App 19.A | 40 | medium | DP Miao NeoclassicalGrowth, SLP EquilibriaWithDistortions; IE CapitalMarketImperfections | Properties 19.5.x are heuristic: restate as signed comparative statics (implicit function theorem with explicit Jacobian-sign hypotheses) |
| 20 | `FrictionalLaborMarkets` | A simple unemployment model, the DMP model, the unemployment-volatility puzzle algebra, endogenous separations, DMP in the growth model, frictional wage dispersion; App 20.A (Nash bargaining, Hosios) | 45 | medium | DP Miao SearchAndMatching; SS lake model, McCall | Hosios only via first-order conditions (non-convex planner) |
| 21 | `Inequality` | Inequality in growth and incomplete-markets models, income processes, Pareto tails, reasons inequality matters for aggregates | 25 | low–medium | LE/Miao IncompleteMarkets; EG SolowSwan; IE LifeCycleFiscalPolicy (Barro) | Kesten–Goldie Pareto tails need implicit renewal theory (decision 5) |
| 22 | `HeterogeneousFirms` | A simple model, reallocation and misallocation (Hsieh–Klenow algebra), Hopenhayn-type general equilibrium, alternative market arrangements, business cycles, endogenous productivity; Hulten's theorem; App 22.A | 35 | medium | SS envelope (Clausen–Strub), Hopenhayn–Prescott; SLP welfare theorems; IE CES duality | Gabaix granularity needs stable-law convergence (decision 5) |
| 23 | `InternationalMacro` | The workhorse open-economy model (endowment and production), risk sharing, the real exchange rate, substitution and wealth effects, Backus–Kehoe–Kydland-type log-linear results | 35 | low–medium | IE InternationalFinancialMarkets, RealExchangeRate, StickyPriceModels, IntertemporalTrade | log-linear results as exact implicit-function derivatives at the symmetric steady state |
| 24 | `SovereignDefault` | The two-period default model in full; the quantitative Eaton–Gersovitz/Arellano model's Bellman equations and the properties the text derives; App 24.A | 20 | medium | IE CapitalMarketImperfections; DP contraction/Blackwell, Miao DynamicGames (MPE) | existence/uniqueness of the infinite-horizon Markov perfect equilibrium (decision 5) |
| 25 | `Sustainability` | Carbon cycle and the carbon budget as linear systems, damages, the static and dynamic integrated assessment models (GHKT optimal carbon tax), finite resources (Hotelling, capital–energy complementarity) | 30 | medium | SLP DeterministicApplications (cake eating), SS natural resources, EG RCK, Miao DifferenceEquations | the GHKT formula as a planner theorem with a carbon stock; empirical climate relations are not derivable |
| | | **Total** | **≈1,014** | | | |

Appendices 3.A–24.A go with their chapters.

---

## 3. What the surveys found in the text

About **140 printed errors**, roughly 100 substantive, with the check behind each in the
chapter surveys. A selection:

- **Ch 3:** the calibration experiment on p. 88 (doubling s raises output by 41%, not 17%; the
  printed number uses the wrong exponent); the closed form for ŷ_t on p. 92 has a stray δ; the
  Uzawa growth rates in 3.A.
- **Ch 4:** "the policy is strictly increasing" needs F₁₂ > 0; Proposition 4.4 omits
  hypotheses its proof uses; missing β in the delayed-depreciation Bellman equation; the
  (1−δ)k term dropped in (4.28).
- **Ch 6:** "optimal iff the limit net rate ≥ 0" is false at 0 (p_t = (t+1)² is a
  counterexample); the storage bond price is 1/χ, not χ.
- **Ch 7:** the convergence condition for Markov chains on p. 190 is neither necessary nor, as
  worded, sufficient (the book's own flip matrix); the aperiodicity definition is far too strong.
- **Ch 10:** the Rouwenhorst recursion has its weights swapped (the printed recursion gives
  autocorrelation 0.149 instead of 0.9); (10.17) is missing α (the book's own numbers come from
  the corrected formula).
- **Ch 11:** the CRRA return-risk claim needs relative prudence ≥ 2; (11.41)'s variance
  coefficient is σ/2, not (σ+1)/2; the log-utility MPC is 1−β.
- **Ch 12–13:** several sign and exponent slips in elasticities and in the growth appendix
  (13.A.10's Hamiltonian discounts with e^{+ρt}).
- **Ch 14:** the HP filter's first-order condition has the wrong sign.
- **Ch 16–17:** (16.17) misstates the covariance pricing identity; inflation equals money
  growth, not its inverse (p. 514); (17.40)'s indeterminacy region is a bounded interval.
- **Ch 18:** the natural rate below (18.15) has the wrong sign; the duration weights sum to θ.
- **Ch 20, 24, 25:** a wrong-signed B in (20.25) and a spurious β in 20.A; a missing minus
  sign in (24.13); carbon-cycle signs in (25.6)/(25.8) that break conservation of carbon.

Many of these are typos in a draft. They will be proved in corrected form and recorded in each
project's `docs/corrections.md` as the chapters are done (decision 8 on reporting them).

---

## 4. Decisions (settled by the user, 2026-11-11)

1. **Repository:** inside `LeanEconomics/DynamicProgramming`.
2. **Folder and namespace:** `AKMM/<Project>` and `AKMM.<Project>`.
3. **Depend, not copy:** projects depend on existing projects through Lake requires (`path`
   within this repository, `git` pinned to a commit for other LeanEconomics repositories)
   instead of copying their material. Phase 0 checks that `verify.py` treats dependency
   modules as library imports, that CI builds the dependencies, and that the shared Mathlib
   build cache is reused.
4. **Order:** book order, Chapter 2 first (Chapter 1 has no project).
5. **Beyond-the-text results** (general Balasko–Shell/Cass, spectral analysis of stationary
   processes, Kesten–Goldie tails, Gabaix granularity, existence/uniqueness of the
   infinite-horizon default equilibrium, Achdou et al. uniqueness): listed as not formalised in
   the first pass. Once all chapters are done, ask the user whether to attempt them.
6. **Continuous time:** follow the textbook. Where the book works in continuous time (Ch 9, the
   continuous-time parts of Ch 12–13), the results are formalised in continuous time as the book
   states them; where the book offers a choice or the setting is open, discrete time is
   preferred. For the maximum principle: sufficiency (Mangasarian/Arrow) and the specific
   Hamiltonian conditions the text uses are proved; the necessity direction is listed as not
   formalised; EconomicGrowth's Ramsey–Cass–Koopmans saddle-path work is reused.
7. **Chapter 8 and figure-read claims:** the algebra is formalised and the empirical method
   discussion listed. Claims that rest only on figures are omitted in the first pass (each
   listed in the source map as "figure claim, deferred"); whether to do them is decided after
   the book is finished, together with decision 5.
8. **The errors:** recorded in each project's `docs/corrections.md`; whether to send anything to
   the authors stays with the user, and nothing is sent by the assistant.
9. **Citations:** the December 2025 draft's pages.

---

## 5. Plan

Phase 0: create the `AKMM/` folder in a new DynamicProgramming worktree, its conventions, the
CI matrix entry and an empty verified project with one path dependency and one git dependency
(to test the dependency setup in `verify.py`, CI and the build cache), on branch `akmm-scaffold`. Then one chapter at a time: a base project with its dependencies declared, a common
brief, two or three section agents per chapter in separate scratch projects, a merge with
clash checks and pruning, merged docs, verification in the real project, a commit on a stacked
branch, and the README row and proposal status updated. Estimated scale: about 1,000 new
theorems by the surveys' count; the Miao chapters came out at several hundred new theorems each,
so this is likely an underestimate. Chapters 4, 11, 13, 15 and 17 are the largest.
