# Proposal: Meyn and Tweedie, *Markov Chains and Stochastic Stability*, in Lean

**Source.** Sean Meyn and Richard L. Tweedie, *Markov Chains and Stochastic Stability*, second
edition, Cambridge University Press, 2009, with a prologue by Peter W. Glynn and an epilogue by
Meyn. There are 20 chapters in three parts (Communication and regeneration; Stability
structures; Convergence) and appendices A–D, about 600 pages. The PDF is
`~/Dropbox/Papers_and_Textbooks/Various Textbooks/Meyn & Tweedie - Markov_Chains_and_Stochastic_Stability (2nd Ed).pdf`
(624 PDF pages). Unlike the SLP scan it has a text layer: `pdftotext -layout` extracts are kept
only in the session scratchpad. Nothing from the book is reproduced in the repository; statements
are restated, with page references.

**Size.** There are about 400 numbered results: 198 theorems, 166 propositions and 32 lemmas,
numbered `Theorem 13.0.1` and so on. Almost all are proved in the text. The book has no
exercises. A few proofs are left to the reader ("we omit the proof", twice) or cited
(Billingsley, for the martingale functional CLT). The size is comparable to SLP Chapters 7–14
together, but denser.

**Why here.** The book is the standard reference for the stability theory that this repository
already uses piecemeal. SLP Chapters 8 and 11–14 (`MarkovProcesses`, `StrongConvergence`,
`WeakConvergence`, `ConvergenceApplications`, `LawsOfLargeNumbers`) build kernels, total
variation, Doeblin's condition, the Feller property, tightness and Prokhorov, the Ionescu-Tulcea
path measure with the Markov property, and a strong law for Markov chains.
`Extensions/StationaryDistributions` proves the existence and uniqueness of stationary
distributions for monotone economies. The `GeneralStates` projects (Sargent and Stachurski) work
with general-state transition kernels. Meyn and Tweedie supplies what these lack: ψ-irreducibility,
small and petite sets, Nummelin splitting, Harris recurrence, Foster–Lyapunov drift criteria, and
the f-, geometric and V-uniform ergodic theorems. These are the tools behind stability results for
the policy-induced chains of dynamic programs (Bewley–Huggett–Aiyagari stationary distributions,
the VFI Toolkit's agent distributions).

**Target.** This repository, `LeanEconomics/DynamicProgramming`, with the same conventions as
`PROPOSAL-SargentStachurski.md` §1–2 and `PROPOSAL-StokeyLucasPrescott.md` §1:
- one independent Lean/Mathlib project per chapter, built one chapter at a time;
- each project with a README library map, `docs/source-map.md`, `docs/corrections.md`,
  `proof-manifest.json` and the `scripts/verify.py` audit;
- a CI matrix entry and a row in the root README.

Status: draft for discussion, 2026-10-21. Nothing is built yet.

---

## 1. Layout and conventions

```
DynamicProgramming/
└── StochasticStability/          one project per chapter, Chapters 1–20
```

- **Folder** `StochasticStability/`, with projects named after the chapter's subject.
- **Namespace** `MeynTweedie.<Project>`.
- **Citations** in docstrings as `MT, Thm 13.0.1, p. 313`, and every cited result appears in
  `docs/source-map.md` with its page.
- **Chapters 1–2** (heuristics and the model zoo) become one project, `MarkovModels`. It defines
  the book's running models as kernels, so later chapters can prove their stability results about
  them:
  - random walks on ℝ and ℝ₊;
  - the linear, nonlinear and bilinear state space models;
  - AR, SETAR and SAC models;
  - the GI/G/1 queue and the storage model.
  
  The two theorems of §1.3 are previews, proved in the chapters that state them in full.
- **Re-prove everything** from the book, in the book's setting. Copying from the earlier projects
  in this repository is allowed (each project stays self-contained), as it was for SLP; nothing is
  imported from the older `EconomicsInLean` library.
- **Appendices.**
  - A (mud maps) summarises the theorems; its arrows are cross-referenced in the source maps.
  - B.2 (the complete stability classification of the scalar SETAR model) is formalised, in the
    project for the chapter whose criteria it uses.
  - C (the glossary of model assumptions) goes into `MarkovModels`.
  - D (background) is proved or matched to Mathlib where it is used.
- **Corrections.** Where a claim is false or imprecise as printed, the corrected statement is
  proved, with a Lean counterexample where possible, and recorded in `docs/corrections.md`.
- **Branches** `mt-chN-<name>`, stacked in book order on the tip of `slp-gaps`. Each is committed
  only after `scripts/verify.py` passes, and never pushed by the assistant.

---

## 2. Chapter projects

The counts are numbered results found in the text; the source maps account for each.

| Ch | Project | Content | Results | Infrastructure and risks |
| ---: | --- | --- | ---: | --- |
| 1–2 | `MarkovModels` | The running models as transition kernels; regeneration structure of queues and storage models; Appendix C | 2 | Definitions; Mathlib `Kernel` |
| 3 | `TransitionProbabilities` | Countable and general state spaces, `Pⁿ`, the path measure, the strong Markov property, hitting and return times, kernels for the specific models | 10 | **Strong Markov property** for stopping times on `Kernel.traj`: only the simple Markov property exists (Ch 14 of SLP); must be built |
| 4 | `Irreducibility` | Communication on countable spaces; ψ-irreducibility and the maximal irreducibility measure; random walk and linear models | 13 | Maximal irreducibility measure via resolvent `K_a` |
| 5 | `PseudoAtoms` | Nummelin splitting, small sets, cyclic behaviour and period, petite sets and sampled chains | 24 | **Splitting** on `X × {0, 1}`: new kernels and their path measures |
| 6 | `TopologyContinuity` | Feller and strong Feller chains, T-chains, continuous components, e-chains | 28 | Weak Feller / tightness from SLP Ch 12 |
| 7 | `NonlinearStateSpace` | Forward accessibility, rank conditions and continuous components, minimal sets, periodicity, equicontinuity | 23 | Implicit function theorem (Mathlib) and Sard-type measure-zero results (`MeasureTheory/Function/Jacobian`); control-theoretic rank conditions |
| 8 | `TransienceRecurrence` | Classification on countable spaces and for ψ-irreducible chains; drift criteria for recurrence and transience; random walk on ℝ₊ | 32 | |
| 9 | `HarrisRecurrence` | Harris recurrence, non-evanescence, topological recurrence, stochastic comparison and increment analysis | 29 | Martingale convergence (Mathlib) |
| 10 | `InvariantMeasures` | Existence of π: chains with atoms (Kac), countable spaces, ψ-irreducible chains via splitting, general models | 22 | |
| 11 | `DriftRegularity` | Regular chains, drift and hitting times, Foster–Lyapunov criteria for regularity, non-positivity | 31 | Comparison theorem (Dynkin's formula) |
| 12 | `InvarianceTightness` | Boundedness in probability, generalized sampling, σ-finite invariant measures, e-chains | 19 | Prokhorov from SLP Ch 12 |
| 13 | `Ergodicity` | Aperiodic ergodic theorem: countable spaces, renewal and regeneration, positive Harris chains | 18 | **Renewal theory** is not in Mathlib: Erdős–Feller–Pollard for aperiodic renewal sequences, coupling |
| 14 | `FErgodicity` | f-norms, f-regularity and drift, f-ergodicity, the key renewal theorem | 31 | |
| 15 | `GeometricErgodicity` | Kendall sets and Kendall's renewal theorem, geometric drift, skeletons, random walk and linear models | 25 | Generating functions of renewal sequences |
| 16 | `VUniformErgodicity` | Operator-norm convergence in the V-weighted norm, uniform ergodicity (Doeblin), increment analysis, queues, AR and state space models | 21 | Weighted operator norms on bounded-by-V functions; SLP Ch 11 Doeblin |
| 17 | `LimitTheorems` | Invariant σ-fields and the LLN, ergodic theorems via atoms and splitting, Poisson's equation, the CLT, the functional CLT, the LIL | 30 | LLN and CLT reduce to i.i.d. blocks: Mathlib's strong law and `CentralLimitTheorem` (i.i.d.). **Functional CLT and LIL**: they need the martingale functional CLT (Thm D.6.4), Brownian motion with continuous paths (Mathlib has only `IsPreBrownianReal`) and weak convergence in `C[0, 1]`, plus a martingale LIL. **Largest risk**; see §3 |
| 18 | `Positivity` | Null recurrence, positivity via `Pⁿ`, T-chains and e-chains, the LLN for e-chains | 16 | |
| 19 | `GeneralizedDrift` | State-dependent and history-dependent drift, mixed drift conditions; Appendix B.2 (SETAR) | 15 | |
| 20 | `Epilogue` | Geometric ergodicity and spectral theory, simulation and MCMC, continuous time (resolvent equations, the exponential ergodic theorem) | 7 | Only the results proved in the text; the survey material is listed as not formalised |

---

## 3. Decisions to make

1. **The functional CLT and the LIL (§§17.4–17.5).** I recommend proving everything else in
   Chapter 17 first: the LLN, the CLT via atoms and splitting, and Poisson's equation, all on
   Mathlib's i.i.d. theorems and a martingale CLT built here. Then decide, as for Brouwer and
   Schauder in SLP Chapter 17, whether to build Brownian motion on `C[0, 1]` and the martingale
   invariance principle, or to state Theorem D.6.4 as a named hypothesis of the functional
   results.
2. **Folder and namespace.** `StochasticStability/` and `MeynTweedie`, as above.
   `MarkovChains/` is the alternative.
3. **Order.** Book order. Chapters 3, 5 and 13 carry the new infrastructure (the strong Markov
   property, splitting and renewal theory); the rest of the book rests on them.
