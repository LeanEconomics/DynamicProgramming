# Proposal: Stokey, Lucas and Prescott, *Recursive Methods in Economic Dynamics*, in Lean

**Source.** Nancy L. Stokey and Robert E. Lucas, Jr., with Edward C. Prescott, *Recursive
Methods in Economic Dynamics*, Harvard University Press, 1989 (fifth printing 1999): 18
chapters in four parts, 588 pages. The PDF and the companion *Solutions Manual* (Irigoyen,
Rossi-Hansberg and Wright, 2002) are in `~/Dropbox/Papers_and_Textbooks/Various Textbooks/`.
The book PDF is a scan with no text layer: two book pages per PDF page, book page `p` on PDF
page `⌊p/2⌋ + 9`. It is read page by page; nothing from it is reproduced in the repository.

**Target.** This repository, `LeanEconomics/DynamicProgramming`, alongside the Sargent and
Stachurski projects. Same conventions as `PROPOSAL-SargentStachurski.md` §1–2: one
independent Lean/Mathlib project per chapter, built one chapter at a time, each with a
README library map, `docs/source-map.md`, `docs/corrections.md`, `proof-manifest.json` and
the `scripts/verify.py` audit; a CI matrix entry; a row in the root README.

Status: started 2026-10-14 with Chapter 2; Chapters 3–6 done 2026-10-14; Chapters 7–9 done 2026-10-15; Chapters 10–13 done 2026-10-16.

---

## 1. Layout and conventions

```
DynamicProgramming/
└── RecursiveMethods/             one project per chapter, Chapters 2–18
```

- **Folder** `RecursiveMethods/`; projects named after the chapter's subject.
- **Namespace** `StokeyLucasPrescott.<Project>`.
- **Citations** in docstrings as `SLP, Thm 4.6, p. 79`, `SLP, Ex 2.3, p. 14`; every cited
  result appears in `docs/source-map.md` with its page.
- **Chapter 1** (Introduction) has no formal content and gets no project.
- **Re-prove everything** from the book, in the book's setting. Copying between my own
  projects in this repository is allowed (each project stays self-contained); nothing is
  imported from or copied out of the older `EconomicsInLean` library.
- **Exercises.** Every provable exercise is formalised. Exercises asking for a plot, a
  computation or an informal discussion are listed in the source map as not formalised. The
  *Solutions Manual* is a cross-check, not a source.
- **Corrections.** Where the book's claim is false or imprecise as printed, the corrected
  statement is proved and the change recorded in `docs/corrections.md`.
- **Branches** `slp-chN-<name>`, stacked in book order on the previous chapter; committed only
  after `scripts/verify.py` passes; never pushed by the assistant.

---

## 2. Chapter projects

| Ch | Project | Content | Infrastructure and risks |
| ---: | --- | --- | --- |
| 2 | `Overview` | Exercises 2.1–2.10: the neoclassical technology `f`, the log/Cobb–Douglas closed forms (finite horizon, Bellman equation, stochastic version, log-normal capital), the savings-rate dynamics, competitive equilibrium and the two welfare theorems for the finite-horizon growth economy | Finite-dimensional concave programming; Mathlib's Gaussian laws for Ex 2.7 |
| 3 | `MathematicalPreliminaries` | Metric and normed spaces, completeness of `C(X)`, the contraction mapping theorem and its corollaries, Blackwell's sufficient conditions, correspondences and the Theorem of the Maximum | Berge's theorem is not in Mathlib: proved here |
| 4 | `DeterministicDP` | The principle of optimality (Thms 4.2–4.5), bounded returns (Thms 4.6–4.11), constant returns to scale, unbounded returns (Thm 4.14), Euler equations and transversality (Thm 4.15) | Sequence spaces of feasible plans |
| 5 | `DeterministicApplications` | The 17 applications of Chapter 5 | Copies of Ch 3–4 machinery |
| 6 | `DeterministicDynamics` | One-dimensional dynamics, Liapounov functions, linear systems and the stable manifold, linear approximation, Euler-equation dynamics | The stable manifold theorem (Thm 6.9) is a candidate for a stated hypothesis |
| 7 | `MeasureIntegration` | Chapter 7's definitions and theorems, each proved or matched to Mathlib (Carathéodory, monotone convergence, Fatou, dominated convergence, Fubini, the monotone class lemma, Radon–Nikodym, conditional expectation) | Mostly Mathlib bridging; the book's statements proved from Mathlib's |
| 8 | `MarkovProcesses` | Transition functions, the operators `T` and `T*`, measures on sequence spaces (Ionescu Tulcea), iterated integrals, stochastic difference equations | Mathlib's `Kernel`, `Kernel.trajMeasure` |
| 9 | `StochasticDP` | The stochastic principle of optimality, bounded returns, constant returns, unbounded returns, stochastic Euler equations, policy and transition functions | Measurable selection for policy functions |
| 10 | `StochasticApplications` | The 11 applications of Chapter 10 | |
| 11 | `StrongConvergence` | Finite Markov chains, total variation, Doeblin's condition and Thm 11.12, monotone mixing | |
| 12 | `WeakConvergence` | Weak convergence (Thm 12.3 portmanteau), distribution functions and Helly, the Feller property, monotone Markov processes (Thm 12.12, Hopenhayn–Prescott), dependence on parameters | Helly's selection theorem may need building |
| 13 | `ConvergenceApplications` | The 8 applications of Chapter 13 | |
| 14 | `LawsOfLargeNumbers` | Strong laws for Markov processes (Thm 14.7 and its corollaries) | Mathlib has the i.i.d. SLLN; the Markov-chain law needs building |
| 15 | `ParetoOptimaEquilibria` | Dual spaces, the two welfare theorems in normed spaces (Thms 15.3–15.4), `ℓ∞` and its dual, inner-product representation of prices (Thm 15.6) | Hahn–Banach is in Mathlib; the `ℓ∞` dual decomposition needs building |
| 16 | `EquilibriumApplications` | The 7 applications of Chapter 16 | |
| 17 | `FixedPointArguments` | The overlapping-generations model, contraction arguments, Brouwer, Schauder, monotone operators, partially observed shocks | **Brouwer and Schauder are not in Mathlib.** Either build Brouwer (via Sperner's lemma or a retraction argument) or state it as a named hypothesis; decided when the chapter is reached |
| 18 | `EquilibriaWithDistortions` | The indirect approach, the local and global first-order approaches | |

The theorem index on book pp. 574–578 lists every numbered result; each chapter's source map
accounts for every entry in it for that chapter.
