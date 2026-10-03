# Proposal: Sargent & Stachurski, *Dynamic Programming* Volumes 1 and 2, in Lean

**Source.** Thomas J. Sargent and John Stachurski, *Dynamic Programming*:
- Volume 1, *Finite States*, 10 chapters plus appendices A–C (425 pages; the
  PDF is dated 17 Aug 2026)
- Volume 2, *General States*, 9 chapters plus appendix A (461 pages; PDF dated
  9 Sep 2026)

Both PDFs are in
`~/Dropbox/Papers_and_Textbooks/Econ_Papers/Completed/Bewley-Huggett-Aiyagari/`.
Text extracts (`pdftotext -layout`) live only in the session scratchpad and are
regenerated as needed.

**Target.** `LeanEconomics/DynamicProgramming`, cloned to
`~/Dropbox/Matlab_Codes/MyProjects/LeanDynamicProgramming/DynamicProgramming/`.
It currently holds only the Apache 2.0 `LICENSE` (one commit on `main`). The
layout copies `LeanEconomics/InternationalEconomics`: one independent
Lean/Mathlib project per chapter, built one chapter at a time, each with a
precise statement of what is proved, a source map, a corrections file, and a
reproducible `scripts/verify.py` audit. GitHub Actions runs every project as a
matrix.

Status: draft for discussion, 2026-10-03. Nothing is built yet.

---

## 1. Repository layout

```
DynamicProgramming/
├── README.md                     index table: project | volume & chapter | checked results | start here
├── LICENSE                       Apache 2.0 (already present)
├── .gitignore                    **/.lake/  **/__pycache__/  *.pyc
├── .gitattributes                * text=auto eol=lf
├── .github/workflows/check.yml   matrix over all chapter projects
├── PROPOSAL-SargentStachurski.md this file
├── FiniteStates/                 Volume 1: 10 chapter projects, section 3
└── GeneralStates/                Volume 2:  9 chapter projects, section 3
```

The CI matrix entries are paths, `FiniteStates/JobSearch` and so on.

Each chapter folder copies `InternationalEconomics/IntertemporalTrade` exactly:

```
<Project>/
├── README.md                 statement, library map (module | theorems | contents), build
├── CONTRIBUTING.md
├── LICENSE                   Apache 2.0 (copy of the root file)
├── THIRD_PARTY_NOTICES.md    Mathlib (Apache 2.0); the book is cited, not reproduced
├── lakefile.toml             lean_lib "<Project>"; mathlib v4.34.0
├── lean-toolchain
├── lake-manifest.json
├── proof-manifest.json       library, modules, theorem_counts, scope, source
├── <Project>.lean            root import file
├── <Project>/                the modules
├── docs/
│   ├── source-map.md         book result / equation / claim  ->  Lean name, with page numbers
│   └── corrections.md        where the book's statement had to be changed, and why
├── scripts/
│   ├── verify.py             copied unchanged from InternationalEconomics
│   └── test_verify.py
└── verification/             FreshAudit.lean, verification.json (generated)
```

`.lake/` in each project is a symlink into `~/.cache/lean-builds/DynamicProgramming-<Volume>-<Project>`,
as in the two sibling repos, so Dropbox never sees build output.

### Cross-project code

Each project is self-contained. A lemma needed by more than one chapter is
copied into each project that uses it, never shared through a Lake path
dependency. This is the InternationalEconomics rule and it is what keeps every
project buildable and auditable on its own.

### Relation to the existing `LeanEconomics` library

`robertdkirkby/EconomicsInLean` already has a general-state dynamic programming
library (`LeanEconomics/DynamicProgramming/`: Blackwell, Bellman, Stochastic,
Weighted, Extended, three Optimality files, OrderedFixedPoints, Parametric; plus
`Topology/Berge*.lean`), about 4,200 lines and 230 theorems. Four of those
results were already taken from Sargent and Stachurski: Vol 1 Prop 2.2.7
(parametric monotonicity), Vol 1 Thm 7.1.3 (Du's concave-operator theorem),
the eventual-contraction lemma of Vol 1 Ch 6, and the Vol 2 Thm 9.1.3 error
bound, all in `OrderedFixedPoints.lean`; `Models/ColemanReffett.lean` does the
Vol 2 §8.3 conjugacy with a kink.

Treatment (decided 2026-10-03): every result is re-proved here from the book,
in the book's setting, without copying from or importing the older library.
The older files are a known-good reference for what is provable, nothing more.
Upstreaming chapter results back into `LeanEconomics` is out of scope here.

---

## 2. Conventions for all projects

1. **Finite states are `Fintype`.** Volume 1 fixes a finite set `X` and works in
   `ℝ^X`. In Lean this is `X → ℝ` with `[Fintype X] [Nonempty X]`, sup norm via
   Mathlib's `PiLp`/`BoundedContinuousFunction` or the `Pi` sup-norm instance,
   and the pointwise order. Matrices are `Matrix X X ℝ`. Distributions on `X` are
   `X → ℝ` with the simplex hypotheses stated, or Mathlib's `PMF X`.
2. **General states use Mathlib's spaces.** Volume 2 works in bounded functions
   `bX`, bounded continuous functions `X →ᵇ ℝ`, Banach spaces and partially
   ordered sets. These are Mathlib's `BoundedContinuousFunction`,
   `NormedAddCommGroup` + `CompleteSpace`, `PartialOrder`, `CompleteLattice`.
   Stochastic kernels are `ProbabilityTheory.Kernel` with `IsMarkovKernel`.
3. **Operators, not algorithms.** VFI, OPI and HPI are theorems about iterates
   of an operator (convergence, rate, finite termination of HPI). The book's
   Julia/Python code and its "Computation" sections are not formalised.
4. **Explicit hypotheses.** Every hypothesis the book leaves implicit becomes a
   named assumption: nonemptiness of feasible sets, boundedness of rewards,
   `β ∈ [0,1)`, irreducibility or primitivity where a strict Perron–Frobenius
   conclusion is used, measurability in Volume 2.
5. **Named theorems are proved, not cited, with three exceptions.** Deep
   results the book quotes without proof and that are neither in Mathlib nor
   reasonable to build here are stated as hypotheses or omitted and recorded in
   `corrections.md` as "not claimed": Hartman–Grobman (Vol 1 Thm 2.1.3),
   general stochastic-approximation convergence behind Q-learning (Vol 2 §9.2),
   and any measure-theoretic selection theorem the Volume 2 appendix invokes
   that Mathlib lacks. Perron–Frobenius is *not* an exception: see section 4.
6. **Exercises.** Every provable end-of-chapter and in-text exercise is
   formalised, as in InternationalEconomics. The two volumes have roughly 490
   exercises; many are one-lemma facts and are the cheapest theorems in the
   book. Exercises that ask for a computation or a plot are listed in the
   source map as "computational, not formalised".
7. **Apache 2.0 headers** on every Lean file, Mathlib's header linter on in
   `lake build`, `autoImplicit = false`.
8. **Namespace** `SargentStachurski.<Project>`, mirroring
   `ObstfeldRogoff.IntertemporalTrade`.
9. **Citations** in docstrings as `S&S I, Prop. 2.2.7, p. 62` and
   `S&S II, Thm. 4.1.3, p. 127`; every cited result appears in
   `docs/source-map.md`.
10. **Monotone comparative statics via order.** The book's recurring argument
    "the operator is order preserving and globally stable, so the fixed point
    moves monotonically with the parameter" is Prop 2.2.7. It is proved once in
    the Vol 1 Ch 2 project and copied wherever it is used.

---

## 3. Chapter projects

### 3.1 Index

Counts are of distinct labelled results (Theorem, Proposition, Lemma,
Corollary), labelled exercises and labelled examples in the PDF text. Pages
are book pages from the tables of contents. Volume 1 projects live under `FiniteStates/`, Volume 2 under `GeneralStates/`.

**Volume 1, Finite States**

| # | Project | Chapter | Pages | Results | Exercises | Examples |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| 1 | `JobSearch` | 1 Introduction: Bellman equations, stability and contractions, infinite-horizon job search | 1–41 | 5 | 35 | 8 |
| 2 | `OperatorsFixedPoints` | 2 Operators and Fixed Points: stability, order, matrices and operators | 42–80 | 18 | 60 | 16 |
| 3 | `MarkovDynamics` | 3 Markov Dynamics: foundations, conditional expectations, job search revisited | 81–104 | 4 | 26 | 0 |
| 4 | `OptimalStopping` | 4 Optimal Stopping | 105–127 | 5 | 16 | 6 |
| 5 | `MarkovDecisionProcesses` | 5 Markov Decision Processes: definition, applications, modified Bellman equations | 128–181 | 9 | 24 | 3 |
| 6 | `StochasticDiscounting` | 6 Stochastic Discounting: time-varying discount factors, state-dependent discounting, asset pricing | 182–212 | 10 | 18 | 6 |
| 7 | `NonlinearValuation` | 7 Nonlinear Valuation: beyond contractions, recursive preferences, general representations | 213–245 | 13 | 40 | 10 |
| 8 | `RecursiveDecisionProcesses` | 8 Recursive Decision Processes | 246–291 | 19 | 41 | 19 |
| 9 | `AbstractDynamicProgramming` | 9 Abstract Dynamic Programming | 292–307 | 13 | 8 | 5 |
| 10 | `ContinuousTime` | 10 Continuous-Time Markov chains and MDPs | 308–341 | 15 | 24 | 3 |

Appendix A (suprema and infima) is Mathlib. Appendix B (remaining proofs for
Ch 2, 6, 7, 9) is folded into those chapters. Appendix C (solutions) is used
as a guide, not formalised separately.

**Volume 2, General States**

| # | Project | Chapter | Pages | Results | Exercises | Examples |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| 11 | `PreludeExamples` | 1 Prelude: a firm problem, finite MDPs, optimal savings, sequential analysis | 1–56 | 8 | 12 | 0 |
| 12 | `AbstractDecisionProcesses` | 2 Abstract Decision Processes on posets: algorithms and convergence | 58–97 | 26 | 24 | 1 |
| 13 | `DecisionProcessesPospaces` | 3 ADPs on Pospaces: adding topology | 98–122 | 22 | 7 | 0 |
| 14 | `DecisionProcessesBanach` | 4 ADPs on Banach Space | 123–146 | 17 | 9 | 2 |
| 15 | `DecisionProcessTransformations` | 5 ADP Transformations: isomorphisms, semiconjugacy | 147–182 | 33 | 15 | 4 |
| 16 | `LinearDecisionProcesses` | 6 Linear Decision Processes | 184–206 | 9 | 2 | 8 |
| 17 | `RecursiveDecisionProcesses` | 7 Recursive Decision Processes | 207–245 | 14 | 15 | 6 |
| 18 | `AdditionalApplications` | 8 Additional Applications: job search, extensions, more applications | 246–294 | 17 | 49 | 1 |
| 19 | `ApproximationLearning` | 9 Approximation and Learning | 295–323 | 10 | 3 | 2 |

Volume 2 Appendix A (foundations, topology, measure and integration, vector
spaces and norms, order: 68 results, 55 exercises, 56 examples over pp.
324–392) is almost entirely Mathlib. It is not a project. A result from it that
Mathlib lacks is proved in the first chapter project that needs it and copied
onward, and recorded in that project's source map under "Appendix A".

Totals: 19 projects, 337 labelled results, 490 exercises, 158 examples.
InternationalEconomics produced 272–927 checked theorems per chapter; the
same range is expected here, with Vol 1 Ch 2, Vol 1 Ch 8 and Vol 2 Ch 5 the
largest.

### 3.2 `FiniteStates/JobSearch/` — Volume 1, Chapter 1 (the first project, in detail)

The chapter introduces every idea of the book on the McCall job-search model,
so the modules follow its sections.

| Module | Book | Contents |
| --- | --- | --- |
| `FiniteHorizon` | §1.1.1, Ex 1.1.1–1.1.3 | Finite-horizon job search: wage distribution on finite `W`, backward induction, value and reservation wage at each date, the `T`-period extension |
| `InfiniteHorizon` | §1.1.2 | The infinite-horizon Bellman equation as a fixed-point problem; the continuation value `h` and the scalar fixed-point equation |
| `NeumannSeries` | §1.2.1, Thm 1.2.1, Lemma 1.2.2 | Spectral radius, Gelfand's formula (Mathlib), `ρ(A) < 1 ⟹ (I − A)⁻¹ = ∑ Aᵏ`, the matrix-norm bound |
| `Contractions` | §1.2.2–1.2.3, Thm 1.2.3 | Banach's theorem on a closed `U ⊆ ℝⁿ` via Mathlib's `ContractingWith`, successive approximation, the a priori and a posteriori error bounds, global stability |
| `FunctionSpace` | §1.2.4, Lemma 1.2.4 | `ℝ^X` for finite `X`: sup norm, completeness, pointwise order, the identities of Lemma 1.2.4 |
| `ValuesAndPolicies` | §1.3.1, Prop 1.3.1 | The job-search Bellman operator `T` is a `β`-contraction on `ℝ^W`; the value function; the reservation-wage policy is optimal; `v* = max(w/(1−β), c + β ∑ v*(w')φ(w'))` |
| `ReservationWage` | §1.3.1–1.3.2, exercises | The scalar equation for `h*`, existence and uniqueness, monotonicity of the reservation wage in `c` and `β` (via Prop 2.2.7 proved here in the scalar case), the computational exercises recorded as not formalised |

Hypotheses made explicit: `W` finite and nonempty, `φ` a probability
distribution on `W`, `β ∈ [0,1)`, `c` a real compensation, wages nonnegative
where the book divides by `1 − β` and compares.

Headline results: `ValuesAndPolicies.isContraction_T`,
`ValuesAndPolicies.valueFunction_eq_max`, `ReservationWage.exists_unique`,
`ReservationWage.mono_compensation`, `Contractions.banach`.

Chapters 2–19 get the same module-level map at the start of their own phase,
written from the chapter text, as InternationalEconomics did one chapter at a
time.

---

## 4. What Mathlib supplies and what must be built

Checked against the Mathlib checkout pinned by InternationalEconomics (v4.34.0).

| Needed | Mathlib | Plan |
| --- | --- | --- |
| Banach fixed point, iterates converge, error bounds | `ContractingWith.fixedPoint`, `efixedPoint`, `apriori_dist_iterate_fixedPoint_le` | Use directly |
| Spectral radius, Gelfand's formula | `spectralRadius`, `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` | Use directly; specialise to matrices |
| Neumann series | `NormedRing.inverse_one_sub`, `NormedRing.tsum_geometric_of_norm_lt_one` | Use directly |
| Knaster–Tarski | `OrderHom.lfp`, `OrderHom.gfp` | Use directly (Vol 1 Ch 7 and 9, Vol 2 Ch 2) |
| Markov kernels, Markov property | `ProbabilityTheory.Kernel`, `IsMarkovKernel` | Use directly in Vol 2; Vol 1 uses stochastic matrices |
| Matrix exponential, Kolmogorov equations | `NormedSpace.exp`, `Matrix.exp` | Use directly (Vol 1 Ch 10) |
| Berge's maximum theorem | absent | Re-prove (Vol 2 Ch 3) |
| **Perron–Frobenius** | absent; only `Matrix.Irreducible` and `Primitive` definitions exist | **Build.** Weak form (`A ≥ 0 ⟹ ρ(A)` is an eigenvalue with a nonnegative eigenvector) in Vol 1 Ch 2; strict form for irreducible `A` where Ch 6 needs it. This is the main mathematical risk of Volume 1 |
| Stochastic dominance (FOSD) on finite sets | absent | Build in Vol 1 Ch 2 |
| Monotone Markov chains | absent | Build in Vol 1 Ch 3 |
| Hartman–Grobman | absent | Not claimed (section 2.5) |
| Blackwell's sufficient conditions | absent | Re-prove where the book first uses it |
| Weighted sup norms | absent | Re-prove (Vol 2 Ch 4, §7.2.2) |

---

## 5. Phasing and branches

Each phase is one branch and one PR against `main`, green on `verify.py` and
CI before it is opened. Branches are stacked in order, as the ten
InternationalEconomics chapter branches were. The user pushes; nothing is
pushed from this machine.

| Phase | Content | Branch |
| --- | --- | --- |
| 0 | Root scaffold: README index, CI matrix, `.gitignore`, `.gitattributes`, this proposal, and the `FiniteStates/JobSearch` project skeleton building a trivial root file. Establishes the toolchain pin and `verify.py`. | `scaffold` |
| 1 | `FiniteStates/JobSearch` complete (section 3.2) | `v1ch1-job-search` |
| 2 | `OperatorsFixedPoints`, including Perron–Frobenius weak form and FOSD | `v1ch2-operators-fixed-points` |
| 3–10 | Volume 1 chapters 3–10, one branch each | `v1ch3-markov-dynamics` … `v1ch10-continuous-time` |
| 11 | `PreludeExamples` | `v2ch1-prelude` |
| 12–19 | Volume 2 chapters 2–9, one branch each | `v2ch2-abstract-decision-processes` … `v2ch9-approximation-learning` |

For each phase the project README's theorem counts, the root README index row
and `proof-manifest.json` are updated in the same commit as the Lean code;
`verify.py` requires this. Each chapter's `docs/corrections.md` records any
printed claim found false or imprecise while formalising it. None are claimed
yet: the survey of 2026-09-18 read both volumes for reusable results, not for
errors.

Order is book order. The alternative, doing Vol 2 Ch 2–4 (the abstract theory)
early so that later Vol 1 chapters can specialise it, conflicts with the
self-contained-project rule and with following the books as written.

---

## 6. Decisions (resolved 2026-10-03)

1. **Folder layout and names.** Two subfolders, `FiniteStates/` (Volume 1) and
   `GeneralStates/` (Volume 2), each holding its chapter projects with the
   unsuffixed names of section 3.1. The CI matrix uses paths.
2. **Lean and Mathlib pin.** `v4.34.0`, the same as InternationalEconomics.
3. **The existing `LeanEconomics` library.** Not copied. Everything is re-proved
   from the book.
4. **Exercises.** All provable exercises in.
5. **Perron–Frobenius.** Prove the weak form in Vol 1 Ch 2 and the irreducible
   form in Ch 6.
6. **Volume 2 Appendix A.** Not a project.
7. **Out of scope.** Hartman–Grobman, Q-learning convergence, all computational
   sections and exercises.
