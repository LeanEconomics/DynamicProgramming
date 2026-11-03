# Proposal: MC, QMC and RQMC simulation of Markov chains, in Lean

**Source.** Robert Kirkby, "Simulating a Markov chain: MC, QMC, RQMC", VFI Toolkit discourse,
posts #1–#3 (October 2026), https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687,
with the references it relies on:
- L'Ecuyer, *Randomized Quasi-Monte Carlo: An Introduction for Practitioners* (MCQMC 2016);
- L'Ecuyer, Munger and Tuffin (2010), the limiting distribution of RQMC estimators;
- Loh (2003), the CLT for scrambled nets;
- Chentsov (1967), Markov chains driven by completely uniformly distributed (CUD) sequences;
- Holroyd and Propp (2010), rotor walks and Markov chains;
- the BEST theorem for Eulerian trails;
- Meyn and Tweedie, Chapter 17 (already formalised in `StochasticStability/LimitTheorems`).

**Goal.** Formalise the mathematical claims of the posts, especially the convergence speeds the
posts attribute to "theory". Where a claim is imprecise, the formalisation fixes a precise reading
and says so. Where a claim is false, there is a Lean counterexample.

**Target.** This repository, folder `RQMCMarkov/`, alongside `RecursiveMethods/` and
`StochasticStability/`, with the usual conventions:
- one Lean/Mathlib project per topic;
- namespace `RQMCMarkov.<Project>`;
- README, `docs/source-map.md` (claim → Lean), `docs/corrections.md`, `proof-manifest.json` and
  `scripts/verify.py` for each project;
- a CI matrix entry and a root README section;
- branches `rqmc-<project>` stacked on `mt-ch20-epilogue`.

Finite state spaces throughout for the Markov part, which is the setting of the posts.

Status: draft for discussion, 2026-10-29. Nothing is built yet.

---

## 1. Project `PointSets` (post #1–#2: MC, QMC, RQMC for i.i.d. uniforms)

Definitions: point sets in `[0,1)^s`, star discrepancy `D*ₙ`, the estimator `(1/n) Σ f(zᵢ)`.

| Claim in the posts | What would be proved |
| --- | --- |
| MC error is `O(n^{-1/2})` | `Var = σ²/n`; CLT from Mathlib. |
| Midpoint stratification `{1/6, 1/2, 5/6}` is QMC | The midpoint rule's discrepancy is `1/(2n)`. |
| RQMC is unbiased when each point is marginally uniform | `E[μ̂] = μ`, for any point set whose points are each `U[0,1)^s`. |
| Stratified RQMC is unbiased, with a common shift or independent per-stratum shifts | Both are unbiased. Their variance is at most the MC variance, and `O(n^{-3})` for Lipschitz `f` with independent shifts. |
| QMC beats MC when the discrepancy falls faster than `n^{-1/2}` | Koksma's inequality in one dimension: `|μ̂ − μ| ≤ V(f) D*ₙ`. The van der Corput sequence (the one-dimensional Sobol sequence) has `D*ₙ = O(log n / n)`. |
| RQMC converges at least as fast as QMC | A random shift mod 1 at most doubles `D*`, so RQMC has MSE `≤ (2 V(f) D*ₙ)²`. |
| A randomly shifted lattice is not asymptotically normal; the limit is a spline | In one dimension, for `C¹ f`, `n(μ̂ − μ) → (f(1) − f(0))(U − 1/2)`, a degree-0 spline (uniform) limit. For `f(x) = x` this holds exactly for every `n`. |
| Owen scrambling gives a CLT (Loh 2003) | Stretch goal: probably large. The rest does not need it. |

## 2. Project `MarkovDriving` (post #3: driving a finite chain by a uniform sequence)

Definitions:
- inverse-CDF update `G(i, u)`: go to `j` when `cs_{i,j−1} < u ≤ cs_{ij}`;
- the path driven by a sequence `u`;
- the per-state stack representation, where the k-th departure from `i` uses `u^{(i)}_k`;
- empirical transition counts `N_ij(T)` and occupation counts `N_i(T)`.

| Claim in the posts | What would be proved |
| --- | --- |
| Inverse-CDF with i.i.d. uniforms gives the right chain | The driven path has the law of the Markov chain: equal to the `Kernel.traj` path measure. |
| MC: the empirical transition matrix converges at `O(1/√T)` (MT Ch. 17) | A.s. convergence, the CLT at `√T`, and the LIL rate `√(log log T / T)`, via the per-state martingale `N_ij − p_ij N_i` (links to `LimitTheorems`). |
| Driving by a single Sobol sequence fails | The van der Corput sequence is not CUD: consecutive pairs avoid half of `[0,1)²`. A two-state chain driven by it has the wrong occupation frequencies (Lean counterexample to "any low-discrepancy sequence works"). |
| A CUD driving sequence gives consistent simulation (Chentsov 1967) | Definition of CUD. For a finite irreducible chain with the inverse-CDF update, empirical state frequencies and time averages converge to `π`. |
| Per-state stacks: departures are balanced, so faster than `O(1/√T)` | `|N_ij − p_ij N_i| ≤ 2 N_i D*_{N_i}(stack i)`. With van der Corput stacks the empirical transition matrix error is `O(log T / T)`. |
| QMC (stacks): occupation error `O(log T / T)` | A general **discrepancy-to-occupation** theorem. If `h` solves Poisson's equation `h − Ph = 1_{x} − π_x`, then `|N_x(T) − T π_x| ≤ 2‖h‖∞ + Σᵢ (departure discrepancy of state i)`, from telescoping. Stacks give `O(log T)`, so the frequency error is `O(log T / T)`. |
| Rotor-router: occupation error `O(1/T)`, better than QMC (Holroyd–Propp 2010) | The same theorem, with each rotor's partial-cycle sum bounded by its cycle length: `|N_x(T) − T π_x| ≤ C`, with `C` explicit and independent of `T`. The transition counts are also within a constant of `p_ij N_i`. |
| Rotors give too-regular paths: in the two-state chain every spell lasts exactly 8 periods | For `p_ii = 7/8` with the balanced cycle, every spell has length exactly 8. Generally, spell lengths under a rotor are deterministic functions of the rotor position, so their distribution is not geometric. |
| Conditional MC "is exactly MC conditional on the counts" | Under MC from a fixed start, a path's probability depends only on its transition counts. So, conditional on the counts, the path is uniform over the paths with those counts. |
| Paths with given counts are Eulerian trails (BEST theorem gives an exact sampler) | Euler's theorem: balanced counts on a connected support have an Eulerian trail. The count of trails (BEST, via the matrix-tree theorem) is a stretch goal. |
| Stratified geometric spell lengths | The stratified inverse-CDF draws from the geometric law are unbiased, with variance at most i.i.d. sampling. The "adjust so they add up" step is a heuristic and is not formalised. |

The discrepancy-to-occupation theorem is the backbone of §2. It puts MC (a martingale term,
`O(√(T log log T))`), QMC stacks (`O(log T)`) and rotors (`O(1)`) into one inequality, which is
the ranking the posts describe.

## 3. Not planned

- Pseudo-random generators (post #1, PPS): no theorem is claimed.
- The MEP application (post #4 is a placeholder).
- Array-RQMC: the posts set it aside.

## 4. Order and size

`PointSets` (≈ 2–4k lines), then `MarkovDriving` (≈ 4–7k lines). The CLT/LIL row reuses
`StochasticStability/LimitTheorems` by copying modules. The stretch goals (Loh's CLT, BEST) are
decided after the rest is done.
