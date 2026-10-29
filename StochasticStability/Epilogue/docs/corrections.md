# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Six claims are false as
printed. Each is refuted in Lean by a counterexample of this project, and a corrected statement
is proved: the eigenfunction (20.9), the limiting eigenfunction of Proposition 20.1.3 (iii), the
constant of the (V4) bound derived from (DV3), the variance bound of p. 515 under (20.7) as
printed, the multiplicative Poisson equation of p. 519, and (20.16). A further entry repairs a
step of the proof of Proposition 20.1.2 (i). Each of these was checked against the page image of
the book, not only its text layer. The book's statements are paraphrased. The last section lists
what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Proposition 20.1.3 (ii), (20.9), p. 516, and its proof | For `ρ^{−1/2} < β < r₀`, `λ = pβ + (1 − p)β⁻¹` is an eigenvalue with eigenfunction `h(n) = (1 − β⁻¹)βⁿ − (1 − β₋⁻¹)β₋ⁿ`; the proof takes `h(n) = βⁿ − cβ₋ⁿ` with `c = (1 − β₋⁻¹)/(1 − β⁻¹)`, of which (20.9) is a multiple. | The coefficients are interchanged, in (20.9) and in `c`. Both geometric series solve `Ph = λh` for `n ≥ 1` (`mm1_geom`); at `n = 0` the series `βⁿ` leaves the error `(1 − p)(1 − β⁻¹)`, so the error cancels for `c = (1 − β⁻¹)/(1 − β₋⁻¹)`, and the eigenfunction is `h(n) = (1 − β₋⁻¹)βⁿ − (1 − β⁻¹)β₋ⁿ` (`mm1Eigfn`, `mm1Op_eigfn`, for every `β ≠ 0`). `mm1EigfnBook_counterexample`: for `p = 1/5`, `β = 3`, the printed function (`mm1EigfnBook`) fails the eigenvalue equation at `n = 0`. Proposition 20.1.3 (ii) is proved with the corrected function (`proposition_20_1_3_ii`). |
| Proposition 20.1.3 (iii), p. 516 | As `β ↓ ρ^{−1/2}`, `λ ↓ 2√(p(1 − p))`, an eigenvalue with eigenfunction `h(n) = (1 − (p⁻¹ − 2)n)ρ^{−n/2}`. | With `s = ρ^{−1/2}` a double root, `h(n) = (1 + an)sⁿ` solves the equation for `n ≥ 1` for every `a`, and the equation at `n = 0` forces `a = 1 − s`. The eigenfunction is `h(n) = (1 + (1 − ρ^{−1/2})n)ρ^{−n/2}` (`mm1EigLim`, `mm1Op_eigLim`); `p⁻¹ − 2` differs from `ρ^{−1/2} − 1` unless `p = 1/2`. `mm1EigLimBook_counterexample`: for `p = 1/5` (`s = 2`) the printed function (`mm1EigLimBook`) has `Ph(0) = 0` but `λh(0) = 4/5`. Part (iii) is proved with the corrected function (`proposition_20_1_3_iii`); the limit of the eigenvalues is `proposition_20_1_3_iii_limit`. |
| (DV3) ⇒ (V4), p. 517 | If `V` is bounded on `C`, (DV3) gives `∆e^V ≤ −βe^V + b' 1_C` with `b' = b + sup_C e^V` and `1 − β = sup_x e^{−δf(x)}`. | On `C`, (DV3) gives `Pe^V ≤ e^{b − δf} e^V ≤ e^b sup_C e^V`, so the constant must be `b' = e^b sup_C e^V` (or larger). `driftV4_of_driftDV3_book_counterexample`: the swap chain on two points (`swapKernel`) with `C = {0}`, `f ≡ 1`, `δ = 1`, `b = 4`, `V(0) = 0`, `V(1) = 3` satisfies (DV3), but `∆e^V(0) = e³ − 1 > 5 − β`. The corrected bound is `driftV4_of_driftDV3` (`f ≥ 1`, `V ≤ M` on `C`): (V4) for `e^V` with `1 − β = e^{−δ}` and `b' = e^b e^M`. |
| Proposition 20.1.2, proof of (ii), p. 515, with (20.7), p. 514 | Geometric ergodicity in `Lᵖ(π)` is (20.7), `‖Pⁿf − π(f)‖ₚᵖ ≤ Rr⁻ⁿ‖f‖ₚᵖ`, with `p`-th powers; in `L²(π)` it gives `γ_f² ≤ R(r + 1)/(r − 1)‖f‖₂²`. | With (20.7) as printed the bound is false. `asymptoticVariance_book_counterexample`: the centred functions of the two-state chain `[[3/4, 1/4], [1/4, 3/4]]` form the eigenvalue-`1/2` direction, where `‖Pⁿf‖₂² = 4⁻ⁿ‖f‖₂²`, so (20.7) holds with `R = 1`, `r = 4`; but for `‖f‖₂ = 1` the asymptotic variance is `1 + 2Σₙ 2⁻ⁿ = 3 > 5/3`. The bound holds for the norm form `‖Pⁿf̃‖₂ ≤ Rr⁻ⁿ‖f̃‖₂` (`asymptoticVariance_le`), and with (20.7) as printed it holds with `√R` and `√r` (`asymptoticVariance_le_sq`). Either bound gives the finiteness that the proof needs. The statements are for a linear map on a real inner product space, `P` on the centred functions of `L²(π)`. |
| Multiplicative Poisson equation, p. 519 | For the eigenfunction `P_f f̌ = λf̌`, `H(F̌) = F̌ − F + Λ(F)` with `F = log f`, `F̌ = log f̌`. | With `H` as in (20.10), `fPf̌ = λf̌` gives `H(F̌) = log(Pe^{F̌}/e^{F̌}) = Λ − F`; the printed right-hand side is `log Pe^{F̌}`. `nonlinGen_book_counterexample`: the identity kernel on a point with `f = 1`, `λ = 1` and `f̌ = e` has `H(F̌) = 0` but `F̌ − F + Λ = 1`. The corrected equation is `nonlinGen_log_eigen`, which also proves `log Pe^{F̌} = F̌ − F + Λ` (positive `f`, `f̌`, `λ`). |
| (20.16), p. 520 | For `f = 1_M`, `P_Mⁿ(x, A) = P_x{Φₙ ∈ A and τ_M > n}`. | With `τ_M` the first return time to `M`, `min{n ≥ 1 : Φₙ ∈ M}` (the book's definition, restated on p. 525), this is false. `killedKernel_returnTime_counterexample`: on two points with the identity kernel and `M = {1}`, `P_M(1, {1}) = 1`, while `{Φ₁ = 1, τ_M > 1}` is empty. The identity holds with "`Φₖ ∈ M` for `k < n`" (`killedKernel_apply`), that is, with `τ_M` the exit time from `M`; for `A ⊆ M` this is `Φ₀, …, Φₙ ∈ M`. The quasi-stationarity definition on p. 520 is to be read with the same `τ_M`. |
| Proposition 20.1.2 (i), proof, p. 515 | Every `λ` in an interval `[λ̲, 1)` is an eigenvalue with an eigenfunction `h ∈ L∞_V`, hence `h ∈ L¹(π)`, with `π(h) = 0` and `‖Pⁿh − π(h)‖₁ = λⁿ‖h‖₁`; this rules out (20.7). | For the fixed `V(n) = r₀ⁿ` of Proposition 20.1.3 the eigenvalues found there lie below `pr₀ + (1 − p)/r₀ < 1`, as the book itself notes on p. 517, so they do not fill an interval up to `1`. The argument is run in `L¹(π)`: for every `β ∈ (ρ^{−1/2}, ρ⁻¹)` the eigenfunction `h_β` is `π`-integrable (`mm1_integrable_pi`), `π(h_β) = 0`, `Pⁿh_β = λ(β)ⁿh_β` (`mm1_integral_pow`), and `λ(β) ↑ 1` as `β ↑ ρ⁻¹` (`mm1Eig_rho_inv`). Proposition 20.1.2 (i) holds as stated (`proposition_20_1_2_i`). This repairs a step of a proof; no counterexample is stated in Lean. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| §20.1.1, `L∞_V` | `L∞_V` is complex without comment; a kernel acts on it when it is a bounded operator. | `L∞_V` is `BM X` (bounded measurable complex functions) in the weighted coordinates `g = f/V`, and `kOp V κ` is the operator of a kernel with `V` measurable, `V ≥ 1` and `κV ≤ cV` (`WeightOK`); otherwise `kOp` is `0`. The Chapter 16 distances use real test functions, so `‖P̃ⁿ − Π‖ ≤ 2|||Pⁿ − 1 ⊗ π|||_V` (`norm_le_vErgDist`). |
| Theorem 20.1.1 (i), p. 513 | `Φ` is `V`-uniformly ergodic. | The hypothesis is the geometric bound (20.4), which the book's proof starts from; it is `V`-uniform ergodicity in the corrected sense of Theorem 16.0.1 of the Chapter 16 project (every distance finite). `P` is a Markov kernel, `π` an invariant probability, `V` measurable with `V ≥ 1` (`theorem_20_1_1_i`). |
| Theorem 20.1.1 (ii), p. 513 | `|||Z_z|||_V < ∞` for `|z| > ε₀`, `ε₀ < 1`; the rate (20.3) is a limit. | `P` and `1 ⊗ π` act on `L∞_V` (`WeightOK V P`, `WeightOK V (Kernel.const X π)`, so `π(V) < ∞`), and `z − (P − Π)` is invertible for `|z| > ε₀`. (20.3) is proved for the `lim sup` of `|||Pⁿ − 1 ⊗ π|||_V^{1/n}`, since the limit need not exist, with the bound `|||Pⁿ − 1 ⊗ π|||_V ≤ Rεⁿ` for every `ε > λ*` (`theorem_20_1_1_ii`). |
| Eigenvalues, p. 512 | `λ ∈ S_V(P)` is an eigenvalue if `Ph = λh` for some `h ∈ L∞_V` with `π(|h|) ≠ 0`; "provided `|λ| < 1` and `π(h) = 0`", `|Pⁿh − π(h)| = |λ|ⁿ|h|`. | `π(h) = 0` is derived, not assumed: for any `λ ≠ 1`, `ΠP = Π` gives `Πh = 0` and `(Pⁿ − Π)h = λⁿh` (`eigen_rate`); an eigenvalue lies in the spectrum (`mem_spectrum_of_apply_eq`). |
| Proposition 20.1.2, p. 515 | Each statement refers to a positive recurrent `ψ`-irreducible chain with invariant probability `π`. | The examples are irreducible and positive: the M/M/1 queue by `bernoulliWalk_isIrreducibleChain` (carried) and `mm1_isReversible`, the branch chain by `branch_isPhiIrreducible` and `isInvariant_branchPi`. These facts are not restated in `proposition_20_1_2_i` and `proposition_20_1_2_ii`. The M/M/1 queue has `0 < p < 1/2`. |
| Proposition 20.1.3, p. 516 | `ρ < 1`, `r₀ ∈ (ρ^{−1/2}, ρ⁻¹)`. | `0 < p < 1/2`. Part (i) holds for every `r₀ ∈ (1, ρ⁻¹)` (`proposition_20_1_3_i`), part (ii) needs only `r₀ < ρ⁻¹` with `β < r₀`, and part (iii) only `r₀ > ρ^{−1/2}`. |
| (DV3), (20.11), p. 517 | `f ≥ 1`, `V : X → [0, ∞]`. | `V` and `f` are real-valued, and (DV3) is stated multiplicatively, `Pe^V ≤ exp(−δf + b1_C)e^V` (`DriftDV3`); `driftDV3_iff_nonlinGen` gives the form with `H(V)` when `e^V` is integrable. `f ≥ 1` and `V ≥ 0` are hypotheses where they are used. |
| Proposition 20.1.4, p. 518 | (DV3) with `f` unbounded and `C ⊆ C_f(n)` for all large `n`. | `f` is measurable; the bound `|||P − P̂ₙ|||_v ≤ e^{−δn}` holds for every `n` with `C ⊆ C_f(n)`, and the convergence when this holds for all large `n`; `f` need not be unbounded (`proposition_20_1_4`). |
| Proposition 20.1.5, p. 518 | `X` countable; (DV3) with `f` coercive and `C` finite. | `X` is countable with measurable singletons, `P` is a Markov kernel, `f ≥ 1` has finite sublevel sets, `V ≥ 0` is real-valued (`proposition_20_1_5`). |
| §20.1.5, p. 519 | The twisted kernel is defined from a Perron–Frobenius eigenfunction. | `isMarkovKernel_twistedKernel` takes any `f̌` with `0 < f̌ < ∞`, `λ ∈ (0, ∞)` and `fPf̌ = λf̌`; the existence of such `f̌` is not formalised. |
| §20.2.1, p. 521 | `V`-uniform ergodicity, `g ∈ L∞_V`; `E_π[W_t] = 0`. | `π(g − Pg) = 0` for any `π`-integrable `g` with `Pg` integrable and `π` invariant (`integral_controlVariate_eq_zero`, `integral_controlVariate_pow_eq_zero`). `cvEstimator_poisson` needs only a solution of Poisson's equation. `exists_poisson_of_vUniform` assumes the bound (20.4). |
| §20.2.2, p. 522 | `X = ℝ`, densities with respect to Lebesgue measure. | The target `π` and the proposal `q(x, ·)` are densities with respect to an s-finite measure `μ` on a general space; `α = 1` where `π(x)q(x, y) = 0` (`mhAccept`, `mhKernel`). |
| Independence sampler, p. 523 | `sup_y π(y)/p(y) < ∞`. | `π ≤ Mp` with `M > 0`, both densities normalised (`indepSampler_uniformlyErgodic`); the rate is `2(1 − M⁻¹)ⁿ`. |
| §20.3.1, p. 524 | A Markovian semigroup of a non-explosive càdlàg process on a topological space. | `MarkovSemigroup X` is a Markov kernel `(t, x) ↦ Pᵗ(x, ·)`, jointly measurable, with `P⁰ = I` and `P^{s+t} = PˢPᵗ` for `s, t ≥ 0`. No process is constructed, so the path conditions are not used. |
| (20.25) ⇒ (20.26), pp. 525–526 | A Harris ergodic `δ`-skeleton. | `π` is a probability invariant for every `Pᵗ`, and the skeleton converges in total variation from the given `x` (`MarkovSemigroup.tendsto_tvNorm_of_skeleton`). |
| Theorem 20.3.1, p. 526 | `Ah = g` if (20.28) is a local martingale for each initial condition. | `IsExtGenerator h k`: `Pᵀh(x) − h(x) = ∫₀ᵀ Pˢk(x) ds` for all `T ≥ 0` and `x`, the mean-zero (Dynkin) form of (20.28), which with the Markov property gives the martingale property. `g` is bounded and measurable (`MarkovSemigroup.theorem_20_3_1_i`, `MarkovSemigroup.theorem_20_3_1_ii`). |
| Theorem 20.3.2, pp. 527–528 | A `ψ`-irreducible aperiodic process; (20.31) with `V : X → [1, ∞]` finite at one point; (20.34) on the absorbing set `S_V`. | Proved for skeletons. `theorem_20_3_2_skeleton`: a `ψ`-irreducible aperiodic `δ`-skeleton with (V4) on a petite set, `PˢV ≤ cV` for `0 ≤ s ≤ δ`, `π` invariant for every `Pᵗ` and `V ≥ 1` real-valued, gives `π(V) < ∞` and (20.34) at every `x`. `theorem_20_3_2_kernel`: under the same local bound and `π(V) < ∞`, (20.34) holds iff the skeleton satisfies (V4) for some `V₀` equivalent to `V`. `theorem_20_3_2_skeleton_tfae`: the skeleton analogues of (20.32), (20.33) and (20.31) are equivalent. |
| §20.3.3, p. 527 | (20.31) is translated to the sampled chain. | The drift is taken in integrated form, `PᵗV + β∫₀ᵗ PˢV ds ≤ V + b∫₀ᵗ Pˢ(·, C) ds`, and gives `(α + β)R_αV ≤ αV + bR_α(·, C)` for the sampled chain (`MarkovSemigroup.resolventKernel_drift`). |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 20.1.1 (i), p. 513 | The power series for `Z_z`, the formula `T_z = Z_z[I + (z − 1)⁻¹1 ⊗ π]`, hence a spectral gap. | The same series and formula (`hasSum_resolvent_of_norm_pow_le`, `resolvent_eq_fundKernel`); the spectral gap is proved by computing the Riesz projection at `1` as a contour integral: it is `1 ⊗ π` for every radius `ε < 1 − ε₀` (`rieszProj_one_eq`), an operator of rank one (`kOp_const_eq`). |
| Theorem 20.1.1 (ii), pp. 513–514 | Cauchy's formula on `|z| = ε` with a uniform bound on `|||Z_z|||_V`. | Gelfand's spectral radius formula (Mathlib) for `P − Π`, with `(P − Π)ⁿ = Pⁿ − Π` (`sub_proj_pow`) and `|||Pⁿ − 1 ⊗ π|||_V ≤ ‖(P − Π)ⁿ‖` (`vErgDist_le_nnnorm_sub_pow`); `λ*` is identified with the largest `|z|`, `z ∈ S_V(P) \ {1}`, through `mem_spectrum_iff_sub_proj` (`spectral_rate_op`). |
| Proposition 20.1.2 (ii), p. 515 | Häggström's example [150] of a `V`-uniformly ergodic chain and `f ∈ L²(π)` with infinite asymptotic variance, with the variance bound. | A different, simpler chain. The branch chain (`branchKernel`) on `ℕ × ℕ` jumps from the hub `(0, 0)` to `(k, k)` with probability `2^{−(k+1)}` and walks deterministically down branch `k` back to the hub. Its invariant law is `π(hub) = 1/2`, `π(i, j) = 2^{−(i+2)}` (`isInvariant_branchPi`); (V4) holds for `V(i, j) = (3/2)ʲ` on a small set (`branch_driftV4`, `branchC_isSmallSet`), so it is `V`-uniformly ergodic (`branch_vUniform`). For the indicator `g` of branch `2n`, `|Pⁿg − π(g)| ≥ 1/2` on half the branch, so `‖Pⁿg − π(g)‖₂ ≥ ‖g‖₂/(2√2)` for every `n` (`proposition_20_1_2_ii`). The asymptotic variance is not used. |
| Proposition 20.1.5, p. 518 | Theorem 3.5 of [219]: a norm limit of finite-rank kernels has a discrete spectrum. | The truncations have finite rank (`finiteDimensional_suppSub`) and converge in operator norm, so `P` is compact (`proposition_20_1_5_compact`); a compact operator has a discrete spectrum by the Riesz–Schauder theory proved here: finitely many eigenvalues outside each disc (`finite_eigenvalues`, via the Riesz lemma), the Fredholm alternative (Mathlib, `finite_spectrum_compact`), Riesz projections independent of the radius, compact and idempotent (`rieszProj_eq_of_le`, `isCompactOperator_rieszProj`, `rieszProj_mul_self`), hence of finite rank (`finiteDimensional_range_of_compact_idempotent`, `isFinitePole_of_compact`, `hasDiscreteSpectrum_of_compact`). |
| Theorem 20.3.2, p. 527 | Proved in [101] for the process, by moving Lyapunov functions between the process, the sampled chains and skeletons. | Theorem 15.0.1 and Theorem 16.0.1 (carried) applied to the skeleton `P^δ` (`theorem_20_3_2_skeleton_tfae`, `theorem_20_3_2_kernel`), and the bound for all `t` from `Pᵗ − 1 ⊗ π = (P^{nδ} − 1 ⊗ π)Pˢ` with `PˢV ≤ cV` (`vUniform_of_skeleton`). |

## Conventions

* The PDF text layer of this chapter drops many symbols (the `≠` of `π(|h|) ≠ 0` and of
  `z ≠ 1` in Theorem 20.1.1, primes, hats, checks, square roots and the exponent `1/2`). Every
  entry above was checked against the page image.
* `λ*` is the spectral radius of `P − 1 ⊗ π` (`spectralRadius ℂ (qOp V P π)`), which lies in
  `[0, 1)`; p. 512 calls it the spectral radius of `Pⁿ − 1 ⊗ π`, which is read with `n = 1`. It
  equals `sup{|z| : z ∈ S_V(P), z ≠ 1}` (`theorem_20_1_1_ii`).
* `IsFinitePole` asks that the Riesz projections converge to an operator of finite rank, not one of
  the form (20.1) with measures `μᵢ`; the multiplicity `n` is not recorded. `HasSpectralGap` and
  `HasDiscreteSpectrum` are the definitions of p. 512 with this notion of pole.
* Geometric ergodicity in `Lᵖ(π)` is `IsLpGeomErgodic` in norm form,
  `‖Pⁿf − π(f)‖ₚ ≤ Rr⁻ⁿ‖f‖ₚ`. For `p = 1` this is (20.7); for `p > 1`, (20.7) with constants
  `R`, `r` is the norm form with `R^{1/p}`, `r^{1/p}`, so Proposition 20.1.2 holds under either
  reading.
* The asymptotic variance is the series (17.3), `π(f̃²) + 2Σ_{n≥1} π(f̃Pⁿf̃)`, written as inner
  products; p. 515 cites (17.4).
* The M/M/1 queue is the Bernoulli walk `bernoulliWalk p` of Chapter 15 (carried), with the
  convention `h(−1) = h(0)` of (20.8) (`mm1Op`, `integral_bernoulliWalk`). Reversibility
  (`IsReversible`) is (20.5) in integrated form.
* (V4) from (DV3) is stated with `1 − β = e^{−δ}`, which bounds `sup_x e^{−δf(x)}` from above
  since `f ≥ 1`.
* `P_f` is `fkKernel P f` with `f : X → [0, ∞]`, so (20.13) is stated with `Πₖ<ₙ f(Φₖ)` and holds
  for `f = e^F` and for `f = 1_M` alike. `λₙ,ₓ(F)` (20.12) is the case `A = X` and has no separate
  name.
* The sampled chain `Φ^α` has the kernel `R_α = ∫ Pᵗ αe^{−αt} dt` (`resolventKernel`); the Poisson
  sampling times are represented by their exponential law (`expLaw`), not by a process.
* The carried modules are copied from the Chapter 16 project without change apart from the
  namespace and the imports (see the [README](../README.md)). The corrections they contain belong
  to Chapters 1–16, are recorded in their module docstrings and in those projects, and are not
  repeated here.

## Not formalised

* **Finite-rank approximations (20.1)** (p. 511) as such, and the resolvents `K_{a_ε}` and `U_h`
  that `Z_z` generalises.
* **The Diaconis–Stroock bound (20.6)** and the bounds of [119] for finite chains (p. 514),
  quoted results resting on the spectral decomposition of reversible and symmetrised matrices;
  the characterisation of reversibility through time reversal (p. 514).
* **Proposition 20.1.2 (iii)** (Roberts and Rosenthal [329]), which needs the spectral theorem for
  self-adjoint operators on `L²(π)`; the remark that geometric ergodicity in `Lᵖ(π)` gives
  `V`-uniform ergodicity (p. 515); Häggström's example [150].
* **The transform method** of p. 516 (the rational function `H(z)`); the eigenfunctions are
  verified directly.
* **The LSS(F, G) example** of (DV3) with Gaussian-tailed disturbances (p. 518).
* **Multiplicative ergodic theory** (pp. 518–520): the limit `Λ(F)`, the Perron–Frobenius
  eigenvalue and eigenfunction, (20.14), the large deviation limit (20.15) with the
  Fenchel–Legendre transform, the bounds of [140], and Sobolev inequalities. These need
  Perron–Frobenius theory for positive operators on `L∞_V` and the arguments of [17, 218, 219].
* **Quasi-stationarity** (p. 520): the existence of `π_M`, the ratio limit theorem, and the
  continuous-time results of [166, 276].
* **Simulation** (pp. 521–523): the CLT form (20.18), approximate solutions of Poisson's equation
  and shadow functions, Figure 20.1, the converse half of claim (i) of p. 523 and claim (ii) on
  the random-walk Metropolis–Hastings algorithm [256, 179], the fluid-model approach of [125], and
  §20.2.3 on machine learning.
* **Continuous-time processes** (pp. 523–528): Doeblin's equations (20.22)–(20.23); the
  construction of the process, non-explosion and the càdlàg property; hitting times `σ_A`, `τ_A`;
  the definitions of irreducibility, positivity, aperiodicity and petiteness for the process; the
  generator (20.27); the local-martingale definition (20.28) of the extended generator; the
  equivalence of (i)–(iii) of Theorem 20.3.2 for the process ((20.32), (20.33) with
  continuous-time hitting times, (20.31) with the extended generator) and the absorbing set
  `S_V`; and the continuous-time Feynman–Kac semigroup and generalized resolvent (20.35)–(20.36).
  Mathlib has no construction of a continuous-time Markov process from a semigroup.
* **Informal remarks and history.** The preface to the chapter (p. 510), the history of the
  weighted norm and of its applications (p. 510), Doeblin's work (p. 524), the remark that the
  eigenvalues depend on `V` (p. 517; used in the repair above), and the forward references.
