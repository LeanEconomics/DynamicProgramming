# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University Press,
2009): Chapter 20, pp. 510–528. Equation numbers are the book's. Lean names are relative to
`MeynTweedie.Epilogue`; names from Mathlib are marked as such. Names marked "carried" are in the
modules copied from the Chapter 16 project (see the [README](../README.md)). `L∞_V` is `BM X` in
the weighted coordinates `g = f/V`, and a kernel `κ` acts on it as `kOp V κ` when `κV ≤ cV`
(`WeightOK V κ`). `Π = 1 ⊗ π` is `piOp V π = kOp V (Kernel.const X π)` and `P − Π` is
`qOp V P π`. `|||P₁ − P₂|||_V` is `vOpNorm V P₁ P₂` and `|||Pⁿ − 1 ⊗ π|||_V` is `vErgDist V P π n`
(carried), with `eW V` the `[0, ∞]`-valued form of a real weight. `‖μ − ν‖` is `tvNorm μ ν`
(carried) and (V4) is `DriftV4 P V ρ b C` (carried). A Markov semigroup is `S : MarkovSemigroup X`
with kernels `S.P t`. Every place where the Lean statement departs from the book is listed in
[corrections](corrections.md).

## Chapter 20 introduction and §20.1 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 510 | The authors' turn to applications; the three sections as proposals for future monographs | Not formalised (informal) |
| p. 510 | The weighted supremum norm, Hordijk and Spieksma [163], and applications of the Geometric Ergodic Theorem | Not formalised (history) |

## §20.1.1 The spectrum of `P`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 510 | The spectral properties of the transition kernel | Not formalised (informal) |
| (20.1), p. 511 | Finite-rank approximations `P̂ = Σᵢ sᵢ ⊗ μᵢ`, bounded on `L∞_V` when `sᵢ ∈ L∞_V` and `μᵢ(V) < ∞` | Not formalised as such; finite-rank operators appear in `IsFinitePole` and in the truncations of `proposition_20_1_5_compact` |
| p. 511 | The setting `L∞_V` | `bmSub`, `BM`, `isClosed_bmSub`, `completeSpace_BM`, `mkBM`, `bmFun`; `WeightOK`, `kFun`, `kOpLin`, `kOp`, `kOp_apply`, `WeightOK.norm_kFun_le`, `WeightOK.comp`, `kOp_comp`, `kOp_id`, `kOp_pow`; `weightOK_const`, `kOp_const_apply`, `kOp_const_mul_kOp`, `kOp_mul_kOp_const`, `kOp_const_mul_self`, `kOp_mul_piOp`, `piOp_mul_kOp`, `piOp_mul_self`; the operator norm against `|||·|||_V`: `norm_kOp_sub_le`, `fNorm_le_norm_kOp_sub`, `vErgDist_le_norm`, `norm_le_vErgDist`, `weightOK_of_vErgDist`, `norm_kOp_le` |
| (20.2), p. 511 | `T_z = [Iz − P]⁻¹` and `Z_z = [Iz − P + 1 ⊗ π]⁻¹`, when the inverses exist as bounded operators on `L∞_V` | `Ring.inverse` (Mathlib) of `z − kOp V P`; `fundKernel V P π z` |
| p. 511 | For `|z| > 1` and `|||Pⁿ|||_V` bounded, `T_z = Σ z^{−n−1}Pⁿ` and `Z_z = Σ z^{−n−1}[P − 1 ⊗ π]ⁿ` | `hasSum_resolvent_of_norm_pow_le` (for any operator with `‖aⁿ‖ ≤ Ktⁿ` and `|z| > t`), `ring_inverse_eq` |
| p. 511 | `Z_z` and `T_z` generalise the resolvents `K_{a_ε}` (3.26) and `U_h` (12.13) | Not formalised (remark) |
| p. 511 | The fundamental kernel `Z = Z_1`; `ĝ = Zg` solves Poisson's equation (17.37) for `g ∈ L∞_V` | `fundKernel_poisson` (`Pf̂ = f̂ − f + π(f)` with `f̂ = (Zg)V`), `mul_fund_eq`; `exists_poisson_of_vUniform` (existence for a chain with the bound (20.4)) |
| p. 512 (i) | The spectrum `S_V(P)`: the `z` for which `T_z` is not a bounded operator on `L∞_V` | `spectrumV V P` (Mathlib's `spectrum ℂ` of `kOp V P`) |
| p. 512 (ii) | A pole of finite multiplicity: an isolated point whose projection `P̂_{z₀} = lim (2πi)⁻¹ ∮_{|z − z₀| = ε} [Iz − P]⁻¹ dz` is of finite rank of the form (20.1) | `rieszProj`, `IsFinitePole` (finite rank; the multiplicity is not recorded); see corrections |
| p. 512 (iii)–(iv) | A spectral gap: `1` is a pole of finite multiplicity; a discrete spectrum: `{z ∈ S_V(P) : |z| ≥ ε}` is finite and consists of poles of finite multiplicity | `HasSpectralGap`, `HasDiscreteSpectrum` |
| p. 512 | Spectral theory in the analysis of the Geometric Ergodic Theorem and large deviations | Not formalised (informal) |

## §20.1.2 Rates of convergence and eigenvalues

| Source | Claim | Lean |
| --- | --- | --- |
| p. 512 | `λ ∈ S_V(P)` is an eigenvalue if `Ph = λh` for some `h ∈ L∞_V` with `π(|h|) ≠ 0`; for `|λ| < 1` and `π(h) = 0`, `|Pⁿh − π(h)| = |λ|ⁿ|h|` | `eigen_rate` (`π(h) = 0` and `(Pⁿ − Π)h = λⁿh` for every `λ ≠ 1`), `mem_spectrum_of_apply_eq` (eigenvalues lie in the spectrum), `one_mem_spectrumV` (`1` with eigenfunction `1`: `oneV`, `kOp_oneV`, `oneV_ne_zero`) |
| p. 512 | On a finite space the second largest eigenvalue governs the rate | Not formalised (quoted) |
| p. 512 | `λ*` is called the spectral radius of `Pⁿ − 1 ⊗ π` | `spectralRadius ℂ (qOp V P π)` (Mathlib), the spectral radius of `P − 1 ⊗ π`; see corrections |
| Theorem 20.1.1 (i), p. 513 | A `V`-uniformly ergodic chain has a spectral gap in `L∞_V`, and `Z_z` exists as a bounded operator for `|z| > ε₀`, some `ε₀ < 1` | `theorem_20_1_1_i` (from the bound (20.4); also `S_V(P) ⊆ {|z| ≤ ε₀} ∪ {1}` and the Riesz projection at `1` equal to `1 ⊗ π`); `norm_sub_pow_le_of_rate`, `mem_spectrum_iff_sub_proj`, `kOp_const_eq` |
| Theorem 20.1.1 (ii), (20.3), p. 513 | If `|||Z_z|||_V < ∞` for `|z| > ε₀`, `ε₀ < 1`, the chain is `V`-uniformly ergodic and `lim n⁻¹ log |||Pⁿ − 1 ⊗ π|||_V ≤ log λ*`, `λ* = max{|z| : z ≠ 1, z ∈ S_V(P)}`, the minimal `ε₀` | `theorem_20_1_1_ii` (`P`, `1 ⊗ π` acting on `L∞_V`; `λ* ≤ ε₀`, `λ* = sup{|z| : z ∈ S_V(P) \ {1}}`, the `lim sup` of `|||Pⁿ − 1 ⊗ π|||_V^{1/n}` at most `λ*`, and `|||Pⁿ − 1 ⊗ π|||_V ≤ Rεⁿ` for `ε > λ*`); `spectral_rate_op` (operator form) |
| (20.4), p. 513 | Proof of (i): `|||Pⁿ − 1 ⊗ π|||_V ≤ Rr⁻ⁿ`, the power series of `Z_z` and the bound `|||Z_z|||_V ≤ R|z|⁻¹/(1 − |z|⁻¹r⁻¹)` | The hypothesis of `theorem_20_1_1_i`; `hasSum_resolvent_of_norm_pow_le`, `sub_proj_pow` (`(P − Π)ⁿ = Pⁿ − Π`, `n ≥ 1`), `pow_mul_proj`, `proj_mul_sub`, `sub_mul_proj` |
| p. 513 | `πZ_z = Z_zπ = z⁻¹π`, and `T_z = Z_z[I + (z − 1)⁻¹1 ⊗ π]` for `z ≠ 1` | `proj_mul_inv`, `inv_sub_of_inv_sub_proj`, `inv_sub_proj_of_inv_sub`, `inv_commute`, `resolvent_eq_op`, `resolvent_eq_fundKernel`, `mem_spectrum_iff_sub_proj_op` |
| pp. 513–514 | Proof of (ii): continuity of `|||Z_z|||_V`, Cauchy's formula for `fₙ = ε^{−n−1}(Pⁿf − π(f))` | Replaced by Gelfand's formula (Mathlib) in `spectral_rate_op`, with `vErgDist_le_nnnorm_sub_pow`, `ofReal_opNorm_eq`; see corrections |
| p. 514 | (20.3) says nothing about a finite `n`; reversible chains have explicit bounds | Not formalised (remark) |
| p. 514 | Reversibility: time reversal of the stationary process, equivalently of `(Φₜ, Φₜ₊₁)` | Not formalised; reversibility is defined by (20.5) |
| (20.5), p. 514 | The detailed balance equations `π(dx)P(x, dy) = π(dy)P(y, dx)` | `IsReversible` (integrated form), `isReversible_of_singleton` (on a countable space), `IsReversible.isInvariant` (invariance, with `B = X`), `measure_eq_tsum_singleton` |
| (20.6), p. 514 | For a reversible finite chain, `‖Pⁿ(x, ·) − π‖ ≤ √((1 − π(x))/π(x)) λ*ⁿ` (Diaconis and Stroock [90]); non-reversible bounds through `PP̃` [119]; surveys | Not formalised (quoted) |
| p. 514 | `L²(π)` and the `Lᵖ(π)` norm `‖f‖ₚ = (π(|f|ᵖ))^{1/p}` | `eLpNorm` (Mathlib), `MemLp` (Mathlib), `eLpNorm_two_sq` |
| (20.7), p. 514 | Geometric ergodicity in `Lᵖ(π)`: `‖Pⁿf − π(f)‖ₚᵖ ≤ Rr⁻ⁿ‖f‖ₚᵖ` | `IsLpGeomErgodic P π p` (norm form); see corrections |
| p. 515 | (20.7) means that the spectral radius of `P − 1 ⊗ π` on `Lᵖ(π)` is below `1`; geometric ergodicity in `Lᵖ(π)` gives `V`-uniform ergodicity for some `V` (Theorem 15.0.1) | Not formalised (remarks) |
| Proposition 20.1.2 (i), p. 515 | There is a reversible `V`-uniformly ergodic chain that is not geometrically ergodic in `L¹(π)` | `proposition_20_1_2_i` (the M/M/1 queue, `0 < p < 1/2`) |
| p. 515 | Proof of (i): every `λ ∈ [λ̲, 1)` is an eigenvalue with eigenfunction in `L∞_V`, hence in `L¹(π)`, with `π(h) = 0` and `‖Pⁿh − π(h)‖₁ = λⁿ‖h‖₁` | Repaired in `L¹(π)`: `mm1_integrable_pi`, `mm1_integral_pow`, `mm1Eig_rho_inv`, `integral_kernel_of_isInvariant`, `integral_bernoulliWalk_real`; see corrections |
| Proposition 20.1.2 (ii), p. 515 | There is a `V`-uniformly ergodic chain that is not geometrically ergodic in `L²(π)` | `proposition_20_1_2_ii` (the branch chain `branchKernel`, not Häggström's example); see corrections |
| p. 515 | Proof of (ii): geometric ergodicity in `L²(π)` gives `γ_f² ≤ R(r + 1)/(r − 1)‖f‖₂²` | False with (20.7) as printed: `asymptoticVariance_book_counterexample`. Corrected: `asymptoticVariance_le` (norm form), `asymptoticVariance_le_sq` (as printed, with `√R`, `√r`); see corrections |
| p. 515 | Häggström's example [150]: a `V`-uniformly ergodic chain and `f ∈ L²(π)` with infinite asymptotic variance | Not formalised; replaced by the branch chain: `IsBranchState`, `branchNext`, `branchJump`, `branchKernel`, `isMarkovKernel_branchKernel`, `branchKernel_hub`, `branchKernel_of_ne`, `branchKernel_singleton`, `branchJump_singleton`, `branchJump_univ`; `branchW`, `branchPi`, `isProbabilityMeasure_branchPi`, `isInvariant_branchPi`; `branch_reaches_hub`, `branch_isPhiIrreducible`, `branchV`, `branchC`, `branch_driftV4`, `branchC_isSmallSet`, `branch_vUniform`; `branchSet`, `branchKernel_pow_branch`, `branchPi_branchSet`, `branchPi_branchSet_le` |
| Proposition 20.1.2 (iii), p. 515 | A reversible chain is geometrically ergodic in `L²(π)` iff it is `V`-uniformly ergodic for some `V` finite `π`-a.e. (Roberts and Rosenthal [329]) | Not formalised (quoted; needs the spectral theorem on `L²(π)`) |

## §20.1.3 The spectrum of the M/M/1 queue

| Source | Claim | Lean |
| --- | --- | --- |
| p. 515 | The sampled M/M/1 queue is the random walk on the half line with increments `±1` | `bernoulliWalk p` (carried), `bernoulliWalk_eq`, `bernoulliWalk_singleton_eq` |
| (20.8), p. 515 | `Ph(n) = ph(n + 1) + (1 − p)h(n − 1)`, with `h(−1) = h(0)` | `mm1Op`, `integral_bernoulliWalk` (complex `h`), `integral_bernoulliWalk_real` |
| p. 516 | `V`-uniformly ergodic for `ρ = p/(1 − p) < 1`, `V(n) = r₀ⁿ`, `r₀ ∈ (1, ρ⁻¹)`; hence a spectral gap | `proposition_20_1_3_i`, `mm1_rate_lt_one`, `mm1_weightOK`; the spectral gap in `mm1_spectralGap_not_discrete` (through `theorem_20_1_1_i`) |
| p. 516 | The invariant law `π(n) = (1 − ρ)ρⁿ`; detailed balance holds, so the queue is reversible | `mm1Rho`, `mm1Rho_inv`, `mm1Rho_facts`, `mm1W`, `mm1Pi`, `mm1Pi_singleton`, `isProbabilityMeasure_mm1Pi`, `mm1_detailed_balance`, `mm1_isReversible` |
| p. 516 | The spectrum in `L∞_V` for `r₀ ∈ (ρ^{−1/2}, ρ⁻¹)` is not discrete although there is a spectral gap | `mm1_spectralGap_not_discrete` |
| p. 516 | The transform `H(z) = Σ z⁻ⁿh(n)` of an eigenfunction is a ratio of quadratics with two poles | Not formalised; the eigenfunctions are verified directly |
| Proposition 20.1.3 (i), p. 516 | The queue is `V`-uniformly ergodic | `proposition_20_1_3_i` (for every `r₀ ∈ (1, ρ⁻¹)`, at a geometric rate; through `bernoulliWalk_driftV4`, carried) |
| Proposition 20.1.3 (ii), (20.9), p. 516 | For `β ∈ (ρ^{−1/2}, r₀)`, `λ = pβ + (1 − p)β⁻¹ ∈ (0, 1)` is in `S_V(P)`, an eigenvalue with eigenfunction (20.9); `β₋ ∈ (1, ρ^{−1/2})` is the second root | (20.9) false as printed: `mm1EigfnBook_counterexample` (`mm1EigfnBook`). Corrected: `proposition_20_1_3_ii`, `mm1Eigfn`, `mm1Op_eigfn`, `mm1Eig`, `mm1Conj`, `mm1Eig_conj`, `mm1Conj_ne_zero`, `proposition_20_1_3_ii_eig` (`λ ∈ (0, 1)`, the second root and its uniqueness), `abs_mm1Eigfn_le`, `mm1_mem_spectrumV`; see corrections |
| Proposition 20.1.3 (iii), p. 516 | As `β ↓ ρ^{−1/2}`, `λ ↓ 2√(p(1 − p))`, an eigenvalue with eigenfunction `(1 − (p⁻¹ − 2)n)ρ^{−n/2}` | The limit: `proposition_20_1_3_iii_limit`, `mm1_sqrt_facts`, `two_mul_p_s`, `p_mul_sqrt_sq`. The eigenfunction is false as printed: `mm1EigLimBook_counterexample` (`mm1EigLimBook`). Corrected: `proposition_20_1_3_iii`, `mm1EigLim`, `mm1Op_eigLim`; see corrections |
| p. 516 | Proof: every geometric series solves the equation for `n ≥ 1`; only `β = 1` gives an eigenfunction alone | `mm1_geom` |
| p. 516 | Proof: `h(n) = βⁿ − cβ₋ⁿ` with the unique `c` making the equation hold at `n = 0` | The corrected `c` is built into `mm1Eigfn`; see corrections |
| p. 517 | `g(x) = px + (1 − p)x⁻¹` is convex, equals `1` at `x = 1` and `x = ρ⁻¹`, and has its minimum at `ρ^{−1/2}`, so `β₋` is unique | `proposition_20_1_3_ii_eig`, `proposition_20_1_3_iii_limit` (strict monotonicity on `[ρ^{−1/2}, ∞)`), `mm1Eig_rho_inv` |
| p. 517 | A spectral gap but not a discrete spectrum; the eigenvalues depend on `V`, with supremum `pr₀ + (1 − p)r₀⁻¹ → 1` as `r₀ ↑ ρ⁻¹` | `mm1_spectralGap_not_discrete`; the dependence on `V` is not stated separately |

## §20.1.4 Drift criterion for a discrete spectrum

| Source | Claim | Lean |
| --- | --- | --- |
| p. 517 | `V`-uniform ergodicity gives a spectral gap, so (V4) is sufficient for one; a stronger drift condition gives a discrete spectrum | `theorem_20_1_1_i`; `proposition_20_1_5` |
| (20.10), p. 517 | The nonlinear generator `H(G) = log(Pe^G/e^G)` | `nonlinGen` |
| (20.11), p. 517 | (DV3): `H(V) ≤ −δf + b1_C` for `f ≥ 1`, `δ > 0`, `b < ∞`, `V : X → [0, ∞]` | `DriftDV3` (multiplicative form, real `V`), `driftDV3_iff_nonlinGen` |
| p. 517 | (DV3) gives `∆e^V ≤ −βe^V + b'1_C` when `V` is bounded on `C`, with `b' = b + sup_C e^V`, `1 − β = sup e^{−δf}` | The constant is wrong: `driftV4_of_driftDV3_book_counterexample` (`swapKernel`). Corrected: `driftV4_of_driftDV3` (`b' = e^b sup_C e^V`, `1 − β = e^{−δ}`); see corrections |
| p. 518 | The LSS(F, G) model with Gaussian-tailed disturbances satisfies (DV3) with quadratic `V` and linear `f` | Not formalised (example) |
| p. 518 | The truncated kernel `P̂ₙ = I_{C_f(n)}P`, `C_f(n) = {f ≤ n}` | `truncKernel` |
| Proposition 20.1.4, p. 518 | Under (20.11) with `f` unbounded and `C ⊆ C_f(n)` for large `n`, `|||P − P̂ₙ|||_v → 0`, `v = e^V` | `proposition_20_1_4` (`|||P − P̂ₙ|||_v ≤ e^{−δn}` whenever `C ⊆ C_f(n)`; `f` measurable, not necessarily unbounded) |
| p. 518 | Proof: `I_{C_f(n)ᶜ}Pv ≤ e^{−δn}v` | In the proof of `proposition_20_1_4`, with `vOpNorm_le` (carried) |
| p. 518 | Wu's truncation technique; research with Kontoyiannis [219, 220] | Not formalised (history) |
| Proposition 20.1.5, p. 518 | On a countable space, (20.11) for a coercive `f` and a finite `C` gives a discrete spectrum in `L∞_v` | `proposition_20_1_5` (`f ≥ 1`, `V ≥ 0`) |
| p. 518 | Proof: `P̂ₙ` has finite rank, so a finite spectrum; `P` is a norm limit of them; by [219, Theorem 3.5] the spectrum of such a `P` is discrete | `proposition_20_1_5_compact` (finite rank, `suppSub`, `finiteDimensional_suppSub`; convergence in operator norm; `P` compact, `isCompactOperator_of_finiteDimensional_range`; nonzero spectral points are eigenvalues by the Fredholm alternative, Mathlib); the Riesz–Schauder theory: `compact_not_separated`, `finite_eigenvalues`, `finite_spectrum_compact`, `circleIntegral_clm_comm`, `continuousOn_resolvent`, `rieszProj_eq_of_le`, `resolvent_eq_inv_add`, `isCompactOperator_rieszProj`, `inv_sub_inv_ring`, `resolvent_mul_resolvent`, `rieszProj_mul_self`, `finiteDimensional_range_of_compact_idempotent`, `exists_pos_dist_of_finite`, `isFinitePole_of_compact`, `hasDiscreteSpectrum_of_compact` |

## §20.1.5 Multiplicative ergodic theory and large deviations

| Source | Claim | Lean |
| --- | --- | --- |
| (20.12), p. 518 | `λₙ,ₓ(F) = E_x[exp(Sₙ(F))]`, `Sₙ(F) = Σ_{k<n} F(Φₖ)` | The case `A = X` of `feynmanKac_apply` with `f = e^F` |
| p. 519 | The multiplicative ergodic theorem `n⁻¹ log λₙ,ₓ(F) → Λ(F)` | Not formalised (quoted) |
| p. 519 | The positive kernel `P_f(x, dy) = f(x)P(x, dy)` | `fkKernel`, `lintegral_fkKernel`, `lintegral_fkKernel_pow_succ` |
| (20.13), p. 519 | `P_fⁿ(x, A) = E_x[exp(Sₙ(F))1{Φₙ ∈ A}]`, the Feynman–Kac semigroup | `feynmanKac_apply` (with `Πₖ<ₙ f(Φₖ)`, on the path space `pathKernel`, carried), `feynmanKac` (any initial law, any measurable `h ≥ 0`) |
| p. 519 | `U_h` as a power series in this semigroup (12.14) | Not formalised (remark) |
| p. 519 | `Λ(F) = log λ` for the Perron–Frobenius eigenvalue; Tweedie, Vere-Jones and Seneta; spectral gaps for `P_f` [17, 218, 219] | Not formalised (quoted) |
| (20.14), p. 519 | `λ⁻ⁿλₙ,ₓ(F) → f̌(x)`, a Perron–Frobenius eigenfunction, `P_f f̌ = λf̌` | Not formalised (quoted) |
| p. 519 | The eigenvector equation as the multiplicative Poisson equation `H(F̌) = F̌ − F + Λ(F)` | False as printed: `nonlinGen_book_counterexample`. Corrected: `nonlinGen_log_eigen` (`H(F̌) = Λ − F`); see corrections |
| p. 519 | The multiplicative ergodic theorem for small bounded `F` under `V`-uniform ergodicity [218] and under (DV3) [17, 219] | Not formalised (quoted) |
| p. 519 | The twisted kernel `P̌(x, A) = f(x)/(λf̌(x)) ∫_A P(x, dy)f̌(y)`, a Markov kernel, geometrically ergodic in the settings of [17, 218, 219] | `twistedKernel`, `isMarkovKernel_twistedKernel`; its ergodicity is not formalised |
| (20.15), p. 520 | `n⁻¹ log P_π{Sₙ ≥ nc} → −I_F(c)`, the Fenchel–Legendre transform; bounds of [140]; Sobolev inequalities | Not formalised (quoted) |

## §20.1.6 Quasi-stationarity

| Source | Claim | Lean |
| --- | --- | --- |
| p. 520 | `M` is quasi-stationary if `P_x{Φₙ ∈ A | τ_M > n} → π_M(A)` | Not formalised |
| (20.16), p. 520 | For `f = 1_M`, `P_Mⁿ(x, A) = P_x{Φₙ ∈ A and τ_M > n}` | False with `τ_M` the return time: `killedKernel_returnTime_counterexample`. Corrected: `killedKernel_apply` (staying in `M` up to time `n − 1`); see corrections |
| p. 520 | Quasi-stationarity is the ratio limit `P_Mⁿ(x, A)/P_Mⁿ(x, X) → π_M(A)`; existence through an ergodic twisted kernel [118]; diffusions [166, 276] | Not formalised (quoted) |

## §20.2 Simulation and MCMC

| Source | Claim | Lean |
| --- | --- | --- |
| (20.17), p. 521 | The sample-path average `π̂ₙ(f)` | Not formalised separately; the case `W ≡ 0` of `cvEstimator` |
| (20.18), p. 521 | The CLT for `π̂ₙ(f)` with asymptotic variance `γ²` | Not formalised (Chapter 17 is not carried) |
| (20.19), p. 521 | The control-variate estimator `π̂ₙ^{CV}(f) = n⁻¹Σ_{k<n}[f(Φₖ) − Wₖ]` | `cvEstimator` |
| (20.20), p. 521 | `Wₜ = g(Φₜ) − Pg(Φₜ)` has steady-state mean `π(g − Pg) = 0` | `integral_controlVariate_eq_zero`, `integral_controlVariate_pow_eq_zero` |
| p. 521 | With `g = f̂` a solution of Poisson's equation, `Wₜ = f(Φₜ) − π(f)` and `π̂ₙ^{CV}(f) = π(f)` for every `n ≥ 1` | `cvEstimator_poisson` (on every path); existence of `f̂` for `f ∈ L∞_V`: `exists_poisson_of_vUniform` |
| p. 522 | Approximate solutions, shadow functions, fluid value functions; Figure 20.1 | Not formalised (survey and simulation) |
| (20.21), p. 522 | The Metropolis–Hastings acceptance probability `α(x, y) = min(1, π(y)q(y, x)/(π(x)q(x, y)))` | `mhAccept`, `mhAccept_mem`, `measurable_mhAccept`, `mhAccept_flow`, `mhAccept_detailed_balance` |
| p. 522 | The chain proposes from `q(x, ·)` and accepts with probability `α`; it satisfies (20.5) with invariant `π` | `mhMove`, `mhKernel`, `mhKernel_apply`, `isMarkovKernel_mhKernel`, `mhKernel_isReversible`, with `IsReversible.isInvariant` |
| pp. 522–523 | The independence sampler `q(x, ·) = p` and the random-walk algorithm `q(x, y) = p(|y − x|)` | The independence sampler is `mhKernel μ π (fun _ y => p y)`; the random-walk algorithm is a case of `mhKernel` |
| p. 523 (i) | The independence sampler is uniformly ergodic iff `sup π/p < ∞`, and otherwise not geometrically ergodic | The "if" half: `indepSampler_minorization`, `indepSampler_uniformlyErgodic` (`‖Pⁿ(x, ·) − π‖ ≤ 2(1 − M⁻¹)ⁿ`, through `theorem_16_2_4`, carried). The rest is not formalised (quoted from [256, 179]) |
| p. 523 (ii) | The random-walk algorithm is rarely uniformly ergodic, and geometrically ergodic iff the tails of `π` are exponentially bounded | Not formalised (quoted) |
| p. 523 | Further analyses [330, 331, 79, 335, 332]; the fluid-model approach [125]; perfect simulation [49] | Not formalised (survey) |
| §20.2.3, p. 523 | Machine learning, TD learning and stochastic approximation | Not formalised (survey) |

## §20.3 Continuous time models

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 523–524 | The continuous-time sequel that was never written; Doeblin's work | Not formalised (history) |
| (20.22)–(20.23), p. 524 | Doeblin's time-changed Brownian representation and the SDE | Not formalised |
| p. 524 | Translating theory from discrete to continuous time through resolvents [278] | Not formalised (informal) |
| p. 524 | A Markovian semigroup `{Pᵗ}` | `MarkovSemigroup` (Markov kernel in `(t, x)`, jointly measurable, `P⁰ = I`, semigroup property), `MarkovSemigroup.P`, `MarkovSemigroup.P_apply`, `MarkovSemigroup.isMarkovKernel_P`, `MarkovSemigroup.P_add`, `MarkovSemigroup.P_add_apply`, `MarkovSemigroup.act`, `MarkovSemigroup.measurable_act`, `MarkovSemigroup.abs_act_le`, `MarkovSemigroup.act_add` |
| pp. 524–525 | Non-explosion; hitting times `σ_A`, `τ_A`; the càdlàg property | Not formalised (no process is constructed) |
| p. 525 | The `δ`-skeleton `{Φ_{δn}}` | `S.P δ` with `MarkovSemigroup.P_nsmul` (`P^{nδ} = (P^δ)ⁿ`) |
| (20.24), p. 525 | The resolvent `U_α = ∫₀^∞ e^{−αt}Pᵗ dt` | `MarkovSemigroup.resolvent`, `MarkovSemigroup.integrableOn_resolvent`, `MarkovSemigroup.measurable_resolvent`, `MarkovSemigroup.abs_resolvent_le`, `MarkovSemigroup.act_resolvent` |
| p. 525 | Sampling at the times of an independent Poisson process of rate `α` gives a chain `Φ^α` with kernel `αU_α` | `MarkovSemigroup.expLaw`, `MarkovSemigroup.isProbabilityMeasure_expLaw`, `MarkovSemigroup.resolventKernel`, `MarkovSemigroup.isMarkovKernel_resolventKernel`, `MarkovSemigroup.integral_resolventKernel`, `MarkovSemigroup.lintegral_resolventKernel` |
| p. 525 | `ψ`-irreducibility, positive recurrence and aperiodicity of the process, through sampled chains and skeletons | Not defined separately: the theorems of §20.3.3 take these hypotheses for the skeleton `S.P δ` |
| (20.25)–(20.26), pp. 525–526 | A Harris ergodic `δ`-skeleton gives `‖Pᵗ(x, ·) − π‖ → 0`, since the distance is non-increasing in `t` | `MarkovSemigroup.tendsto_tvNorm_of_skeleton`, `MarkovSemigroup.tvNorm_antitone` |
| (20.27), p. 526 | The generator `DV = lim_{t→0} t⁻¹(PᵗV − V)` | Not formalised |
| p. 526 | The discrete-time martingale `Mₙ` built from `g = ∆h` | Not formalised (remark) |
| (20.28), p. 526 | The extended generator: `Ah = g` if `M_T = h(Φ_T) − h(Φ₀) − ∫₀ᵀ g(Φₛ) ds` is a local martingale | `MarkovSemigroup.IsExtGenerator` (semigroup form: `Pᵀh − h = ∫₀ᵀ Pˢg ds`); see corrections |
| Theorem 20.3.1 (i), (20.29), p. 526 | `U_α = U_β + (β − α)U_βU_α = U_β + (β − α)U_αU_β` | `MarkovSemigroup.theorem_20_3_1_i` (bounded measurable `g`), `MarkovSemigroup.resolvent_resolvent`; `setIntegral_Ioi_comp_add`, `integral_triangle_swap`, `integral_Ioo_exp_mul`, `MarkovSemigroup.integrable_triangle` |
| Theorem 20.3.1 (ii), (20.30), p. 526 | For bounded measurable `g`, `U_αg` is in the domain of the extended generator and `AU_αg = αU_αg − g` | `MarkovSemigroup.theorem_20_3_1_ii` |
| p. 527 | Lyapunov functions move between the process, the sampled chains and the skeletons | `MarkovSemigroup.resolventKernel_drift` ((20.31) in integrated form gives a drift for the sampled chain), `lintegral_exp_Ici`, `lintegral_exp_mul_lintegral_Ioc` |
| (20.31), p. 527 | Exponential drift towards `C`: `AV ≤ −βV + b1_C` with `V : X → [1, ∞]` | In integrated form, the hypothesis of `MarkovSemigroup.resolventKernel_drift`; for the skeleton, (V4) for `P^δ` (`DriftV4`, carried) |
| p. 527 | `C` is petite if it is petite for some sampled chain | Petiteness for the skeleton, `IsPetite (S.P δ) C` (carried) |
| Theorem 20.3.2, (20.32)–(20.33), p. 527 | For a `ψ`-irreducible aperiodic process, (i) positivity with geometric convergence of `Pᵗ(x, C)` on a petite set, (ii) `sup_C E_x[κ^{τ_C}] < ∞` for a closed petite set, and (iii) (20.31) for a closed petite set, are equivalent | For the process: not formalised. For a `ψ`-irreducible aperiodic skeleton the analogues are equivalent: `theorem_20_3_2_skeleton_tfae` (`IsLocallyGeomErgodic`, `HasKendallPetite`, `HasDriftV4`, through `theorem_15_0_1`, carried) |
| (20.34), p. 528 | Under (i)–(iii), `S_V = {V < ∞}` is absorbing and full, and `|||Pᵗ − 1 ⊗ π|||_V ≤ Rr⁻ᵗ` on `S_V` | `theorem_20_3_2_skeleton` ((V4) for a skeleton and `PˢV ≤ cV` on `[0, δ]` give `π(V) < ∞` and (20.34) at every `x`), `theorem_20_3_2_kernel` ((20.34) iff (V4) for the skeleton with an equivalent `V₀`, through `theorem_16_0_1`, carried), `vUniform_of_skeleton`, `norm_kOp_le`, `inv_pow_floor_le`; `S_V` is not formalised (`V` is finite) |
| p. 527 | A proof is in [101]; refinements in [218] | Not formalised (quoted) |
| (20.35)–(20.36), p. 528 | The continuous-time Feynman–Kac semigroup `Pₕᵗ` and the generalized resolvent `U_h`; `U_α = [αI − A]⁻¹` and `U_h = [I_{−H} − A]⁻¹` formally | Not formalised |
