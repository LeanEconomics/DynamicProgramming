# Corrections to the source

Places where a claim in Chapter 4 of Sargent and Stachurski, *Dynamic
Programming*, Volume 2, is imprecise as printed, relies on an unstated hypothesis, or
where the Lean statement departs from the printed one. In each case the Lean statement
proves the corrected or stated version and cites the original. Entries are recorded when
found and revised if formalisation shows the finding itself to be wrong.

## Errors

| Where | Book says | Correction |
| --- | --- | --- |
| Ex 4.2.2, (4.17), p. 139; proof of Prop 4.2.3, p. 140 | `v_σ = (I − K_σ)⁻¹(−c + K_σ q)`; `T_σ` is affine with `r_σ := −c + K_σ q`, where `(K_σ f)(x) = β(x) ∫ f(x')(1 − σ(x'))P(x, dx')`. | From (4.16), `T_σ v = −c + K(σq) + K((1 − σ)v)`, so the constant term is `r_σ = −c + K(σq)`, not `−c + K((1 − σ)q)`. For the policy that launches everywhere, `K_σ = 0` and the printed formula gives `v_σ = −c`, while `T_σ(−c) = −c + Kq`, so `−c` is a fixed point only when `Kq = 0` (`RealOption.eq_4_17_misprint`). The lifetime value is `v_σ = ∑ₜ K_σᵗ(−c + K(σq))` (`RealOption.exercise_4_2_2`), and Proposition 4.2.3 is proved with `r_σ = −c + K(σq)` (`RealOption.rσ`). |
| Thms 4.1.3, 4.1.6, 4.1.8, Ex 4.1.2 | `(V, 𝕋)` semi-regular on a closed `V₀`. | As for Theorem 3.1.5, `V₀ = ∅` always qualifies, and then the conclusions fail; the proofs find a fixed point of `T` in `V₀`. `V₀` is assumed nonempty (`BanachLattice.theorem_4_1_3`, `BanachLattice.theorem_4_1_6`, `BanachLattice.theorem_4_1_8`, `BanachLattice.exercise_4_1_2`). The counterexample is in the Chapter 3 project (`ADP.theorem_3_1_5_needs_nonempty`). |

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| §A.5.3.4, applications on `bX` | `𝟙` is a normalized order unit of `bX`. | Only when `X` is nonempty (otherwise `‖𝟙‖ = 0`): `BM.isNormalizedOrderUnit_one` assumes `[Nonempty X]`. |
| Thm 4.1.1, p. 124 | `S` eventually contracting on a closed subset of a Banach space. | Proved for any complete metric space (`theorem_4_1_1`), with the rate `β = max(λ, 1/2)^{1/n}`. |
| Lemma 4.1.2, Thm 4.1.3, p. 125 | `V` an increasing subset of `E`. | Only closure under `v ↦ v + κe`, `κ ≥ 0`, is used (`BanachLattice.lemma_4_1_2_subtype`, `BanachLattice.theorem_4_1_3`); the norm is then sup-nonexpansive on `V` too (`BanachLattice.isSupNonexpansive_subtype`). |
| Thms 4.1.4–4.1.8, p. 127–130 | `V` a closed subset of the Banach lattice `E`. | Proved for any complete metric poset `V` carried into `E` by an isometric order embedding `ι` (`BanachLattice.IsIsoOrderEmbedding`), covering `V = E` and closed subsets. Theorems 4.1.4–4.1.6 do not use the scalar multiplication of `E`. |
| Thm 4.1.10 (Du), p. 131 | Cited from Du (1990) and Zhang (2012). | Proved for Banach lattices (`BanachLattice.theorem_4_1_10`): the orbits of `a` and `b` are squeezed together at rate `(1 − ε)ᵏ`, and completeness with the lattice norm gives the fixed point, so no Knaster–Tarski argument is needed. Any `ε ∈ (0, 1]` works (`BanachLattice.du_concave`, `BanachLattice.du_convex`). |
| §4.2.1.2, p. 135; Lemma A.5.32 | `ρ(βP) = β` by Lemma A.5.32. | Only `‖βP‖ ≤ β`, hence `ρ(βP) ≤ β < 1`, is used (`FirmL1.specRad_D_lt_one`, `L1.markovCLM_norm_le`). The Markov operator on `L¹(ψ)` needs only stationarity `ψP = ψ`, not that `P` be stochastic (`L1.markovCLM`). |
| §4.2.1.3 | `r > −1`, so `β > 0`. | `β ≥ 0` bounded measurable suffices (`FirmSD.βf_nonneg`). |
| Assumption 4.2.2 | `P` has a unique stationary distribution `φ`. | Uniqueness is not used: any stationary `φ` works (`RealOption.stationary`). |
| §4.2.3 | `X` a metric space. | Only the measurable structure is used. |
| Ex 4.2.4, p. 142 | A Borel measurable maximizer. | The least maximizer for a fixed linear order on the finite set `A` (`argmaxSel`, `measurable_argmaxSel`); any finite `A` admits such an order, so the regularity results assume only `A` finite and nonempty (`PostAction.adp_regular`). |
| Prop 4.2.5, p. 144 | Constant `β < 1` implies `ρ(K_σ) < 1`. | Proved for `β(x) ≤ b < 1` when the rows of `P` sum to one (`FiniteSE.specRad_lt_one_of_le`). |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| §A.4.3, (A.20) | `ρ(A) = sup{|λ| : λ ∈ σ(A)}`, with Gelfand's formula `‖Aᵏ‖^{1/k} → ρ(A)`. | `ρ(A)` is defined in Gelfand's form `inf_{k ≥ 1} ‖Aᵏ‖^{1/k}` (`BanachLattice.specRad`), which is the limit in Gelfand's formula; the identification with the complex spectrum is the formula the book cites. Exercise A.4.2 is then immediate (`BanachLattice.exercise_A_4_2`). |
| §A.5.3.6, Thm A.5.25 | Positive linear operators on a Banach lattice are bounded. | Positive operators are taken as bounded linear operators with `Av ≥ 0` for `v ≥ 0` (`BanachLattice.IsPositiveOp`). |
| (4.6), discount operators | `D : E₊ → E₊`. | A map `D : E → E` sending `E₊` into itself; only its values on `E₊` matter (`BanachLattice.IsDiscountOperator`). |
| Du's conditions, Thm 4.1.11 | `S` a self-map of `V = [a, b]`, concave or convex. | Concavity and convexity are stated for maps `E → E` on `[a, b]` (`ConcaveOn`, `ConvexOn`); a self-map of the subtype `[a, b]` is read through its extension by the identity (`BanachLattice.extendIcc`). |
| Policies in §4.2.1–4.2.2 | `σ : X → {0, 1}` measurable. | Measurable `σ : X → Bool`, with `𝟙` and `1 − σ` as `polInd` and `polCont`. |
| §4.2.1.2, §4.2.2 | Equations in `L¹`. | Elements of `L¹` are almost-everywhere classes; pointwise formulas such as (4.13) hold almost everywhere (`FirmL1.adp_bellman_coeFn`, `FirmL1.T_coeFn`). The real option Bellman equation (4.18) holds as an identity in `L¹(φ)` (`RealOption.adp_bellman`). |
| Ex 4.2.2, (4.17) | `(I − K_σ)⁻¹ = ∑ₜ K_σᵗ`. | As the limit of partial sums, the convention of Theorem A.4.10 (`RealOption.exercise_4_2_2`). |
| Props 4.2.1–4.2.6 | VFI, OPI and HPI converge. | VFI converges in the order sense and geometrically on all of the value space; OPI and HPI converge for every greedy selector. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Thm A.5.26 | Monotonicity of the spectral radius on positive operators | Not needed: the discount operators used are bounded directly. |
| Figures 4.1–4.3, Algorithm 4.1 | Plots, the AR(1)/Tauchen illustration of `ρ(K)`, the structural estimation loop | Numerical or informal. |
| §4.3 | Chapter notes | Not mathematical claims. |
