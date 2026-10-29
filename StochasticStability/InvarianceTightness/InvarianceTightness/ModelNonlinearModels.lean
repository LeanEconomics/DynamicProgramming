/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.ModelLinearModels
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Nonlinear state space models

Copied from the `MarkovModels` project (MT Chapters 1–2), with the namespace renamed, for the
model examples of Chapter 6.

MT, §2.2, pp. 26–33, §2.3, pp. 33–38, and §C.2.2–C.2.3 of Appendix C, pp. 547–551.

* `nssKernel Γ F`: the nonlinear state space model NSS(F) and its scalar case SNSS(F)
  (MT, (SNSS1), p. 26; (NSS1), p. 29); a smooth `F` gives a Markov kernel
  (`isMarkovKernel_nssKernel_of_contDiff`). Its control model CM(F) is `controlMap F`
  (MT, (2.5), (2.8)).
* `bilinearKernel`: the simple bilinear model (MT, (SBL1), (2.7), p. 27), with
  `F(x, w) = (θ + bw)x + w` (`bilinearStep_eq`, Figure 2.2), smooth (`contDiff_bilinearStep`).
* `dblKernel`: the dependent parameter bilinear model (MT, (DBL1), (2.13)–(2.15), p. 32) on the
  state `(θ, Y)`. **Correction:** (2.15) lists the state in the order `(Y, θ)` on the right but
  returns `(θ, Y)`; `dbl_printed_ne` shows the printed map does not reproduce (2.13)–(2.14).
* `narmaKernel`: the NARMA(k, ℓ) model in its Markovian realization on `ℝᵏ × ℝˡ`
  (MT, (NARMA1), (2.9), p. 30); ARMA is the linear case (`armaKernel_eq_narmaKernel`).
* The gumleaf attractor (MT, §2.2.3, pp. 30–31): `gumleafMap` realizes (2.10)
  (`gumleafMap_of_recursion`); `gumleafKernel` is the noisy model (2.12). The transformation
  `squash z = (1 + |z|)⁻¹ z` maps `ℝ²` one-to-one onto the open unit disk
  (`eNorm2_squash_lt_one`, `unsquash_squash`, `squash_unsquash`). **Correction:** (2.11) as
  printed applies `F` to the transformed state; the transformed chain actually follows
  `squash ∘ F ∘ unsquash` (`squash_gumleafMap`), and `gumleaf_printed_ne` shows the printed form
  differs.
* `setarKernel`: the SETAR model (MT, (SETAR1), p. 28) with regime `setarRegime r x`
  (`setarRegime_eq_iff`: `r_{j−1} < x ≤ r_j`) and independent regime noises; its kernel is
  `P(x, A) = Γ_j{w : φ(j) + θ(j)x + w ∈ A}` (`setarKernel_apply'`). `setar_not_continuous`: the
  SETAR map need not be continuous (MT, p. 28).
* `sacKernel`: the closed loop simple adaptive control model (MT, (2.22)–(2.25), p. 36), with
  Gaussian disturbances in `sacGaussianKernel`. `sac_closed_loop` derives (2.22)–(2.23) from
  (2.20)–(2.21), the Kalman filter and the certainty equivalence control; `sacStep_sigma_mem` and
  `sacKernel_apply_Icc` show `[σ_z², σ_z²/(1 − α²)] × ℝ²` is invariant (MT, p. 36);
  `sac_rls` is the recursive least squares special case (MT, p. 36).
* `rcaKernel`: the random coefficient autoregression (MT, (RCA1), p. 550).
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff Matrix

/-! ### NSS(F) and SNSS(F) -/

/-- The nonlinear state space model NSS(F) (MT, (NSS1), p. 29), and for `X = W = ℝ` the scalar
model SNSS(F) (MT, (SNSS1), p. 26): `Xₖ = F(Xₖ₋₁, Wₖ)` with disturbance law `Γ`. It is the
random recursion kernel; its control model CM(F) is `controlMap F`. -/
noncomputable abbrev nssKernel {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (Γ : Measure W) (F : X × W → X) : Kernel X X :=
  recursionKernel Γ F

/-- A smooth (`C^∞`) NSS(F) model on second-countable Borel normed spaces is a Markov kernel; in
fact continuity of `F` suffices. -/
theorem isMarkovKernel_nssKernel_of_contDiff {E V : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] (Γ : Measure V) [IsProbabilityMeasure Γ] {F : E × V → E}
    (hF : ContDiff ℝ ∞ F) : IsMarkovKernel (nssKernel Γ F) :=
  isMarkovKernel_recursionKernel Γ hF.continuous.measurable

/-! ### The simple bilinear model -/

/-- The simple bilinear step `F(x, w) = θx + bxw + w` (MT, (SBL1), (2.7), p. 27). -/
def bilinearStep (θ b : ℝ) (p : ℝ × ℝ) : ℝ := θ * p.1 + b * p.1 * p.2 + p.2

/-- The bilinear step is `F(x, w) = (θ + bw)x + w`, the form of Figure 2.2. -/
theorem bilinearStep_eq (θ b x w : ℝ) : bilinearStep θ b (x, w) = (θ + b * w) * x + w := by
  simp only [bilinearStep]
  ring

/-- The bilinear model is a smooth SNSS(F) model. -/
theorem contDiff_bilinearStep (θ b : ℝ) : ContDiff ℝ ∞ (bilinearStep θ b) := by
  unfold bilinearStep
  fun_prop

/-- The simple bilinear model (MT, (SBL1), p. 27) with error law `Γ`. -/
noncomputable def bilinearKernel (Γ : Measure ℝ) (θ b : ℝ) : Kernel ℝ ℝ :=
  recursionKernel Γ (bilinearStep θ b)

/-- The simple bilinear model is a Markov kernel. -/
theorem isMarkovKernel_bilinearKernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ) :
    IsMarkovKernel (bilinearKernel Γ θ b) :=
  isMarkovKernel_recursionKernel Γ (contDiff_bilinearStep θ b).continuous.measurable

/-- `P(x, A) = Γ{w : θx + (bx + 1)w ∈ A}` for the bilinear model. -/
theorem bilinearKernel_apply' (Γ : Measure ℝ) [SFinite Γ] (θ b x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    bilinearKernel Γ θ b x A = Γ {w | θ * x + (b * x + 1) * w ∈ A} := by
  rw [bilinearKernel, recursionKernel_apply' Γ (contDiff_bilinearStep θ b).continuous.measurable
    x hA]
  congr 1
  ext w
  simp only [mem_ofPred_eq, bilinearStep]
  ring_nf

/-! ### The dependent parameter bilinear model -/

/-- The dependent parameter bilinear step on the state `(θ, Y)` with disturbance `(Z, W)`
(MT, (2.15), p. 32, with the state order of the box (DBL1)):
`F((θ, Y), (Z, W)) = (αθ + Z, θY + W)`. -/
def dblStep (α : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (α * p.1.1 + p.2.1, p.1.1 * p.1.2 + p.2.2)

/-- (2.14): `θₖ₊₁ = αθₖ + Zₖ₊₁`. -/
theorem dblStep_fst (α θ Y Z W : ℝ) : (dblStep α ((θ, Y), (Z, W))).1 = α * θ + Z := rfl

/-- (2.13): `Yₖ₊₁ = θₖYₖ + Wₖ₊₁`. -/
theorem dblStep_snd (α θ Y Z W : ℝ) : (dblStep α ((θ, Y), (Z, W))).2 = θ * Y + W := rfl

/-- The dependent parameter bilinear model is a smooth two-dimensional NSS(F) model. -/
theorem contDiff_dblStep (α : ℝ) : ContDiff ℝ ∞ (dblStep α) := by
  unfold dblStep
  fun_prop

/-- The dependent parameter bilinear model (MT, (DBL1)–(DBL2), p. 32): `Z` and `W` independent
with laws `Γz` and `Γw`, so the disturbance law is the product `Γz ⊗ Γw`. -/
noncomputable def dblKernel (Γz Γw : Measure ℝ) (α : ℝ) : Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  recursionKernel (Γz.prod Γw) (dblStep α)

/-- The dependent parameter bilinear model is a Markov kernel. -/
theorem isMarkovKernel_dblKernel (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] (α : ℝ) : IsMarkovKernel (dblKernel Γz Γw α) :=
  isMarkovKernel_recursionKernel _ (contDiff_dblStep α).continuous.measurable

/-- (2.15) as printed: the argument is written `(Y, θ)` while the value is `(θ', Y')`. -/
def dblPrinted (α : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (α * p.1.2 + p.2.1, p.1.2 * p.1.1 + p.2.2)

/-- **Correction to (2.15).** Read as a map of the state `(Y, θ)`, the printed `F` does not give
the next state `(θY + W, αθ + Z)` of (2.13)–(2.14): at `α = 0`, `(Y, θ) = (1, 2)`, `Z = W = 0`
it returns `(0, 2)` instead of `(2, 0)`. The consistent form is `dblStep` on `(θ, Y)`. -/
theorem dbl_printed_ne :
    dblPrinted 0 ((1, 2), (0, 0)) ≠ ((2 : ℝ) * 1 + 0, (0 : ℝ) * 2 + 0) := by
  simp [dblPrinted]

/-! ### NARMA models -/

/-- The NARMA(k, ℓ) step on `((Yₙ₋₁, …, Yₙ₋ₖ), (Wₙ₋₁, …, Wₙ₋ℓ))` with new error `Wₙ`:
`Yₙ = G(Yₙ₋₁, …, Yₙ₋ₖ, Wₙ, Wₙ₋₁, …, Wₙ₋ℓ)` is shifted in (MT, (NARMA1), (2.9), p. 30). -/
def narmaStep {k l : ℕ} (G : (Fin k → ℝ) × ℝ × (Fin l → ℝ) → ℝ)
    (p : ((Fin k → ℝ) × (Fin l → ℝ)) × ℝ) : (Fin k → ℝ) × (Fin l → ℝ) :=
  (shiftIn (G (p.1.1, p.2, p.1.2)) p.1.1, shiftIn p.2 p.1.2)

/-- The NARMA step is measurable when `G` is. -/
theorem measurable_narmaStep {k l : ℕ} {G : (Fin k → ℝ) × ℝ × (Fin l → ℝ) → ℝ}
    (hG : Measurable G) : Measurable (narmaStep G) := by
  have h1 : Measurable fun p : ((Fin k → ℝ) × (Fin l → ℝ)) × ℝ => G (p.1.1, p.2, p.1.2) :=
    hG.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact (measurable_shiftIn.comp (h1.prodMk (measurable_fst.comp measurable_fst))).prodMk
    (measurable_shiftIn.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

/-- The NARMA(k, ℓ) model as a Markov chain on `ℝᵏ × ℝˡ` (MT, (2.9), p. 30). -/
noncomputable def narmaKernel {k l : ℕ} (Γ : Measure ℝ) (G : (Fin k → ℝ) × ℝ × (Fin l → ℝ) → ℝ) :
    Kernel ((Fin k → ℝ) × (Fin l → ℝ)) ((Fin k → ℝ) × (Fin l → ℝ)) :=
  recursionKernel Γ (narmaStep G)

/-- The NARMA model is a Markov kernel. -/
theorem isMarkovKernel_narmaKernel {k l : ℕ} (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    {G : (Fin k → ℝ) × ℝ × (Fin l → ℝ) → ℝ} (hG : Measurable G) :
    IsMarkovKernel (narmaKernel Γ G) :=
  isMarkovKernel_recursionKernel Γ (measurable_narmaStep hG)

/-- ARMA(k, ℓ) is the NARMA(k, ℓ) model with the linear `G`. -/
theorem armaKernel_eq_narmaKernel {k l : ℕ} (Γ : Measure ℝ) (α : Fin k → ℝ) (β : Fin l → ℝ) :
    armaKernel Γ α β =
      narmaKernel Γ fun q => ∑ i, α i * q.1 i + q.2.1 + ∑ j, β j * q.2.2 j :=
  rfl

/-! ### The gumleaf attractor -/

/-- The gumleaf map `F(a, b) = (1/a − 1/b, a)` (MT, p. 30), with Lean's convention `1/0 = 0`. -/
noncomputable def gumleafMap (x : ℝ × ℝ) : ℝ × ℝ := (1 / x.1 - 1 / x.2, x.1)

/-- MT, p. 30: if `vₙ = 1/vₙ₋₁ − 1/vₙ₋₂` (2.10) then `xₙ = (vₙ, vₙ₋₁)` follows `xₙ = F(xₙ₋₁)`. -/
theorem gumleafMap_of_recursion (v : ℕ → ℝ) (hv : ∀ n, v (n + 2) = 1 / v (n + 1) - 1 / v n)
    (n : ℕ) : (v (n + 2), v (n + 1)) = gumleafMap (v (n + 1), v n) := by
  rw [gumleafMap, hv n]

/-- The noisy gumleaf step (2.12): `Xₙ = (1/Xᵃₙ₋₁ − 1/Xᵇₙ₋₁ + Wₙ, Xᵃₙ₋₁)`. -/
noncomputable def gumleafNoisyStep (p : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (1 / p.1.1 - 1 / p.1.2 + p.2, p.1.1)

/-- The noisy gumleaf step is measurable. -/
theorem measurable_gumleafNoisyStep : Measurable gumleafNoisyStep := by
  unfold gumleafNoisyStep
  fun_prop

/-- The gumleaf attractor perturbed by noise, (2.12) (MT, p. 31), as a Markov chain on `ℝ²`. -/
noncomputable def gumleafKernel (Γ : Measure ℝ) : Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  recursionKernel Γ gumleafNoisyStep

/-- The noisy gumleaf model is a Markov kernel. -/
theorem isMarkovKernel_gumleafKernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (gumleafKernel Γ) :=
  isMarkovKernel_recursionKernel Γ measurable_gumleafNoisyStep

/-- The Euclidean norm on `ℝ²`. -/
noncomputable def eNorm2 (z : ℝ × ℝ) : ℝ := √(z.1 ^ 2 + z.2 ^ 2)

/-- `|c z| = |c| |z|`. -/
theorem eNorm2_smul (c : ℝ) (z : ℝ × ℝ) : eNorm2 (c • z) = |c| * eNorm2 z := by
  simp only [eNorm2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show (c * z.1) ^ 2 + (c * z.2) ^ 2 = c ^ 2 * (z.1 ^ 2 + z.2 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The transformation `[z] = (1 + |z|)⁻¹ z` of MT, p. 30. -/
noncomputable def squash (z : ℝ × ℝ) : ℝ × ℝ := (1 + eNorm2 z)⁻¹ • z

/-- `|[z]| = |z| / (1 + |z|)`. -/
theorem eNorm2_squash (z : ℝ × ℝ) : eNorm2 (squash z) = eNorm2 z / (1 + eNorm2 z) := by
  have h0 : 0 ≤ eNorm2 z := Real.sqrt_nonneg _
  rw [squash, eNorm2_smul, abs_of_pos (inv_pos.mpr (by linarith)), inv_mul_eq_div]

/-- MT, p. 30: `[z]` lies in the open unit disk. -/
theorem eNorm2_squash_lt_one (z : ℝ × ℝ) : eNorm2 (squash z) < 1 := by
  have h0 : 0 ≤ eNorm2 z := Real.sqrt_nonneg _
  rw [eNorm2_squash, div_lt_one (by linarith)]
  linarith

/-- The inverse transformation `y ↦ (1 − |y|)⁻¹ y` on the open unit disk. -/
noncomputable def unsquash (y : ℝ × ℝ) : ℝ × ℝ := (1 - eNorm2 y)⁻¹ • y

/-- `[·]` is one-to-one: `unsquash [z] = z`. -/
theorem unsquash_squash (z : ℝ × ℝ) : unsquash (squash z) = z := by
  have h0 : 0 ≤ eNorm2 z := Real.sqrt_nonneg _
  have h1 : 1 - eNorm2 z / (1 + eNorm2 z) = (1 + eNorm2 z)⁻¹ := by
    field_simp
    ring
  rw [unsquash, eNorm2_squash, h1, squash, smul_smul, inv_inv, mul_inv_cancel₀ (by linarith),
    one_smul]

/-- `[·]` maps onto the open unit disk: `[unsquash y] = y` for `|y| < 1`. -/
theorem squash_unsquash {y : ℝ × ℝ} (hy : eNorm2 y < 1) : squash (unsquash y) = y := by
  have h0 : 0 ≤ eNorm2 y := Real.sqrt_nonneg _
  have hn : eNorm2 (unsquash y) = eNorm2 y / (1 - eNorm2 y) := by
    rw [unsquash, eNorm2_smul, abs_of_pos (inv_pos.mpr (by linarith)), inv_mul_eq_div]
  have hne : 1 - eNorm2 y ≠ 0 := by linarith
  have h1 : 1 + eNorm2 y / (1 - eNorm2 y) = (1 - eNorm2 y)⁻¹ := by
    field_simp
    ring
  rw [squash, hn, h1, unsquash, smul_smul, inv_inv, mul_inv_cancel₀ (by linarith), one_smul]

/-- **Corrected (2.11).** The transformed gumleaf states `[xₙ]` follow the recursion
`[xₙ] = [F(unsquash [xₙ₋₁])]`. -/
theorem squash_gumleafMap (x : ℝ × ℝ) :
    squash (gumleafMap x) = squash (gumleafMap (unsquash (squash x))) := by
  rw [unsquash_squash]

/-- **Correction to (2.11).** The printed recursion `[xₙ] = [F([xₙ₋₁])]` applies `F` to the
transformed state, and differs from the transformed chain: from `v₀ = v₁ = 1`, the true next
transformed state `[(0, 1)]` has second coordinate `1/2`, while the printed recursion gives
`1/(2 + √2)`. -/
theorem gumleaf_printed_ne :
    squash (gumleafMap (squash (1, 1))) ≠ squash (gumleafMap (1, 1)) := by
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hn11 : eNorm2 (1, 1) = √2 := by norm_num [eNorm2]
  set c : ℝ := (1 + √2)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hsq : squash (1, 1) = (c, c) := by
    simp [squash, hn11, hc]
  have hF1 : gumleafMap (c, c) = (0, c) := by simp [gumleafMap]
  have hF2 : gumleafMap (1, 1) = (0, 1) := by norm_num [gumleafMap]
  have hn0c : eNorm2 (0, c) = c := by
    simp [eNorm2, Real.sqrt_sq hcpos.le]
  have hn01 : eNorm2 ((0 : ℝ), (1 : ℝ)) = 1 := by simp [eNorm2]
  rw [hsq, hF1, hF2]
  intro h
  have h2 := congrArg Prod.snd h
  simp only [squash, Prod.smul_snd, smul_eq_mul, hn0c, hn01] at h2
  have hc1 : c ≠ 1 := by
    intro h1
    rw [hc, inv_eq_one] at h1
    linarith
  field_simp at h2
  apply hc1
  linarith

/-! ### The SETAR model -/

/-- The predicate defining the SETAR regime of `x`: the regime index `n` is `m`, or the
threshold `rₙ` satisfies `x ≤ rₙ`. -/
def setarP {m : ℕ} (r : Fin m → ℝ) (x : ℝ) (n : ℕ) : Prop := n = m ∨ ∃ h : n < m, x ≤ r ⟨n, h⟩

/-- Some index satisfies the regime predicate. -/
theorem setarP_exists {m : ℕ} (r : Fin m → ℝ) (x : ℝ) : ∃ n, setarP r x n := ⟨m, Or.inl rfl⟩

open Classical in
/-- The SETAR regime of `x` for finite thresholds `r₀ < ⋯ < r_{m−1}` (the book's `r₁, …, r_{M−1}`,
with `M = m + 1` regimes, `r₀ = −∞` and `r_M = ∞` in the book's indexing): the least `j` with
`x ≤ r_j`, or `m` if there is none. -/
noncomputable def setarRegime {m : ℕ} (r : Fin m → ℝ) (x : ℝ) : Fin (m + 1) :=
  ⟨Nat.find (setarP_exists r x), Nat.lt_succ_of_le (Nat.find_min' _ (Or.inl rfl))⟩

/-- The regime of `x` is `j` exactly when every threshold below index `j` is `< x` and the
threshold at index `j` (if any) is `≥ x`. -/
theorem setarRegime_eq_iff {m : ℕ} (r : Fin m → ℝ) (x : ℝ) (j : Fin (m + 1)) :
    setarRegime r x = j ↔
      (∀ i : Fin m, (i : ℕ) < j → r i < x) ∧ ∀ h : (j : ℕ) < m, x ≤ r ⟨j, h⟩ := by
  classical
  rw [setarRegime, Fin.ext_iff, Fin.val_mk]
  convert Nat.find_eq_iff (setarP_exists r x) using 1
  have hj := j.isLt
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun n hn hP => ?_⟩
    · by_cases hjm : (j : ℕ) = m
      · exact Or.inl hjm
      · exact Or.inr ⟨by omega, h2 (by omega)⟩
    · rcases hP with hnm | ⟨hn', hx⟩
      · omega
      · exact absurd hx (not_le.mpr (h1 ⟨n, hn'⟩ hn))
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun h => ?_⟩
    · have := h2 i hi
      simp only [setarP, not_or, not_exists, not_le] at this
      exact this.2 i.isLt
    · rcases h1 with h1 | ⟨_, hx⟩
      · omega
      · exact hx

/-- **The book's regime condition.** For increasing thresholds, the regime of `x` is `j` exactly
when `r_{j−1} < x ≤ r_j` (MT, (SETAR1), p. 28), with the conventions `r_{−1} = −∞`,
`r_m = ∞`. -/
theorem setarRegime_eq_iff_Ioc {m : ℕ} {r : Fin m → ℝ} (hr : Monotone r) (x : ℝ)
    (j : Fin (m + 1)) :
    setarRegime r x = j ↔
      (∀ h : 0 < (j : ℕ), r ⟨j - 1, by have := j.isLt; omega⟩ < x) ∧
        ∀ h : (j : ℕ) < m, x ≤ r ⟨j, h⟩ := by
  rw [setarRegime_eq_iff]
  refine and_congr_left' ⟨fun h hj => h _ (by change (j : ℕ) - 1 < j; omega), fun h i hi => ?_⟩
  have := h (by omega)
  exact lt_of_le_of_lt (hr (Fin.mk_le_mk.mpr (by omega) : i ≤ ⟨(j : ℕ) - 1, _⟩)) this

/-- The SETAR regime is a measurable function of the state. -/
theorem measurable_setarRegime {m : ℕ} (r : Fin m → ℝ) : Measurable (setarRegime r) := by
  refine measurable_to_countable' fun j => ?_
  have hset : setarRegime r ⁻¹' {j} =
      (⋂ i : Fin m, ⋂ (_ : (i : ℕ) < j), Ioi (r i)) ∩ ⋂ (h : (j : ℕ) < m), Iic (r ⟨j, h⟩) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, setarRegime_eq_iff, mem_inter_iff, mem_iInter,
      mem_Ioi, mem_Iic]
  rw [hset]
  exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_Ioi).inter
    (MeasurableSet.iInter fun _ => measurableSet_Iic)

/-- The SETAR step `F(x, w) = φ(j) + θ(j)x + w(j)` with `j` the regime of `x`; the disturbance
`w = (w(0), …, w(m))` carries one noise per regime. -/
noncomputable def setarStep {m : ℕ} (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (p : ℝ × (Fin (m + 1) → ℝ)) : ℝ :=
  φ (setarRegime r p.1) + θ (setarRegime r p.1) * p.1 + p.2 (setarRegime r p.1)

/-- The SETAR step is measurable. -/
theorem measurable_setarStep {m : ℕ} (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) :
    Measurable (setarStep φ θ r) := by
  have hreg : Measurable fun p : ℝ × (Fin (m + 1) → ℝ) => setarRegime r p.1 :=
    (measurable_setarRegime r).comp measurable_fst
  have hw : Measurable fun p : ℝ × (Fin (m + 1) → ℝ) => p.2 (setarRegime r p.1) := by
    have heq : (fun p : ℝ × (Fin (m + 1) → ℝ) => p.2 (setarRegime r p.1)) =
        fun p => ∑ j, if setarRegime r p.1 = j then p.2 j else 0 := by
      funext p
      rw [Finset.sum_ite_eq]
      simp
    rw [heq]
    refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_
      ((measurable_pi_apply j).comp measurable_snd) measurable_const
    exact hreg (measurableSet_singleton j)
  exact (((measurable_of_countable φ).comp hreg).add
    (((measurable_of_countable θ).comp hreg).mul measurable_fst)).add hw

/-- The SETAR model (MT, (SETAR1), p. 28): in regime `j` the chain moves by
`Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)`, the regime noises `Wₙ(j) ~ Γ j` being independent, so the
disturbance law is the product `⊗ⱼ Γ j`. -/
noncomputable def setarKernel {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) (φ θ : Fin (m + 1) → ℝ)
    (r : Fin m → ℝ) : Kernel ℝ ℝ :=
  recursionKernel (Measure.pi Γ) (setarStep φ θ r)

/-- The SETAR model is a Markov kernel. -/
theorem isMarkovKernel_setarKernel {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) :
    IsMarkovKernel (setarKernel Γ φ θ r) :=
  isMarkovKernel_recursionKernel _ (measurable_setarStep φ θ r)

/-- The SETAR kernel only uses the noise of the current regime:
`P(x, A) = Γ_j{w : φ(j) + θ(j)x + w ∈ A}` with `j` the regime of `x`. -/
theorem setarKernel_apply' {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    setarKernel Γ φ θ r x A =
      Γ (setarRegime r x) {w | φ (setarRegime r x) + θ (setarRegime r x) * x + w ∈ A} := by
  rw [setarKernel, recursionKernel_apply' _ (measurable_setarStep φ θ r) x hA]
  have hS : MeasurableSet {w : ℝ | φ (setarRegime r x) + θ (setarRegime r x) * x + w ∈ A} :=
    (measurable_const_add _) hA
  exact (measurePreserving_eval Γ (setarRegime r x)).measure_preimage hS.nullMeasurableSet

/-- MT, p. 28: SETAR models need not be continuous, so they are not NSS(F) models in the smooth
sense. With one threshold `r₀ = 0` and intercepts `φ = (0, 1)`, the map `x ↦ F(x, 0)` jumps at
`0`. -/
theorem setar_not_continuous :
    ¬ Continuous fun x : ℝ => setarStep (m := 1) ![0, 1] ![0, 0] ![0] (x, 0) := by
  intro hc
  have hreg0 : setarRegime (m := 1) ![0] 0 = 0 := by
    rw [setarRegime_eq_iff]
    refine ⟨fun i hi => absurd hi (by simp), fun _ => ?_⟩
    simp
  have hregpos : ∀ x : ℝ, 0 < x → setarRegime (m := 1) ![0] x = 1 := fun x hx => by
    rw [setarRegime_eq_iff]
    refine ⟨fun i _ => ?_, fun h => absurd h (by simp)⟩
    fin_cases i
    simpa using hx
  have hval0 : setarStep (m := 1) ![0, 1] ![0, 0] ![0] (0, 0) = 0 := by
    simp [setarStep, hreg0]
  have hvalpos : ∀ x : ℝ, 0 < x → setarStep (m := 1) ![0, 1] ![0, 0] ![0] (x, 0) = 1 :=
    fun x hx => by simp [setarStep, hregpos x hx]
  have hopen : IsOpen ((fun x : ℝ => setarStep (m := 1) ![0, 1] ![0, 0] ![0] (x, 0)) ⁻¹'
      Iio (1 / 2)) := isOpen_Iio.preimage hc
  have hmem : (0 : ℝ) ∈ (fun x : ℝ => setarStep (m := 1) ![0, 1] ![0, 0] ![0] (x, 0)) ⁻¹'
      Iio (1 / 2) := by
    simp only [mem_preimage, mem_Iio, hval0]
    norm_num
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  have hx : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have := hball hx
  simp only [mem_preimage, mem_Iio, hvalpos (ε / 2) (by linarith)] at this
  norm_num at this

/-! ### The simple adaptive control model -/

/-- The closed loop step of the simple adaptive control model (MT, (2.22)–(2.24), p. 36) on the
state `(Σ, θ̃, Y)` with disturbance `(Z, W)`:
`Y' = θ̃Y + W`, `θ̃' = αθ̃ − αΣY'Y(ΣY² + σ_w²)⁻¹ + Z`, `Σ' = σ_z² + α²σ_w²Σ(ΣY² + σ_w²)⁻¹`. -/
noncomputable def sacStep (α σz σw : ℝ) (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  (σz ^ 2 + α ^ 2 * σw ^ 2 * p.1.1 / (p.1.1 * p.1.2.2 ^ 2 + σw ^ 2),
    α * p.1.2.1 - α * p.1.1 * (p.1.2.1 * p.1.2.2 + p.2.2) * p.1.2.2 /
      (p.1.1 * p.1.2.2 ^ 2 + σw ^ 2) + p.2.1,
    p.1.2.1 * p.1.2.2 + p.2.2)

/-- The SAC step is measurable. -/
theorem measurable_sacStep (α σz σw : ℝ) : Measurable (sacStep α σz σw) := by
  unfold sacStep
  fun_prop

/-- The closed loop simple adaptive control model `Φₖ = (Σₖ, θ̃ₖ, Yₖ)` (MT, (2.25), p. 36) with
disturbance law `Γ` of `(Z, W)`. -/
noncomputable def sacKernel (Γ : Measure (ℝ × ℝ)) (α σz σw : ℝ) : Kernel (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) :=
  recursionKernel Γ (sacStep α σz σw)

/-- The SAC model is a Markov kernel. -/
theorem isMarkovKernel_sacKernel (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] (α σz σw : ℝ) :
    IsMarkovKernel (sacKernel Γ α σz σw) :=
  isMarkovKernel_recursionKernel Γ (measurable_sacStep α σz σw)

/-- The SAC model with the Gaussian disturbances of (SAC2): `Z ~ N(0, σ_z²)` and
`W ~ N(0, σ_w²)` independent. -/
noncomputable def sacGaussianKernel (α σz σw : ℝ) : Kernel (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) :=
  sacKernel ((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) α σz σw

/-- The Gaussian SAC model is a Markov kernel. -/
theorem isMarkovKernel_sacGaussianKernel (α σz σw : ℝ) :
    IsMarkovKernel (sacGaussianKernel α σz σw) :=
  isMarkovKernel_sacKernel _ α σz σw

/-- **The closed loop equations** (MT, pp. 35–36). Given the open loop model (2.20)–(2.21),
`Y' = θY + U + W` and `θ' = αθ + Z`, the Kalman filter update
`θ̂' = αθ̂ + αΣ(Y' − θ̂Y − U)Y(ΣY² + σ_w²)⁻¹`, and the certainty equivalence control `U = −θ̂Y`,
the estimation error `θ̃ = θ − θ̂` satisfies (2.22)–(2.23). -/
theorem sac_closed_loop (α σw θ θhat Y S Z W : ℝ) :
    let U := -θhat * Y
    let Y' := θ * Y + U + W
    let θ' := α * θ + Z
    let θhat' := α * θhat + α * S * (Y' - θhat * Y - U) * Y / (S * Y ^ 2 + σw ^ 2)
    Y' = (θ - θhat) * Y + W ∧
      θ' - θhat' = α * (θ - θhat) - α * S * Y' * Y / (S * Y ^ 2 + σw ^ 2) + Z := by
  intro U Y' θ' θhat'
  refine ⟨by simp only [Y', U]; ring, ?_⟩
  simp only [θ', θhat', Y', U]
  ring

/-- **Invariance of the `Σ` interval** (MT, p. 36). If `|α| < 1`, `σ_w ≠ 0` and
`Σ ∈ [σ_z², σ_z²/(1 − α²)]`, then `Σ' ∈ [σ_z², σ_z²/(1 − α²)]`. -/
theorem sacStep_sigma_mem {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) {S th Y : ℝ}
    (hS : S ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))) (z : ℝ × ℝ) :
    (sacStep α σz σw ((S, th, Y), z)).1 ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) := by
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have h1 : 0 < 1 - α ^ 2 := by linarith
  have hS0 : 0 ≤ S := le_trans (sq_nonneg σz) hS.1
  have hw2 : 0 < σw ^ 2 := by positivity
  have hD : 0 < S * Y ^ 2 + σw ^ 2 := by positivity
  simp only [sacStep]
  constructor
  · have : 0 ≤ α ^ 2 * σw ^ 2 * S / (S * Y ^ 2 + σw ^ 2) := by positivity
    linarith
  · have hle : α ^ 2 * σw ^ 2 * S / (S * Y ^ 2 + σw ^ 2) ≤ α ^ 2 * S := by
      rw [div_le_iff₀ hD]
      have : 0 ≤ α ^ 2 * S * (S * Y ^ 2) := by positivity
      nlinarith
    have hS2 : α ^ 2 * S ≤ α ^ 2 * (σz ^ 2 / (1 - α ^ 2)) :=
      mul_le_mul_of_nonneg_left hS.2 (sq_nonneg α)
    have heq : σz ^ 2 + α ^ 2 * (σz ^ 2 / (1 - α ^ 2)) = σz ^ 2 / (1 - α ^ 2) := by
      field_simp
      ring
    linarith

/-- MT, p. 36: the closed loop chain lives on `X = [σ_z², σ_z²/(1 − α²)] × ℝ²`: from a state in
`X`, the next state is in `X` with probability one. -/
theorem sacKernel_apply_Icc (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) {S th Y : ℝ}
    (hS : S ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))) :
    sacKernel Γ α σz σw (S, th, Y) (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ) = 1 := by
  rw [sacKernel, recursionKernel_apply' Γ (measurable_sacStep α σz σw) _
    (measurableSet_Icc.prod MeasurableSet.univ)]
  have : {w : ℝ × ℝ | sacStep α σz σw ((S, th, Y), w) ∈
      Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ (univ : Set (ℝ × ℝ))} = univ := by
    ext w
    simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true, iff_true]
    exact sacStep_sigma_mem hα hσw hS w
  rw [this, measure_univ]

/-- MT, p. 36: with `α = 1`, `σ_w = 1` and `σ_z = 0`, the variance recursion is that of
recursive least squares, `Σₖ₊₁⁻¹ = Σₖ⁻¹ + Yₖ²`. -/
theorem sac_rls {S : ℝ} (hS : 0 < S) (th Y : ℝ) (z : ℝ × ℝ) :
    ((sacStep 1 0 1 ((S, th, Y), z)).1)⁻¹ = S⁻¹ + Y ^ 2 := by
  simp only [sacStep]
  have hD : 0 < S * Y ^ 2 + 1 := by positivity
  field_simp
  ring

/-! ### Random coefficient autoregression -/

/-- The RCA step `x ↦ (A + Γ)x + W` (MT, p. 550). -/
def rcaStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (p : (Fin n → ℝ) × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ))) : Fin n → ℝ :=
  (A + p.2.1) *ᵥ p.1 + p.2.2

/-- The RCA step is measurable. -/
theorem measurable_rcaStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Measurable (rcaStep A) := by
  unfold rcaStep
  fun_prop

/-- The random coefficient autoregression `Xₖ₊₁ = (A + Γₖ₊₁)Xₖ + Wₖ₊₁` (MT, (RCA1), p. 551): the
coefficient noise `Γ` and the additive noise `W` are i.i.d. and independent, with laws `ΓΓ`
and `ΓW`. -/
noncomputable def rcaKernel {n : ℕ} (ΓΓ : Measure (Matrix (Fin n) (Fin n) ℝ))
    (ΓW : Measure (Fin n → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ) :
    Kernel (Fin n → ℝ) (Fin n → ℝ) :=
  recursionKernel (ΓΓ.prod ΓW) (rcaStep A)

/-- The RCA model is a Markov kernel. -/
theorem isMarkovKernel_rcaKernel {n : ℕ} (ΓΓ : Measure (Matrix (Fin n) (Fin n) ℝ))
    (ΓW : Measure (Fin n → ℝ)) [IsProbabilityMeasure ΓΓ] [IsProbabilityMeasure ΓW]
    (A : Matrix (Fin n) (Fin n) ℝ) : IsMarkovKernel (rcaKernel ΓΓ ΓW A) :=
  isMarkovKernel_recursionKernel _ (measurable_rcaStep A)

/-- With no coefficient noise (`Γ = 0` almost surely), RCA is LSS(A, I). -/
theorem rcaKernel_dirac_zero {n : ℕ} (ΓW : Measure (Fin n → ℝ)) [SFinite ΓW]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rcaKernel (Measure.dirac 0) ΓW A = lssMatrixKernel ΓW A 1 := by
  rw [rcaKernel, Measure.dirac_prod,
    ← recursionKernel_comp_noise ΓW (measurable_rcaStep A) measurable_prodMk_left, lssMatrixKernel]
  congr 1
  funext p
  simp [rcaStep]

end MeynTweedie.InvarianceTightness
