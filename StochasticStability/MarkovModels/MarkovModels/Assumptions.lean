/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovModels.NonlinearModels
import MarkovModels.Storage
import MarkovModels.Renewal
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Appendix C: the glossary of model assumptions

MT, Appendix C, pp. 543–551. The models themselves are defined as kernels in the other modules of
this project; this module collects the further assumptions the book imposes on them, as
predicates on the model data, with a few consequences.

**C.1 Regenerative models.** (RT1)–(RT4): `forwardKernel`, `backwardKernel`, `fwdTime`,
`bwdTime`, `fwdTimeCts`, `bwdTimeCts`, `fwdSkeleton`, `bwdSkeleton` (`Renewal`). (RW1), (RW2),
(RWHL1): `randomWalkKernel`, `IsSpreadOut`, `halfLineWalkKernel` (`RandomWalk`). (Q1)–(Q3):
`waitingTimeKernel` (`Queues`); (Q4) `IsGIM1Service`, (Q5) `IsMG1Arrivals`, with the distribution
functions `1 − e^{−μt}` (`cdf_of_isGIM1Service`). (SSM1)–(SSM2): `storageKernel`; (CSM1)–(CSM2):
`contentKernel` (`Storage`).

**C.2 State space models.** (SLM): `ar1Kernel`; (LSS1) `lssKernel`, `lssMatrixKernel`;
(LSS2) `HasFiniteMeanVariance`; (LSS3) `IsStdGaussianNoise`; (LSS4) `IsNonsingularNoise`;
(LSS5) `HasStableEigenvalues`; (LCM1)–(LCM2) `lcmTrajectory`; (AR), (ARMA): `arKernel`,
`armaKernel` (`LinearModels`). (DS1)–(DS2): `IsSemiDynamicalSystem`, `SatisfiesDS2`. (SNSS1),
(NSS1): `nssKernel` with `IsSmoothModel`; (SNSS2), (NSS2): `HasDensityOnControlSet`; (SNSS3),
(NSS3): `HasLscDensity`, whose control set `{γ > 0}` is open (`isOpen_controlSet`). (CM1):
`controlMap`; (CM2) `SatisfiesCM2`; (CM3) `SatisfiesCM3`. (NARMA): `narmaKernel`. (SAC1)–(SAC3):
`sacKernel`, `sacGaussianKernel`, `SatisfiesSAC2`. (SETAR1)–(SETAR3): `setarKernel`,
`SatisfiesSETAR1Noise`, `SatisfiesSETAR2`, `SatisfiesSETAR3`. (SBL1)–(SBL2): `bilinearKernel`,
`SatisfiesSBL2`. (DBL1)–(DBL2): `dblKernel`, `SatisfiesDBL2`. (RCA1)–(RCA3): `rcaKernel`,
`SatisfiesRCA2`, `SatisfiesRCA3` (`NonlinearModels`).

**Notes on the text.** (LSS2) asks for a finite mean in Appendix C but for a finite mean and
variance in §1.2.2 (p. 9); `HasFiniteMeanVariance` is the stronger form. (CM2) and (CM3) say
"for each initial condition `x₀⁰ ∈ ℝ`" also in the multidimensional case; the state space `X` is
meant.
-/

namespace MeynTweedie.MarkovModels

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ContDiff Matrix

/-! ### C.1 Regenerative models -/

/-- (Q4), MT p. 545: exponential service times, `H(−∞, t] = 1 − e^{−μt}`: a GI/M/1 queue. -/
def IsGIM1Service (H : Measure ℝ) : Prop := ∃ μ : ℝ, 0 < μ ∧ H = expMeasure μ

/-- (Q5), MT p. 545: exponential interarrival times, `G(−∞, t] = 1 − e^{−λt}`: an M/G/1
queue. -/
def IsMG1Arrivals (G : Measure ℝ) : Prop := ∃ lam : ℝ, 0 < lam ∧ G = expMeasure lam

/-- Under (Q4) the service distribution function is `H(−∞, t] = 1 − e^{−μt}` for `t ≥ 0`. -/
theorem cdf_of_isGIM1Service {μ : ℝ} (hμ : 0 < μ) {t : ℝ} (ht : 0 ≤ t) :
    cdf (expMeasure μ) t = 1 - Real.exp (-(μ * t)) := by
  rw [cdf_expMeasure_eq hμ, ite_eq_left ht]

/-! ### C.2.1 Linear models -/

/-- (LSS2), MT pp. 9 and 546: the noise has finite mean and variance (finite second moment). -/
def HasFiniteMeanVariance {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    (Γ : Measure V) : Prop :=
  MemLp id 2 Γ

/-- (LSS3), MT p. 546: `W ~ N(0, I)` on `ℝᵖ`. -/
def IsStdGaussianNoise {p : ℕ} (Γ : Measure (Fin p → ℝ)) : Prop :=
  Γ = Measure.pi fun _ => gaussianReal 0 1

/-- (LSS4), MT p. 546: the noise law is not singular with respect to Lebesgue measure. -/
def IsNonsingularNoise {p : ℕ} (Γ : Measure (Fin p → ℝ)) : Prop :=
  ¬ Γ ⟂ₘ (volume : Measure (Fin p → ℝ))

/-- (LSS5), MT p. 546: the eigenvalues of `F` lie in the open unit disk of `ℂ`. -/
def HasStableEigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (F.map (algebraMap ℝ ℂ)), ‖μ‖ < 1

/-- Under (LSS3) the LSS(F, G) model is a Markov kernel. -/
theorem isMarkovKernel_lssMatrixKernel_of_stdGaussian {n p : ℕ} {Γ : Measure (Fin p → ℝ)}
    (hΓ : IsStdGaussianNoise Γ) (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    IsMarkovKernel (lssMatrixKernel Γ F G) := by
  rw [hΓ]
  exact isMarkovKernel_lssMatrixKernel _ F G

/-! ### C.2.2 Nonlinear models -/

/-- (DS1), MT p. 547: a semi-dynamical system `Φₖ₊₁ = F(Φₖ)` with `F` continuous. -/
def IsSemiDynamicalSystem {Y : Type*} [TopologicalSpace Y] (F : Y → Y) : Prop := Continuous F

/-- (DS2), MT p. 547: a positive function `V`, a compact set `C` and `M < ∞` with
`V(F(x)) − V(x) ≤ −1` off `C` and `sup_{x ∈ C} V(F(x)) ≤ M`. -/
def SatisfiesDS2 {Y : Type*} [TopologicalSpace Y] (F : Y → Y) : Prop :=
  ∃ (V : Y → ℝ) (C : Set Y) (M : ℝ), (∀ x, 0 < V x) ∧ IsCompact C ∧
    (∀ x ∉ C, V (F x) - V x ≤ -1) ∧ ∀ x ∈ C, V (F x) ≤ M

/-- (SNSS1), (NSS1), MT pp. 547–548: the model map `F` is smooth (`C^∞`). -/
def IsSmoothModel {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (F : E × V → E) : Prop :=
  ContDiff ℝ ∞ F

/-- (SNSS2), (NSS2), MT p. 548: the noise law has a density `γ` supported on the open control set
`O = {γ > 0}`. -/
def HasDensityOnControlSet {p : ℕ} (Γ : Measure (Fin p → ℝ)) (γ : (Fin p → ℝ) → ℝ≥0∞)
    (O : Set (Fin p → ℝ)) : Prop :=
  Γ = volume.withDensity γ ∧ IsOpen O ∧ ∀ w, 0 < γ w ↔ w ∈ O

/-- (SNSS3), (NSS3), MT p. 548: the noise law has a lower semicontinuous density. -/
def HasLscDensity {p : ℕ} (Γ : Measure (Fin p → ℝ)) (γ : (Fin p → ℝ) → ℝ≥0∞) : Prop :=
  Γ = volume.withDensity γ ∧ LowerSemicontinuous γ

/-- (NSS3), MT p. 548: with a lower semicontinuous density the control set `{γ > 0}` is open, so
(NSS3) implies (NSS2). -/
theorem isOpen_controlSet {p : ℕ} {γ : (Fin p → ℝ) → ℝ≥0∞} (hγ : LowerSemicontinuous γ) :
    IsOpen {w | 0 < γ w} :=
  hγ.isOpen_preimage 0

/-- (NSS3) implies (NSS2) with control set `{γ > 0}`. -/
theorem hasDensityOnControlSet_of_lsc {p : ℕ} {Γ : Measure (Fin p → ℝ)}
    {γ : (Fin p → ℝ) → ℝ≥0∞} (h : HasLscDensity Γ γ) :
    HasDensityOnControlSet Γ γ {w | 0 < γ w} :=
  ⟨h.1, isOpen_controlSet h.2, fun _ => Iff.rfl⟩

/-- (CM2), MT p. 548, for the scalar model: from every initial condition some control sequence
in `O` makes the derivative of `Fₖ` with respect to the controls non-zero. -/
def SatisfiesCM2 (F : ℝ × ℝ → ℝ) (O : Set ℝ) : Prop :=
  ∀ x₀ : ℝ, ∃ (k : ℕ) (u : Fin k → ℝ), (∀ i, u i ∈ O) ∧ fderiv ℝ (controlMap F k x₀) u ≠ 0

/-- (CM3), MT p. 549: from every initial condition some control sequence in `O` gives a
controllability matrix `C_{x}^k(u) = [∂Fₖ/∂u₁ | ⋯ | ∂Fₖ/∂uₖ]` of rank `n`. -/
def SatisfiesCM3 {n p : ℕ} (F : (Fin n → ℝ) × (Fin p → ℝ) → (Fin n → ℝ))
    (O : Set (Fin p → ℝ)) : Prop :=
  ∀ x₀ : Fin n → ℝ, ∃ (k : ℕ) (u : Fin k → Fin p → ℝ), (∀ i, u i ∈ O) ∧
    Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (controlMap F k x₀) u : (Fin k → Fin p → ℝ) →ₗ[ℝ] (Fin n → ℝ))) = n

/-! ### C.2.3 Particular examples -/

/-- (SAC2), MT pp. 35 and 549: the parameter noise variance satisfies `σ_z < 1` and the noises
are non-degenerate. -/
def SatisfiesSAC2 (σz σw : ℝ) : Prop := 0 < σz ∧ σz < 1 ∧ 0 < σw

/-- The zero-mean condition on the regime noises in (SETAR1), MT p. 550. -/
def SatisfiesSETAR1Noise {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) : Prop :=
  ∀ j, Integrable id (Γ j) ∧ ∫ w, w ∂(Γ j) = 0

/-- (SETAR2), MT p. 550: each regime noise has a density positive on the whole line. -/
def SatisfiesSETAR2 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) : Prop :=
  ∀ j, ∃ γ : ℝ → ℝ≥0∞, Γ j = volume.withDensity γ ∧ ∀ w, 0 < γ w

/-- (SETAR3), MT p. 550: the noises of the two end regimes have finite variance. -/
def SatisfiesSETAR3 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) : Prop :=
  MemLp id 2 (Γ 0) ∧ MemLp id 2 (Γ (Fin.last m))

/-- (SBL2), MT p. 550: finite second moment and a lower semicontinuous density. -/
def SatisfiesSBL2 (Γ : Measure ℝ) : Prop :=
  MemLp id 2 Γ ∧ ∃ γ : ℝ → ℝ≥0∞, Γ = volume.withDensity γ ∧ LowerSemicontinuous γ

/-- (DBL2), MT pp. 32 and 550: `Z` and `W` have lower semicontinuous densities, `W` has a finite
second moment and `E[log(1 + |Z|)] < ∞`. (Independence is built into `dblKernel`.) -/
def SatisfiesDBL2 (Γz Γw : Measure ℝ) : Prop :=
  (∃ γ : ℝ → ℝ≥0∞, Γz = volume.withDensity γ ∧ LowerSemicontinuous γ) ∧
    (∃ γ : ℝ → ℝ≥0∞, Γw = volume.withDensity γ ∧ LowerSemicontinuous γ) ∧
    MemLp id 2 Γw ∧ Integrable (fun z => Real.log (1 + |z|)) Γz

/-- (RCA2), MT p. 551: `E[W] = 0`, `E[WWᵀ] = G`, `E[Γ] = 0`, `E[Γ ⊗ Γ] = C`, and the eigenvalues
of `A ⊗ A + C` lie in the open unit disk. -/
def SatisfiesRCA2 {n : ℕ} (ΓΓ : Measure (Matrix (Fin n) (Fin n) ℝ)) (ΓW : Measure (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) : Prop :=
  (∀ i, ∫ w, w i ∂ΓW = 0) ∧ (∀ i j, ∫ w, w i * w j ∂ΓW = G i j) ∧
    (∀ i j, ∫ M, M i j ∂ΓΓ = 0) ∧
    (∀ i j k l, ∫ M, M i j * M k l ∂ΓΓ = C (i, k) (j, l)) ∧
    HasStableEigenvalues (Matrix.kroneckerMap (· * ·) A A + C)

/-- (RCA3), MT p. 551: the joint law of `(Γₖ, Wₖ)` has an everywhere positive density with
respect to Lebesgue measure on `ℝ^{n² + n}`. -/
def SatisfiesRCA3 {n : ℕ} (ΓΓ : Measure (Matrix (Fin n) (Fin n) ℝ)) (ΓW : Measure (Fin n → ℝ)) :
    Prop :=
  ∃ γ : (Fin n → Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞, (∀ z, 0 < γ z) ∧
    (ΓΓ.prod ΓW).map (fun q => (Matrix.of.symm q.1, q.2)) = volume.withDensity γ

end MeynTweedie.MarkovModels
