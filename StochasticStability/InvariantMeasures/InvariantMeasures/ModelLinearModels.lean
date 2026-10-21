/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.ModelRandomWalk
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-!
# Linear models

Copied from the `MarkovModels` project (MT Chapters 1–2), with the namespace renamed, for
the model examples of Chapter 4.

MT, §1.2.2, pp. 7–10, §2.1, pp. 22–25, and (SLM), (LSS), (LCM), (AR), (ARMA) of Appendix C,
pp. 546–547.

* `linear_controlMap`: for any additive step `F(x, w) = A x + B w`, the closed form
  `Fₙ(x₀, u) = Aⁿ x₀ + Σᵢ Aⁿ⁻¹⁻ⁱ B uᵢ`; `orbit_linear` is MT's
  `Xₖ = Fᵏ x₀ + Σⱼ Fᵏ⁻ʲ G Wⱼ` (MT, p. 9 and (LSS1)).
* `lssKernel Γ F G`: the linear state space model LSS(F, G), `Xₖ₊₁ = F Xₖ + G Wₖ₊₁`, with `F`, `G`
  continuous linear maps between second-countable Borel normed spaces (for instance
  `EuclideanSpace ℝ (Fin n)`). `lssMatrixKernel Γ F G` is the same model with an `n × n` matrix `F`
  and an `n × p` matrix `G` on `ℝⁿ = Fin n → ℝ` (MT, (LSS1), p. 9). Both are Markov kernels, and
  their `n`-step laws are the laws of the closed form (`lssMatrixKernel_pow_apply`).
* `lcmTrajectory F G`: the deterministic linear control model LCM(F, G) (MT, (1.4), p. 9), and
  `IsControllable F G` (MT, §1.3.1, p. 14).
* `ar1Kernel Γ α`: the simple linear (AR(1)) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` (MT, (SLM1), p. 23). It is
  LSS(α, 1) (`ar1Kernel_eq_lssKernel`) and random walk when `α = 1`
  (`ar1Kernel_one`); random walk is LSS(1, 1) (`randomWalkKernel_eq_lssKernel`, MT, p. 12).
* `arStep α`, `arKernel Γ α`: the AR(k) model on `Xₙ = (Yₙ, …, Yₙ₋ₖ₊₁)` (MT, (AR1), p. 24);
  `arStep_eq_companion` is the state space form (2.1), p. 25, and
  `arKernel_eq_lssMatrixKernel` makes AR(k) an LSS model. `arVec_succ` shows the vector of
  lagged values of any AR(k) sample path follows the recursion.
* `armaStep`, `armaKernel`: the ARMA(k, ℓ) model in the state
  `Xₙ = (Yₙ, …, Yₙ₋ₖ₊₁, Wₙ, …, Wₙ₋ℓ₊₁)` (MT, (ARMA1), p. 25). `arma_of_ar` is MT's
  "simple algebra and an inductive argument" (p. 25): if `Z` follows the AR(k) recursion (2.2)
  then `Yₙ = Zₙ + Σ βⱼ Zₙ₋ⱼ` follows the ARMA(k, ℓ) recursion.
* Figure 1.1 (MT, p. 8): for `F = I + ΔA`, `A = [[−0.2, 1], [−1, −0.2]]`, `Δ = 0.02`,
  `|F x|² = 0.992416 |x|²` (`fig11_sqNorm_mulVec`), so trajectories of `xₖ₊₁ = F xₖ` spiral in
  to `0` (`fig11_tendsto_zero`) and those of `xₖ₊₁ = F⁻¹ xₖ` spiral out
  (`fig11_inv_tendsto_atTop`).
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Matrix

/-! ### The closed form of a linear recursion -/

/-- **Closed form of a linear recursion.** For an additive step `F(x, w) = A x + B w`,
`Fₙ(x₀, u₁, …, uₙ) = Aⁿ x₀ + Σ_{i < n} Aⁿ⁻¹⁻ⁱ B uᵢ₊₁`. -/
theorem linear_controlMap {E V : Type*} [AddCommMonoid E] (A : E →+ E) (B : V → E) (n : ℕ)
    (x : E) (u : Fin n → V) :
    controlMap (fun p : E × V => A p.1 + B p.2) n x u =
      (⇑A)^[n] x + ∑ i : Fin n, (⇑A)^[n - 1 - i] (B (u i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [controlMap_succ, ih, map_add, map_sum, Fin.sum_univ_castSucc, ← add_assoc,
      Function.iterate_succ_apply']
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Function.iterate_succ_apply' (⇑A)]
      congr 2
      simp only [Fin.val_castSucc]
      have := i.isLt
      omega
    · simp

/-- MT, (LSS1), p. 9: the sample path of a linear recursion is
`Xₙ = Aⁿ x₀ + Σ_{j=1}^{n} Aⁿ⁻ʲ B ωⱼ`. -/
theorem orbit_linear {E V : Type*} [AddCommMonoid E] (A : E →+ E) (B : V → E) (x : E)
    (ω : ℕ → V) (n : ℕ) :
    orbit (fun p : E × V => A p.1 + B p.2) x ω n =
      (⇑A)^[n] x + ∑ j ∈ Finset.range n, (⇑A)^[n - 1 - j] (B (ω (j + 1))) := by
  rw [orbit_eq_controlMap, linear_controlMap,
    Fin.sum_univ_eq_sum_range (fun j => (⇑A)^[n - 1 - j] (B (ω (j + 1))))]

/-! ### The linear state space model LSS(F, G) -/

/-- The linear state space model LSS(F, G) (MT, (LSS1), p. 9): `Xₖ₊₁ = F Xₖ + G Wₖ₊₁` with
`F : E → E` and `G : V → E` continuous linear maps and disturbance law `Γ` on `V`. -/
noncomputable def lssKernel {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (Γ : Measure V) (F : E →L[ℝ] E) (G : V →L[ℝ] E) : Kernel E E :=
  recursionKernel Γ fun p => F p.1 + G p.2

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The LSS step `(x, w) ↦ F x + G w` is measurable. -/
theorem measurable_lssStep (F : E →L[ℝ] E) (G : V →L[ℝ] E) :
    Measurable fun p : E × V => F p.1 + G p.2 :=
  (F.continuous.measurable.comp measurable_fst).add (G.continuous.measurable.comp measurable_snd)

/-- `P(x, A) = Γ{w : F x + G w ∈ A}` for LSS(F, G). -/
theorem lssKernel_apply' (Γ : Measure V) [SFinite Γ] (F : E →L[ℝ] E) (G : V →L[ℝ] E) (x : E)
    {A : Set E} (hA : MeasurableSet A) : lssKernel Γ F G x A = Γ {w | F x + G w ∈ A} :=
  recursionKernel_apply' Γ (measurable_lssStep F G) x hA

/-- LSS(F, G) is a Markov kernel. -/
theorem isMarkovKernel_lssKernel (Γ : Measure V) [IsProbabilityMeasure Γ] (F : E →L[ℝ] E)
    (G : V →L[ℝ] E) : IsMarkovKernel (lssKernel Γ F G) :=
  isMarkovKernel_recursionKernel Γ (measurable_lssStep F G)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace V]
  [BorelSpace V] in
/-- Powers of a continuous linear map act as iterates. -/
theorem clm_pow_apply (F : E →L[ℝ] E) (n : ℕ) (x : E) : (F ^ n) x = (⇑F)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change F ((F ^ n) x) = _
    rw [ih, Function.iterate_succ_apply']

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace V]
  [BorelSpace V] in
/-- **Closed form for LSS(F, G)** (MT, p. 9): `Xₙ = Fⁿ x₀ + Σ_{j=1}^{n} Fⁿ⁻ʲ G Wⱼ`. -/
theorem orbit_lss (F : E →L[ℝ] E) (G : V →L[ℝ] E) (x : E) (ω : ℕ → V) (n : ℕ) :
    orbit (fun p : E × V => F p.1 + G p.2) x ω n =
      (F ^ n) x + ∑ j ∈ Finset.range n, (F ^ (n - 1 - j)) (G (ω (j + 1))) := by
  have h := orbit_linear (F : E →+ E) G x ω n
  simp only [AddMonoidHom.coe_coe] at h
  rw [h, clm_pow_apply]
  simp only [clm_pow_apply]

/-- **The `n`-step law of LSS(F, G)**: `Pⁿ(x, ·)` is the law of
`Fⁿ x + Σ_{i < n} Fⁿ⁻¹⁻ⁱ G Wᵢ₊₁` under the product law of the disturbances. -/
theorem lssKernel_pow_apply (Γ : Measure V) [IsProbabilityMeasure Γ] (F : E →L[ℝ] E)
    (G : V →L[ℝ] E) (n : ℕ) (x : E) :
    (lssKernel Γ F G ^ n) x = (Measure.pi fun _ : Fin n => Γ).map
      (fun u => (F ^ n) x + ∑ i : Fin n, (F ^ (n - 1 - i)) (G (u i))) := by
  rw [lssKernel, recursionKernel_pow_apply Γ (measurable_lssStep F G)]
  congr 1
  funext u
  have h := linear_controlMap (F : E →+ E) G n x u
  simp only [AddMonoidHom.coe_coe] at h
  rw [h, clm_pow_apply]
  simp only [clm_pow_apply]

/-! ### Matrix form on `ℝⁿ` -/

/-- Multiplication by a matrix is measurable. -/
theorem measurable_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    Measurable fun x : Fin n → ℝ => M *ᵥ x :=
  (continuous_const.matrix_mulVec continuous_id).measurable

/-- The LSS(F, G) model with an `n × n` matrix `F` and an `n × p` matrix `G` on `ℝⁿ`
(MT, (LSS1), p. 9). -/
noncomputable def lssMatrixKernel {n p : ℕ} (Γ : Measure (Fin p → ℝ))
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Kernel (Fin n → ℝ) (Fin n → ℝ) :=
  recursionKernel Γ fun q => F *ᵥ q.1 + G *ᵥ q.2

/-- The matrix LSS step is measurable. -/
theorem measurable_lssMatrixStep {n p : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) :
    Measurable fun q : (Fin n → ℝ) × (Fin p → ℝ) => F *ᵥ q.1 + G *ᵥ q.2 :=
  ((measurable_mulVec F).comp measurable_fst).add ((measurable_mulVec G).comp measurable_snd)

/-- The matrix LSS(F, G) model is a Markov kernel. -/
theorem isMarkovKernel_lssMatrixKernel {n p : ℕ} (Γ : Measure (Fin p → ℝ))
    [IsProbabilityMeasure Γ] (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    IsMarkovKernel (lssMatrixKernel Γ F G) :=
  isMarkovKernel_recursionKernel Γ (measurable_lssMatrixStep F G)

/-- Multiplication by a matrix as an additive map. -/
def mulVecHom {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) : (Fin p → ℝ) →+ (Fin n → ℝ) where
  toFun x := M *ᵥ x
  map_zero' := Matrix.mulVec_zero M
  map_add' := Matrix.mulVec_add M

/-- The underlying function of `mulVecHom M` is `x ↦ M x`. -/
@[simp] theorem coe_mulVecHom {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :
    ⇑(mulVecHom M) = fun x => M *ᵥ x := rfl

/-- Matrix powers act as iterates of `x ↦ F x`. -/
theorem matrix_pow_mulVec {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (x : Fin n → ℝ) :
    (F ^ k) *ᵥ x = (fun y => F *ᵥ y)^[k] x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Function.iterate_succ_apply']

/-- **Closed form for the matrix LSS(F, G)** (MT, p. 9). -/
theorem orbit_lssMatrix {n p : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (x : Fin n → ℝ) (ω : ℕ → Fin p → ℝ) (k : ℕ) :
    orbit (fun q : (Fin n → ℝ) × (Fin p → ℝ) => F *ᵥ q.1 + G *ᵥ q.2) x ω k =
      (F ^ k) *ᵥ x + ∑ j ∈ Finset.range k, (F ^ (k - 1 - j) * G) *ᵥ ω (j + 1) := by
  have h := orbit_linear (mulVecHom F) (G *ᵥ ·) x ω k
  simp only [coe_mulVecHom] at h
  rw [h, matrix_pow_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mulVec_mulVec, matrix_pow_mulVec]

/-- **The `n`-step law of the matrix LSS(F, G) model.** -/
theorem lssMatrixKernel_pow_apply {n p : ℕ} (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (x : Fin n → ℝ) :
    (lssMatrixKernel Γ F G ^ k) x = (Measure.pi fun _ : Fin k => Γ).map
      (fun u => (F ^ k) *ᵥ x + ∑ i : Fin k, (F ^ (k - 1 - i) * G) *ᵥ u i) := by
  rw [lssMatrixKernel, recursionKernel_pow_apply Γ (measurable_lssMatrixStep F G)]
  congr 1
  funext u
  have h := linear_controlMap (mulVecHom F) (G *ᵥ ·) k x u
  simp only [coe_mulVecHom] at h
  rw [h, matrix_pow_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mulVec_mulVec, matrix_pow_mulVec]

/-! ### The deterministic linear control model LCM(F, G) -/

/-- The linear control model LCM(F, G) (MT, (LCM1)–(LCM2), (1.4), p. 9): the deterministic
trajectory `xₖ₊₁ = F xₖ + G uₖ₊₁` driven by a control sequence `u₁, …, uₖ`. It is the control
map of the LSS(F, G) step. -/
def lcmTrajectory {n p : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x₀ : Fin n → ℝ) (u : Fin k → Fin p → ℝ) : Fin n → ℝ :=
  controlMap (fun q : (Fin n → ℝ) × (Fin p → ℝ) => F *ᵥ q.1 + G *ᵥ q.2) k x₀ u

/-- MT, §1.3.1, p. 14: LCM(F, G) is *controllable* if every state can be steered to every other
state in finitely many steps. -/
def IsControllable {n p : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Prop :=
  ∀ x₀ x : Fin n → ℝ, ∃ (m : ℕ) (u : Fin m → Fin p → ℝ), lcmTrajectory F G m x₀ u = x

/-- The closed form of the LCM(F, G) trajectory: `xₖ = Fᵏ x₀ + Σᵢ Fᵏ⁻¹⁻ⁱ G uᵢ₊₁`. -/
theorem lcmTrajectory_eq {n p : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x₀ : Fin n → ℝ) (u : Fin k → Fin p → ℝ) :
    lcmTrajectory F G k x₀ u = (F ^ k) *ᵥ x₀ + ∑ i : Fin k, (F ^ (k - 1 - i) * G) *ᵥ u i := by
  have h := linear_controlMap (mulVecHom F) (G *ᵥ ·) k x₀ u
  simp only [coe_mulVecHom] at h
  rw [lcmTrajectory, h, matrix_pow_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mulVec_mulVec, matrix_pow_mulVec]

/-! ### The simple linear model AR(1) -/

/-- The simple linear model, or AR(1) model (MT, (SLM1)–(SLM2), p. 23):
`Xₙ₊₁ = αXₙ + Wₙ₊₁` with error law `Γ`. -/
noncomputable def ar1Kernel (Γ : Measure ℝ) (α : ℝ) : Kernel ℝ ℝ :=
  recursionKernel Γ fun p => α * p.1 + p.2

/-- The AR(1) step is measurable. -/
theorem measurable_ar1Step (α : ℝ) : Measurable fun p : ℝ × ℝ => α * p.1 + p.2 :=
  (measurable_const.mul measurable_fst).add measurable_snd

/-- The AR(1) model is a Markov kernel. -/
theorem isMarkovKernel_ar1Kernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ) :
    IsMarkovKernel (ar1Kernel Γ α) :=
  isMarkovKernel_recursionKernel Γ (measurable_ar1Step α)

/-- `P(x, A) = Γ{w : αx + w ∈ A}` for AR(1). -/
theorem ar1Kernel_apply' (Γ : Measure ℝ) [SFinite Γ] (α x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : ar1Kernel Γ α x A = Γ {w | α * x + w ∈ A} :=
  recursionKernel_apply' Γ (measurable_ar1Step α) x hA

/-- MT, p. 23: the simple linear model is the scalar LSS(F, G) model with `F = α`, `G = 1`. -/
theorem ar1Kernel_eq_lssKernel (Γ : Measure ℝ) (α : ℝ) :
    ar1Kernel Γ α = lssKernel Γ (α • ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) := by
  simp [ar1Kernel, lssKernel]

/-- MT, p. 23: the simple linear model extends random walk, which is the case `α = 1`. -/
theorem ar1Kernel_one (Γ : Measure ℝ) : ar1Kernel Γ 1 = randomWalkKernel Γ := by
  simp only [ar1Kernel, randomWalkKernel, one_mul]

/-- MT, p. 12: random walk on `ℝ` is the one-dimensional LSS(F, G) model with `F = G = 1`. -/
theorem randomWalkKernel_eq_lssKernel (Γ : Measure ℝ) :
    randomWalkKernel Γ = lssKernel Γ (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) := by
  rw [← ar1Kernel_one, ar1Kernel_eq_lssKernel, one_smul]

/-- The AR(1) sample path: `Xₙ = αⁿ x₀ + Σ_{j=1}^{n} αⁿ⁻ʲ Wⱼ`. -/
theorem orbit_ar1 (α x : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    orbit (fun p : ℝ × ℝ => α * p.1 + p.2) x ω n =
      α ^ n * x + ∑ j ∈ Finset.range n, α ^ (n - 1 - j) * ω (j + 1) := by
  have h := orbit_linear (AddMonoidHom.mulLeft α) id x ω n
  simp only [AddMonoidHom.coe_mulLeft, id] at h
  rw [h]
  have hit : ∀ m (y : ℝ), (α * ·)^[m] y = α ^ m * y := fun m y => by
    induction m generalizing y with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply, ih, pow_succ]; ring
  simp only [hit]

/-! ### Autoregressions AR(k) -/

/-- Shifting a new value into a lag vector: `shiftIn a (v₀, …, vₖ₋₁) = (a, v₀, …, vₖ₋₂)`. -/
def shiftIn {α : Type*} {k : ℕ} (a : α) (v : Fin k → α) : Fin k → α :=
  fun i => if h : (i : ℕ) = 0 then a else v ⟨i - 1, by have := i.isLt; omega⟩

/-- The first coordinate of `shiftIn a v` is `a`. -/
theorem shiftIn_apply_zero {α : Type*} {k : ℕ} (a : α) (v : Fin (k + 1) → α) :
    shiftIn a v 0 = a := rfl

/-- The other coordinates of `shiftIn a v` are those of `v`, shifted by one. -/
theorem shiftIn_apply_succ {α : Type*} {k : ℕ} (a : α) (v : Fin (k + 1) → α) (i : Fin k) :
    shiftIn a v i.succ = v i.castSucc := by
  simp [shiftIn]
  rfl

/-- `shiftIn` is jointly measurable. -/
theorem measurable_shiftIn {α : Type*} [MeasurableSpace α] {k : ℕ} :
    Measurable fun p : α × (Fin k → α) => shiftIn p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : (i : ℕ) = 0
  · simpa [shiftIn, h] using measurable_fst
  · simp only [shiftIn, h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

/-- `shiftIn` is additive in the pair `(a, v)`. -/
theorem shiftIn_add {k : ℕ} (a b : ℝ) (v u : Fin k → ℝ) :
    shiftIn (a + b) (v + u) = shiftIn a v + shiftIn b u := by
  ext i
  by_cases h : (i : ℕ) = 0 <;> simp [shiftIn, h]

/-- The AR(k) step on lag vectors `y = (Yₙ₋₁, …, Yₙ₋ₖ)`:
`Yₙ = α₁Yₙ₋₁ + ⋯ + αₖYₙ₋ₖ + Wₙ` is shifted in (MT, (AR1), p. 24). -/
def arStep {k : ℕ} (α : Fin k → ℝ) (p : (Fin k → ℝ) × ℝ) : Fin k → ℝ :=
  shiftIn (∑ j, α j * p.1 j + p.2) p.1

/-- The AR(k) step is measurable. -/
theorem measurable_arStep {k : ℕ} (α : Fin k → ℝ) : Measurable (arStep α) := by
  have h1 : Measurable fun p : (Fin k → ℝ) × ℝ => ∑ j, α j * p.1 j + p.2 :=
    (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp measurable_fst)).add measurable_snd
  exact measurable_shiftIn.comp (h1.prodMk measurable_fst)

/-- The AR(k) model as a Markov chain on `ℝᵏ` (MT, (AR1)–(AR2), p. 24). -/
noncomputable def arKernel {k : ℕ} (Γ : Measure ℝ) (α : Fin k → ℝ) :
    Kernel (Fin k → ℝ) (Fin k → ℝ) :=
  recursionKernel Γ (arStep α)

/-- The AR(k) model is a Markov kernel. -/
theorem isMarkovKernel_arKernel {k : ℕ} (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (α : Fin k → ℝ) : IsMarkovKernel (arKernel Γ α) :=
  isMarkovKernel_recursionKernel Γ (measurable_arStep α)

/-- The companion matrix of MT, (2.1), p. 25: first row `(α₁, …, αₖ)`, ones on the
subdiagonal. -/
def companion {k : ℕ} (α : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 then α j else if (i : ℕ) = j + 1 then 1 else 0

/-- The input column `(1, 0, …, 0)ᵀ` of MT, (2.1). -/
def firstUnit (k : ℕ) : Matrix (Fin k) (Fin 1) ℝ :=
  Matrix.of fun i _ => if (i : ℕ) = 0 then 1 else 0

/-- **MT, (2.1), p. 25.** The AR(k) step in state space form `Xₙ = A Xₙ₋₁ + e₁ Wₙ`. -/
theorem arStep_eq_companion {k : ℕ} (α : Fin k → ℝ) (y : Fin k → ℝ) (w : ℝ) :
    arStep α (y, w) = companion α *ᵥ y + firstUnit k *ᵥ (fun _ => w) := by
  ext i
  by_cases h : (i : ℕ) = 0
  · simp [arStep, shiftIn, h, companion, firstUnit, Matrix.mulVec, dotProduct]
  · have hi : (i : ℕ) - 1 < k := by have := i.isLt; omega
    have h1 : arStep α (y, w) i = y ⟨(i : ℕ) - 1, hi⟩ := by
      simp only [arStep, shiftIn, h, dite_false]
    have h2 : (companion α *ᵥ y) i = y ⟨(i : ℕ) - 1, hi⟩ := by
      simp only [Matrix.mulVec, dotProduct, companion, Matrix.of_apply, h, ite_false]
      rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, hi⟩ : Fin k)]
      · have hc : (i : ℕ) = ((⟨(i : ℕ) - 1, hi⟩ : Fin k) : ℕ) + 1 := by
          change (i : ℕ) = (i : ℕ) - 1 + 1
          omega
        rw [ite_eq_left hc, one_mul]
      · intro j _ hj
        have hc : ¬ (i : ℕ) = (j : ℕ) + 1 := fun hij => hj (Fin.ext (by
          change (j : ℕ) = (i : ℕ) - 1
          omega))
        rw [ite_eq_right hc, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have h3 : (firstUnit k *ᵥ fun _ => w) i = 0 := by
      simp [Matrix.mulVec, dotProduct, firstUnit, h]
    rw [Pi.add_apply, h1, h2, h3, add_zero]

/-- **AR(k) is a linear state space model**: `arKernel Γ α` is LSS(A, e₁) with the companion
matrix `A` of (2.1) and the disturbance law `Γ` viewed on `ℝ¹`. -/
theorem arKernel_eq_lssMatrixKernel {k : ℕ} (Γ : Measure ℝ) [SFinite Γ] (α : Fin k → ℝ) :
    arKernel Γ α = lssMatrixKernel (Γ.map fun w _ => w) (companion α) (firstUnit k) := by
  have hg : Measurable fun w : ℝ => (fun _ : Fin 1 => w) :=
    measurable_pi_iff.mpr fun _ => measurable_id
  rw [lssMatrixKernel, ← recursionKernel_comp_noise Γ (measurable_lssMatrixStep _ _) hg, arKernel]
  congr 1
  funext p
  exact arStep_eq_companion α p.1 p.2

/-- The lag vector `(Yₙ, Yₙ₋₁, …, Yₙ₋ₖ₊₁)` of a sequence `Y : ℤ → ℝ`. -/
def arVec {k : ℕ} (Y : ℤ → ℝ) (n : ℤ) : Fin k → ℝ := fun i => Y (n - i)

/-- MT, p. 24: if `Y` satisfies the AR(k) recursion at time `n`, the lag vectors satisfy
`Xₙ = arStep(Xₙ₋₁, Wₙ)`; so the Markov chain `X` has the AR sample paths as its first
coordinate. -/
theorem arVec_succ {k : ℕ} (α : Fin k → ℝ) (Y W : ℤ → ℝ) (n : ℤ)
    (hY : Y n = ∑ j : Fin k, α j * Y (n - 1 - j) + W n) :
    arVec Y n = arStep α (arVec Y (n - 1), W n) := by
  ext i
  by_cases h : (i : ℕ) = 0
  · simp only [arVec, arStep, shiftIn, h, dite_true]
    rw [Nat.cast_zero, sub_zero]
    exact hY
  · simp only [arVec, arStep, shiftIn, h, dite_false]
    congr 1
    have := i.isLt
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)]
    ring

/-! ### ARMA(k, ℓ) models -/

/-- The ARMA(k, ℓ) step on the state `(y, v) = ((Yₙ₋₁, …, Yₙ₋ₖ), (Wₙ₋₁, …, Wₙ₋ℓ))` with new
error `w = Wₙ` (MT, (ARMA1), p. 25, first realization). -/
def armaStep {k l : ℕ} (α : Fin k → ℝ) (β : Fin l → ℝ)
    (p : ((Fin k → ℝ) × (Fin l → ℝ)) × ℝ) : (Fin k → ℝ) × (Fin l → ℝ) :=
  (shiftIn (∑ i, α i * p.1.1 i + p.2 + ∑ j, β j * p.1.2 j) p.1.1, shiftIn p.2 p.1.2)

/-- The ARMA step is measurable. -/
theorem measurable_armaStep {k l : ℕ} (α : Fin k → ℝ) (β : Fin l → ℝ) :
    Measurable (armaStep α β) := by
  have h1 : Measurable fun p : ((Fin k → ℝ) × (Fin l → ℝ)) × ℝ =>
      ∑ i, α i * p.1.1 i + p.2 + ∑ j, β j * p.1.2 j :=
    ((Finset.measurable_sum _ fun i _ => measurable_const.mul
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))).add
        measurable_snd).add
      (Finset.measurable_sum _ fun j _ => measurable_const.mul
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))
  exact (measurable_shiftIn.comp (h1.prodMk (measurable_fst.comp measurable_fst))).prodMk
    (measurable_shiftIn.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

/-- The ARMA(k, ℓ) model as a Markov chain on `ℝᵏ × ℝˡ` (MT, (ARMA1)–(ARMA2), p. 25). -/
noncomputable def armaKernel {k l : ℕ} (Γ : Measure ℝ) (α : Fin k → ℝ) (β : Fin l → ℝ) :
    Kernel ((Fin k → ℝ) × (Fin l → ℝ)) ((Fin k → ℝ) × (Fin l → ℝ)) :=
  recursionKernel Γ (armaStep α β)

/-- The ARMA model is a Markov kernel. -/
theorem isMarkovKernel_armaKernel {k l : ℕ} (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (α : Fin k → ℝ) (β : Fin l → ℝ) : IsMarkovKernel (armaKernel Γ α β) :=
  isMarkovKernel_recursionKernel Γ (measurable_armaStep α β)

/-- **MT, p. 25, the low-dimensional realization of ARMA(k, ℓ).** If `Z` satisfies the AR(k)
recursion (2.2), `Zₘ = Σᵢ αᵢ Zₘ₋₁₋ᵢ + Wₘ`, at all times `m ≥ n₀`, then
`Yₙ = Zₙ + Σⱼ βⱼ Zₙ₋₁₋ⱼ` satisfies the ARMA(k, ℓ) recursion
`Yₙ = Σᵢ αᵢ Yₙ₋₁₋ᵢ + Wₙ + Σⱼ βⱼ Wₙ₋₁₋ⱼ` at all times `n ≥ n₀ + ℓ`. -/
theorem arma_of_ar {k l : ℕ} (α : Fin k → ℝ) (β : Fin l → ℝ) (Z W : ℤ → ℝ) (n₀ : ℤ)
    (hZ : ∀ m, n₀ ≤ m → Z m = ∑ i : Fin k, α i * Z (m - 1 - i) + W m) (n : ℤ)
    (hn : n₀ + l ≤ n) :
    let Y : ℤ → ℝ := fun m => Z m + ∑ j : Fin l, β j * Z (m - 1 - j)
    Y n = ∑ i : Fin k, α i * Y (n - 1 - i) + W n + ∑ j : Fin l, β j * W (n - 1 - j) := by
  intro Y
  have hZj : ∀ j : Fin l, Z (n - 1 - j) =
      ∑ i : Fin k, α i * Z (n - 1 - j - 1 - i) + W (n - 1 - j) := fun j =>
    hZ _ (by have := j.isLt; omega)
  have hcross : ∑ j : Fin l, β j * ∑ i : Fin k, α i * Z (n - 1 - j - 1 - i) =
      ∑ i : Fin k, α i * ∑ j : Fin l, β j * Z (n - 1 - i - 1 - j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show n - 1 - (j : ℤ) - 1 - i = n - 1 - i - 1 - j by ring]
    ring
  simp only [Y, hZ n (by omega), hZj, mul_add, Finset.sum_add_distrib]
  linear_combination hcross

/-! ### Figure 1.1: a stable and an unstable deterministic linear model -/

/-- The matrix `F = I + ΔA` of Figure 1.1 (MT, p. 8), `A = [[−0.2, 1], [−1, −0.2]]`,
`Δ = 0.02`. -/
noncomputable def fig11F : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0.996, 0.02; -0.02, 0.996]

/-- `fig11F` is `I + ΔA` with `A = [[−0.2, 1], [−1, −0.2]]` and `Δ = 0.02`. -/
theorem fig11F_eq : fig11F = 1 + (0.02 : ℝ) • !![-0.2, 1; -1, -0.2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [fig11F, Matrix.one_apply]

/-- The squared Euclidean norm on `ℝ²`. -/
def sqNorm2 (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- `|F x|² = 0.992416 |x|²`: `F` is a contraction composed with a rotation. -/
theorem fig11_sqNorm_mulVec (x : Fin 2 → ℝ) : sqNorm2 (fig11F *ᵥ x) = 0.992416 * sqNorm2 x := by
  simp [sqNorm2, fig11F, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- MT, p. 8: the trajectories of `xₖ₊₁ = F xₖ` spiral in: `|Fᵏ x|² → 0`. -/
theorem fig11_tendsto_zero (x : Fin 2 → ℝ) :
    Tendsto (fun k => sqNorm2 ((fig11F ^ k) *ᵥ x)) atTop (nhds 0) := by
  have h : ∀ k, sqNorm2 ((fig11F ^ k) *ᵥ x) = 0.992416 ^ k * sqNorm2 x := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, fig11_sqNorm_mulVec, ih, pow_succ']; ring
  simp only [h]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (0.992416 : ℝ)) (by norm_num)
    (by norm_num)).mul_const (sqNorm2 x)

/-- MT, p. 8: read in the other direction, `xₖ₊₁ = F⁻¹ xₖ`, the trajectory from any `x ≠ 0`
spirals out: `|F⁻ᵏ x|² → ∞`. -/
theorem fig11_inv_tendsto_atTop (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    Tendsto (fun k => sqNorm2 ((fig11F⁻¹ ^ k) *ᵥ x)) atTop atTop := by
  have hdet : IsUnit fig11F.det := by
    rw [isUnit_iff_ne_zero, fig11F, Matrix.det_fin_two_of]
    norm_num
  have hinv : ∀ y, sqNorm2 (fig11F⁻¹ *ᵥ y) = 0.992416⁻¹ * sqNorm2 y := fun y => by
    have h := fig11_sqNorm_mulVec (fig11F⁻¹ *ᵥ y)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
    rw [h]
    field_simp
  have h : ∀ k, sqNorm2 ((fig11F⁻¹ ^ k) *ᵥ x) = 0.992416⁻¹ ^ k * sqNorm2 x := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, hinv, ih, pow_succ']; ring
  have hpos : 0 < sqNorm2 x := by
    have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    unfold sqNorm2
    rcases this with h0 | h1
    · have := pow_pos (abs_pos.mpr h0) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.mpr h1) 2
      rw [sq_abs] at this
      positivity
  simp only [h]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).atTop_mul_const hpos

end MeynTweedie.InvariantMeasures
