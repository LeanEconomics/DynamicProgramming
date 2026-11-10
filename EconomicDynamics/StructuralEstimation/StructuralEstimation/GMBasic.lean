/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.StationaryErgodicity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The GMM set-up (Miao, Chapter 12 introduction and §12.1, pp. 385–388)

Miao, pp. 385–388. The model generates `ℝ^r`-valued data `x_t`; here the data are a process
`X : ℕ → Ω → E` on a probability space `(Ω, P)` with values in a measurable space `E` (the book's
`ℝ^r`; nothing below needs more structure), and the observed sample is `x₀, …, x_{T−1}` (the book
indexes it `t = 1, …, T`). Parameters are `θ ∈ Θ ⊆ ℝ^k` (`Fin k → ℝ`, sup norm), and the moment
function `h : E → ℝ^k → ℝ^q` has `q` coordinates.

* `gm_sampleMoment X h T ω θ = g_T(θ) = (1/T) Σ_{t<T} h(x_t, θ)` (p. 388);
* `gm_popMoment P X h θ = g(θ) = E h(x₀, θ)` (12.1), coordinatewise (for a stationary process
  `E h(x_t, θ) = E h(x₀, θ)` for every `t`, `gm_integral_comp_eq`);
* `gm_quadForm W v = v'Wv` and the GMM objective `Q_T(θ) = g_T(θ)' W_T g_T(θ)` (`gm_objective`)
  and its population analogue `Q₀(θ) = g(θ)' W g(θ)` (`gm_popObjective`, p. 389);
* `Assumption_12_1_3` (global identification), `Assumption_12_1_7` (dominance) and
  `Assumption_12_1_4` (the weighting matrices) as named propositions. Assumptions 12.1.1, 12.1.5
  are `IsStationary` and `IsErgodicProcess` of Chapter 4; Assumptions 12.1.2, 12.1.6 are stated
  as hypotheses (`ContinuousOn`, `IsCompact`) where they are used.

Departure (see `docs/GM-corrections.md`): Assumption 12.1.7, `E[sup_θ ‖h(x_t, θ)‖] < ∞`, is stated
as the existence of an integrable envelope `D` with `‖h(x, θ)‖ ≤ D(x)` on `Θ`; the supremum over
an uncountable `Θ` need not be measurable, and when it is, `D = sup_θ ‖h(·, θ)‖` is such an
envelope (`assumption_12_1_7_of_sup`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Miao, p. 388: the sample moment `g_T(θ) = (1/T) Σ_{t<T} h(x_t, θ)`. -/
noncomputable def gm_sampleMoment {k q : ℕ} (X : ℕ → Ω → E) (h : E → (Fin k → ℝ) → Fin q → ℝ)
    (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) : Fin q → ℝ :=
  fun i => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, h (X t ω) θ i

/-- Miao, (12.1), p. 387: the population moment `g(θ) = E[h(x_t, θ)]` (at `t = 0`). -/
noncomputable def gm_popMoment {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (θ : Fin k → ℝ) : Fin q → ℝ :=
  fun i => ∫ ω, h (X 0 ω) θ i ∂P

/-- The quadratic form `v'Wv = Σ_i Σ_j v_i W_ij v_j`. -/
def gm_quadForm {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * W i j * v j

/-- Miao, p. 388: the GMM objective `Q_T(θ) = g_T(θ)' W_T g_T(θ)`. -/
noncomputable def gm_objective {k q : ℕ} (X : ℕ → Ω → E) (h : E → (Fin k → ℝ) → Fin q → ℝ)
    (WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ) (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) : ℝ :=
  gm_quadForm (WT T ω) (gm_sampleMoment X h T ω θ)

/-- Miao, p. 389: the population objective `Q₀(θ) = E[h(x_t, θ)]' W E[h(x_t, θ)]`. -/
noncomputable def gm_popObjective {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (W : Matrix (Fin q) (Fin q) ℝ) (θ : Fin k → ℝ) : ℝ :=
  gm_quadForm W (gm_popMoment P X h θ)

/-- **Assumption 12.1.3** (global identification, Miao, p. 387): on `Θ`,
`E[h(x_t, θ)] = 0` if and only if `θ = θ₀`. -/
def Assumption_12_1_3 {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (Θ : Set (Fin k → ℝ)) (θ₀ : Fin k → ℝ) : Prop :=
  ∀ θ ∈ Θ, gm_popMoment P X h θ = 0 ↔ θ = θ₀

/-- **Assumption 12.1.4** (Miao, p. 388): each `W_T` is positive semidefinite and `W_T → W` in
probability (entrywise) with `W` positive definite. -/
def Assumption_12_1_4 {q : ℕ} (P : Measure Ω) (WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ)
    (W : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  (∀ T ω, (WT T ω).PosSemidef) ∧ W.PosDef ∧
    ∀ i j, TendstoInMeasure P (fun T ω => WT T ω i j) atTop (fun _ => W i j)

/-- **Assumption 12.1.7** (dominance, Miao, p. 389), in envelope form: there is a measurable
`D` with `E D(x_t) < ∞` and `‖h(x, θ)‖ ≤ D(x)` for all `x` and `θ ∈ Θ`. -/
def Assumption_12_1_7 {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (Θ : Set (Fin k → ℝ)) : Prop :=
  ∃ D : E → ℝ, Measurable D ∧ Integrable (fun ω => D (X 0 ω)) P ∧ ∀ x, ∀ θ ∈ Θ, ‖h x θ‖ ≤ D x

/-- Miao, Assumption 12.1.7 (p. 389): if `x ↦ sup_{θ∈Θ} ‖h(x, θ)‖` is finite, measurable and
integrable, it is an envelope, so the book's `E[sup_θ ‖h(x_t, θ)‖] < ∞` gives
`Assumption_12_1_7`. -/
theorem assumption_12_1_7_of_sup {k q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E}
    {h : E → (Fin k → ℝ) → Fin q → ℝ} {Θ : Set (Fin k → ℝ)}
    (hbdd : ∀ x, BddAbove ((fun θ => ‖h x θ‖) '' Θ))
    (hm : Measurable fun x => sSup ((fun θ => ‖h x θ‖) '' Θ))
    (hi : Integrable (fun ω => sSup ((fun θ => ‖h (X 0 ω) θ‖) '' Θ)) P) :
    Assumption_12_1_7 P X h Θ :=
  ⟨fun x => sSup ((fun θ => ‖h x θ‖) '' Θ), hm, hi, fun x _ hθ =>
    le_csSup (hbdd x) (Set.mem_image_of_mem _ hθ)⟩

/-- `gm_quadForm W v = v ⬝ᵥ W.mulVec v`. -/
theorem gm_quadForm_eq {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    gm_quadForm W v = v ⬝ᵥ W.mulVec v := by
  simp only [gm_quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The quadratic form is continuous in the vector. -/
theorem gm_continuous_quadForm {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) :
    Continuous (gm_quadForm W) := by
  unfold gm_quadForm
  fun_prop

/-- For positive definite `W`, `v'Wv > 0` when `v ≠ 0`. -/
theorem gm_quadForm_pos {q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef)
    {v : Fin q → ℝ} (hv : v ≠ 0) : 0 < gm_quadForm W v := by
  rw [gm_quadForm_eq]
  have := hW.dotProduct_mulVec_pos hv
  simpa using this

/-- `0'W0 = 0`. -/
theorem gm_quadForm_zero {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) : gm_quadForm W 0 = 0 := by
  simp [gm_quadForm]

/-- Miao, p. 387: for a stationary process the mean `E h(x_t, θ)` does not depend on `t`. -/
theorem gm_integral_comp_eq {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) {φ : E → ℝ} (hφ : Measurable φ)
    (t : ℕ) : ∫ ω, φ (X t ω) ∂P = ∫ ω, φ (X 0 ω) ∂P := by
  have h := hst t 0
  have hm : Measurable fun y : Fin 1 → E => φ (y 0) := hφ.comp (measurable_pi_apply 0)
  have e1 : ∫ ω, φ (X t ω) ∂P = ∫ y, φ (y 0) ∂(P.map (window X t 0)) := by
    rw [integral_map (measurable_window hX t 0).aemeasurable hm.aestronglyMeasurable]
    simp [window]
  have e0 : ∫ ω, φ (X 0 ω) ∂P = ∫ y, φ (y 0) ∂(P.map (window X 0 0)) := by
    rw [integral_map (measurable_window hX 0 0).aemeasurable hm.aestronglyMeasurable]
    simp [window]
  rw [e1, e0, h]

end Miao.StructuralEstimation
