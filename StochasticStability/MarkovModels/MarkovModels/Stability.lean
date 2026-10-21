/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The stability notions of MT, §1.3

MT, §1.3, pp. 13–19. The section previews the book's stability notions and two of its main
theorems; this module gives the definitions those previews use, so that later chapters can state
Theorem 1.3.1 (proved in Chapter 13) and Theorem 1.3.2 (Chapters 6 and 18) against them.

* `pathMeasure P x`: the law `Pₓ` of the chain started at `x`, by the Ionescu-Tulcea theorem
  (Mathlib's `Kernel.traj`); copied from `LawsOfLargeNumbers/MarkovPaths.lean` of this repository.
* `hittingTime A`, `hitEvent A`: `τ_A = inf(n ≥ 1 : Φₙ ∈ A)` (MT, p. 14) and the event
  `{τ_A < ∞}` (`hittingTime_lt_top_iff`).
* `IsPhiIrreducible` (MT, (I), p. 14), `IsPhiRecurrent` ((1.8), p. 15), `HasFiniteMeanHitting`
  ((1.9)), `IsNonEvanescent` ((1.10)), `IsTightChain` ((1.11)).
* Theorem 1.3.1's conditions: invariance (1.12) is Mathlib's `Kernel.Invariant`, equivalent to the
  invariant equations `π(A) = ∫ π(dx) P(x, A)` (`invariant_iff_eq_lintegral`); `IsSmallSet`,
  `BoundedMeanReturn` (1.13), `SatisfiesDrift` (1.14), `IsLocallyConvergent` (1.15) and
  `ConvergesInTotalVariation` (1.16), with `tvDist`.
* Theorem 1.3.2's conditions: `IsWeakFeller` (MT, p. 17).
* The dynamical system notions of MT, §1.3.2, pp. 17–18, for a map `T` of a metric space:
  `IsLagrangeStable`, `IsLyapunovStable`, `IsAsymptoticallyStable`,
  `IsGloballyAsymptoticallyStable`. The example of MT, p. 18: `x ↦ x + 1` is stable in the sense
  of Lyapunov (`succ_isLyapunovStable`) but not Lagrange stable (`succ_not_isLagrangeStable`) nor
  globally asymptotically stable (`succ_not_isGloballyAsymptoticallyStable`).
* The dynamical system `μ ↦ μP` on probability measures (MT, p. 17): its fixed points are the
  invariant measures (`fixedPoint_distStep_iff`), the claim in (iii) of MT, p. 18.

Theorems 1.3.1 and 1.3.2 themselves are forward references (MT, Chapters 13, 6 and 18).
-/

namespace MeynTweedie.MarkovModels

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The path measure -/

/-- The kernels `(x₀, …, xₙ) ↦ P(xₙ, ·)` that drive the path. -/
noncomputable def trajKernel (P : Kernel X X) (n : ℕ) : Kernel (Π _ : Finset.Iic n, X) X :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

/-- The path kernels are Markov kernels. -/
theorem isMarkovKernel_trajKernel (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (trajKernel P n) := by
  unfold trajKernel
  infer_instance

/-- The law `Pₓ` of the path `(Φ₀, Φ₁, …)` of the chain with transition kernel `P` started at
`Φ₀ = x` (MT, p. 14). -/
noncomputable def pathMeasure (P : Kernel X X) [IsMarkovKernel P] (x : X) : Measure (ℕ → X) :=
  @Kernel.traj (fun _ => X) _ (trajKernel P) (isMarkovKernel_trajKernel P) 0 (fun _ => x)

/-- `Pₓ` is a probability measure. -/
theorem isProbabilityMeasure_pathMeasure (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    IsProbabilityMeasure (pathMeasure P x) := by
  have := isMarkovKernel_trajKernel P
  unfold pathMeasure
  infer_instance

/-! ### Hitting times and the stability notions (I)–(II) -/

/-- The first hitting time `τ_A = inf(n ≥ 1 : Φₙ ∈ A)`, `∞` if `A` is never reached (MT, p. 14). -/
noncomputable def hittingTime (A : Set X) (ω : ℕ → X) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ ω n ∈ A), (n : ℕ∞)

/-- The event `{τ_A < ∞}` that the chain reaches `A` at some time `n ≥ 1`. -/
def hitEvent (A : Set X) : Set (ℕ → X) := {ω | ∃ n, 1 ≤ n ∧ ω n ∈ A}

omit [MeasurableSpace X] in
/-- `τ_A < ∞` exactly on the event that `A` is reached. -/
theorem hittingTime_lt_top_iff (A : Set X) (ω : ℕ → X) :
    hittingTime A ω < ⊤ ↔ ω ∈ hitEvent A := by
  simp only [hittingTime, hitEvent, mem_ofPred_eq, iInf_lt_iff, exists_prop]
  constructor
  · rintro ⟨n, hn, -⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn, ENat.natCast_lt_top n⟩

/-- `{τ_A < ∞}` is measurable for measurable `A`. -/
theorem measurableSet_hitEvent {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (hitEvent A) := by
  have : hitEvent A = ⋃ n : ℕ, ⋃ (_ : 1 ≤ n), (fun ω : ℕ → X => ω n) ⁻¹' A := by
    ext ω
    simp [hitEvent]
  rw [this]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => measurable_pi_apply n hA

/-- **(I) φ-irreducibility** (MT, p. 14): every set of positive `φ`-measure is reached with
positive probability from every starting point. -/
def IsPhiIrreducible (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) : Prop :=
  ∀ x A, MeasurableSet A → 0 < φ A → 0 < pathMeasure P x (hitEvent A)

/-- **(1.8)** (MT, p. 15): every set of positive `φ`-measure is reached with probability one. -/
def IsPhiRecurrent (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) : Prop :=
  ∀ x A, MeasurableSet A → 0 < φ A → pathMeasure P x (hitEvent A) = 1

/-- **(1.9)** (MT, p. 15): every set of positive `φ`-measure is reached in finite mean time. -/
def HasFiniteMeanHitting (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) : Prop :=
  ∀ x A, MeasurableSet A → 0 < φ A →
    ∫⁻ ω, (hittingTime A ω : ℝ≥0∞) ∂(pathMeasure P x) < ⊤

/-- The event `{Φ → ∞} = ⋂ₙ {Φ ∈ Oₙ i.o.}ᶜ` of (1.10), for a countable family of open precompact
sets `Oₙ` (MT, p. 15). -/
def evanescenceEvent (O : ℕ → Set X) : Set (ℕ → X) :=
  ⋂ n, {ω | ∃ᶠ k in atTop, ω k ∈ O n}ᶜ

/-- The chain is non-evanescent (MT, (1.10), p. 15): `Pₓ{Φ → ∞} = 0` for every `x`. -/
def IsNonEvanescent [TopologicalSpace X] (P : Kernel X X) [IsMarkovKernel P] (O : ℕ → Set X) :
    Prop :=
  (∀ n, IsOpen (O n) ∧ IsCompact (closure (O n))) ∧
    ∀ x, pathMeasure P x (evanescenceEvent O) = 0

/-- **(1.11)** (MT, p. 15): tightness of the transition probabilities: for every `x` and `ε > 0`
there is a compact `C` with `lim inf_k Pᵏ(x, C) ≥ 1 − ε`. -/
def IsTightChain [TopologicalSpace X] (P : Kernel X X) : Prop :=
  ∀ x, ∀ ε : ℝ≥0∞, 0 < ε → ∃ C, IsCompact C ∧ 1 - ε ≤ liminf (fun k => (P ^ k) x C) atTop

/-! ### The conditions of Theorem 1.3.1 -/

/-- **(1.12)** (MT, p. 16): `π` is invariant, `πP = π`, exactly when it solves the invariant
equations `π(A) = ∫ π(dx) P(x, A)` for all measurable `A`. -/
theorem invariant_iff_eq_lintegral (P : Kernel X X) (π : Measure X) :
    P.Invariant π ↔ ∀ A, MeasurableSet A → π A = ∫⁻ x, P x A ∂π := by
  refine ⟨fun h A hA => ?_, fun h => ?_⟩
  · conv_lhs => rw [← h.def]
    exact Measure.bind_apply hA P.aemeasurable
  · refine Measure.ext fun A hA => ?_
    rw [Measure.bind_apply hA P.aemeasurable, ← h A hA]

/-- A *small* set (MT, §1.3.1; defined in Chapter 5): for some `m` and some nontrivial measure
`ν`, `Pᵐ(x, ·) ≥ ν` for every `x ∈ C`. -/
def IsSmallSet (P : Kernel X X) (C : Set X) : Prop :=
  ∃ (m : ℕ) (ν : Measure X), ν ≠ 0 ∧ ∀ x ∈ C, ∀ A, MeasurableSet A → ν A ≤ (P ^ m) x A

/-- **(1.13)** (MT, p. 16): `sup_{x ∈ C} Eₓ[τ_C] ≤ M`. -/
def BoundedMeanReturn (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (M : ℝ≥0∞) : Prop :=
  ∀ x ∈ C, ∫⁻ ω, (hittingTime C ω : ℝ≥0∞) ∂(pathMeasure P x) ≤ M

/-- **(1.14)** (MT, p. 16), the Foster–Lyapunov drift condition `PV ≤ V − 1 + b 1_C`, written
additively, `PV + 1 ≤ V + b 1_C`, for `V` with values in `[0, ∞]`. -/
def SatisfiesDrift (P : Kernel X X) (V : X → ℝ≥0∞) (C : Set X) (b : ℝ≥0∞) : Prop :=
  ∀ x, ∫⁻ y, V y ∂(P x) + 1 ≤ V x + b * C.indicator 1 x

/-- **(1.15)** (MT, p. 16): for some `c > 0`, `lim inf_n sup_{x ∈ C} |Pⁿ(x, C) − c| = 0`. -/
def IsLocallyConvergent (P : Kernel X X) (C : Set X) : Prop :=
  ∃ c : ℝ, 0 < c ∧ liminf (fun n => ⨆ x ∈ C, |((P ^ n) x).real C - c|) atTop = 0

/-- The total variation distance `sup_A |μ(A) − ν(A)|` of MT, (1.16). -/
noncomputable def tvDist (μ ν : Measure X) : ℝ :=
  ⨆ (A : Set X) (_ : MeasurableSet A), |μ.real A - ν.real A|

/-- **(1.16)** (MT, p. 16): `sup_A |Pⁿ(x, A) − π(A)| → 0`. -/
def ConvergesInTotalVariation (P : Kernel X X) (π : Measure X) (x : X) : Prop :=
  Tendsto (fun n => tvDist ((P ^ n) x) π) atTop (𝓝 0)

/-! ### The condition of Theorem 1.3.2 -/

/-- The (weak) Feller property (MT, p. 17): `Pf(x) = ∫ P(x, dy) f(y)` is continuous for every
bounded continuous `f`. -/
def IsWeakFeller [TopologicalSpace X] (P : Kernel X X) : Prop :=
  ∀ f : X → ℝ, Continuous f → (∃ M, ∀ x, |f x| ≤ M) → Continuous fun x => ∫ y, f y ∂(P x)

/-! ### The dynamical system approach (MT, §1.3.2) -/

/-- The dynamical system `μ ↦ μP` on measures (MT, p. 17). -/
noncomputable def distStep (P : Kernel X X) (μ : Measure X) : Measure X := μ.bind P

/-- MT, p. 18, (iii): the fixed points of `μ ↦ μP` are exactly the solutions of the invariant
equations (1.12). -/
theorem fixedPoint_distStep_iff (P : Kernel X X) (π : Measure X) :
    distStep P π = π ↔ ∀ A, MeasurableSet A → π A = ∫⁻ x, P x A ∂π :=
  invariant_iff_eq_lintegral P π

variable {Y : Type*} [PseudoMetricSpace Y]

/-- **Lagrange stability** (MT, (i), p. 17): every orbit `{Tᵏx}` is precompact. -/
def IsLagrangeStable (T : Y → Y) : Prop :=
  ∀ x, IsCompact (closure (range fun k => T^[k] x))

/-- **Stability in the sense of Lyapunov** (MT, (ii), p. 18):
`lim sup_{y → x} sup_{k ≥ 0} d(Tᵏy, Tᵏx) = 0`. -/
def IsLyapunovStable (T : Y → Y) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → ∀ k, dist (T^[k] y) (T^[k] x) ≤ ε

/-- **Asymptotic stability** (MT, (iii), p. 18): a fixed point `x*` such that trajectories
starting near `x*` stay near it and converge to it. -/
def IsAsymptoticallyStable (T : Y → Y) (xstar : Y) : Prop :=
  T xstar = xstar ∧ (∀ ε > 0, ∃ δ > 0, ∀ y, dist y xstar < δ → ∀ k, dist (T^[k] y) xstar ≤ ε) ∧
    ∃ δ > 0, ∀ y, dist y xstar < δ → Tendsto (fun k => T^[k] y) atTop (𝓝 xstar)

/-- **Global asymptotic stability** (MT, (iv), (1.17), p. 18). -/
def IsGloballyAsymptoticallyStable (T : Y → Y) (xstar : Y) : Prop :=
  IsLyapunovStable T ∧ ∀ x, Tendsto (fun k => T^[k] x) atTop (𝓝 xstar)

/-- The iterates of `x ↦ x + 1`. -/
theorem iterate_add_one (k : ℕ) (x : ℝ) : (fun y : ℝ => y + 1)^[k] x = x + k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    push_cast
    ring

/-- MT, p. 18: `xₖ₊₁ = xₖ + 1` is stable in the sense of Lyapunov. -/
theorem succ_isLyapunovStable : IsLyapunovStable fun y : ℝ => y + 1 := by
  intro x ε hε
  refine ⟨ε, hε, fun y hy k => ?_⟩
  rw [iterate_add_one, iterate_add_one, Real.dist_eq, show y + k - (x + k) = y - x by ring,
    ← Real.dist_eq]
  exact hy.le

/-- MT, p. 18: the orbits of `xₖ₊₁ = xₖ + 1` are unbounded, so the system is not Lagrange
stable. -/
theorem succ_not_isLagrangeStable : ¬ IsLagrangeStable fun y : ℝ => y + 1 := by
  intro h
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (h 0).isBounded
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have h0 : (0 : ℝ) ∈ closure (range fun k => (fun y : ℝ => y + 1)^[k] 0) :=
    subset_closure ⟨0, rfl⟩
  have hk' : (k : ℝ) ∈ closure (range fun k => (fun y : ℝ => y + 1)^[k] 0) :=
    subset_closure ⟨k, by simp only [iterate_add_one, zero_add]⟩
  have := hC hk' h0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Nat.cast_nonneg k)] at this
  linarith

/-- MT, p. 18: `xₖ₊₁ = xₖ + 1` is not globally asymptotically stable: its orbits diverge. -/
theorem succ_not_isGloballyAsymptoticallyStable (xstar : ℝ) :
    ¬ IsGloballyAsymptoticallyStable (fun y : ℝ => y + 1) xstar := by
  rintro ⟨-, h⟩
  have h1 := h 0
  simp only [iterate_add_one, zero_add] at h1
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop xstar h1

end MeynTweedie.MarkovModels
