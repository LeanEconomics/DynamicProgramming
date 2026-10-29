import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Probability.StrongLaw
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Metrizable.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The path space of a Markov chain (MT §3.1, §3.4.1)

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd ed., §3.1 and §3.4.1,
pp. 48–61. The state space is an arbitrary measurable space `X`; no countable generation or
topology is needed. A transition probability kernel is a Markov kernel `P : Kernel X X`. The
sample space is `Ω = ℕ → X` with the product σ-algebra, and `Φₙ(ω) = ω n` are the coordinates.

* `trajKernel`, `pathKernel`, `pathMeasure`: `P_x` and `P_μ` are built from `P` by the
  Ionescu-Tulcea theorem (Mathlib's `Kernel.traj`, `Kernel.trajMeasure`). `pathKernel P` is the
  kernel `x ↦ P_x`, so `x ↦ P_x(B)` is measurable for every event `B`.
* `pathMeasure_eq_comp` (p. 53): `P_μ = ∫ P_x μ(dx)`, the mixture formula; `pathMeasure_dirac`:
  `P_{δ_x} = P_x`; `pathMeasure_inter_zero` (3.1): `P_μ(B ∩ {Φ₀ ∈ C}) = ∫_C P_x(B) μ(dx)`.
* `pathMeasure_map_zero`: the law of `Φ₀` under `P_μ` is `μ`; `ae_pathKernel_zero`:
  `Φ₀ = x`, `P_x`-a.s. (p. 49).
* `natFilt`: the natural filtration `𝓕ₙ^Φ = σ(Φ₀, …, Φₙ)` (p. 63).
* `setLIntegral_succ`: the one-step Markov identity `∫_G f(Φₙ₊₁) dP_μ = ∫_G Pf(Φₙ) dP_μ` for
  `G ∈ 𝓕ₙ^Φ`.
* `cylFn`, `measure_inter_shift_box`: the finite-dimensional distributions, even jointly with an
  event of `𝓕ₙ^Φ`.
* `IsMarkovChain`: a process with the finite-dimensional distributions (3.20), the definition of
  a time-homogeneous Markov chain with kernel `P` and initial law `μ` (p. 61).
* **Theorem 3.4.1** (`theorem_3_4_1`, p. 60): the coordinate process under `P_μ` is such a chain.
  `theorem_3_4_1_unique`: `P_μ` is the only probability on path space with these
  finite-dimensional distributions, and `law_eq_pathMeasure`: every Markov chain with kernel `P`
  and initial law `μ` has law `P_μ`.

**Corrections.** None. The book assumes a countably generated σ-algebra on `X`; the construction
needs no assumption on `X` at all (Ionescu-Tulcea).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The path measures -/

/-- The kernels `(x₀, …, xₙ) ↦ P(xₙ, ·)` that drive the path of the chain. -/
noncomputable def trajKernel (P : Kernel X X) (n : ℕ) : Kernel (Π _ : Finset.Iic n, X) X :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

/-- The driving kernels are Markov. -/
theorem isMarkovKernel_trajKernel (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (trajKernel P n) := by
  unfold trajKernel
  infer_instance

/-- The kernel `x ↦ P_x`: the law of the path started at `x` (MT p. 49). -/
noncomputable def pathKernel (P : Kernel X X) [IsMarkovKernel P] : Kernel X (ℕ → X) :=
  (@Kernel.traj (fun _ => X) _ (trajKernel P) (isMarkovKernel_trajKernel P) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm
    (MeasurableEquiv.measurable _)

/-- `P_x` is a probability measure. -/
theorem isMarkovKernel_pathKernel (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovKernel (pathKernel P) := by
  have := isMarkovKernel_trajKernel P
  unfold pathKernel
  infer_instance

/-- The law `P_μ` of the chain with transition kernel `P` and initial distribution `μ`
(MT p. 53, Theorem 3.4.1). -/
noncomputable def pathMeasure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    Measure (ℕ → X) :=
  @Kernel.trajMeasure (fun _ => X) _ μ (trajKernel P) (isMarkovKernel_trajKernel P)

/-- `P_μ` is a probability measure. -/
theorem isProbabilityMeasure_pathMeasure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (pathMeasure P μ) := by
  have := isMarkovKernel_trajKernel P
  unfold pathMeasure
  infer_instance

/-- **The mixture formula** (MT p. 53): `P_μ = ∫ P_x μ(dx)`. -/
theorem pathMeasure_eq_comp (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    pathMeasure P μ = pathKernel P ∘ₘ μ := by
  have := isMarkovKernel_trajKernel P
  have := isMarkovKernel_pathKernel P
  ext s hs
  rw [pathMeasure, Kernel.trajMeasure, Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (MeasurableEquiv.measurable _)]
  rfl

/-- `P_{δ_x} = P_x`. -/
theorem pathMeasure_dirac (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    pathMeasure P (Measure.dirac x) = pathKernel P x := by
  rw [pathMeasure_eq_comp, Measure.dirac_bind (Kernel.measurable _)]

/-- Under `P_x` the path starts at `x`: the law of `Φ₀` is `δ_x` (MT p. 49). -/
theorem pathKernel_map_zero (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    (pathKernel P x).map (fun ω => ω 0) = Measure.dirac x := by
  have := isMarkovKernel_trajKernel P
  have hg : Measurable fun y : Π _ : Finset.Iic 0, X => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  have hfr := Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) 0
  have h1 := Kernel.traj_map_frestrictLe (X := fun _ => X) (κ := trajKernel P) 0 0
  rw [Kernel.partialTraj_self] at h1
  have h3 := congrArg (fun η => (η (fun _ : Finset.Iic 0 => x)).map
    (fun y : Π _ : Finset.Iic 0, X => y ⟨0, Finset.mem_Iic.2 le_rfl⟩)) h1
  simp only [Kernel.map_apply _ hfr, Kernel.id_apply, Measure.map_dirac' hg,
    Measure.map_map hg hfr] at h3
  exact h3

/-- `P_x(Φ₀ ∈ A) = 1_A(x)`. -/
theorem pathKernel_zero_mem (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) : pathKernel P x {ω | ω 0 ∈ A} = A.indicator 1 x := by
  have h := congrArg (fun m : Measure X => m A) (pathKernel_map_zero P x)
  simp only [Measure.map_apply (measurable_pi_apply 0 : Measurable fun ω : ℕ → X => ω 0) hA,
    Measure.dirac_apply' _ hA] at h
  exact h

/-- `Φ₀ = x`, `P_x`-almost surely (when points are measurable, so that `{Φ₀ = x}` is an
event). -/
theorem ae_pathKernel_zero [MeasurableSingletonClass X] (P : Kernel X X) [IsMarkovKernel P]
    (x : X) :
    ∀ᵐ ω ∂pathKernel P x, ω 0 = x := by
  have h := pathKernel_map_zero P x
  have hae : ∀ᵐ y ∂(pathKernel P x).map (fun ω => ω 0), y = x := by
    rw [h, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable hae

/-- (3.1), MT p. 51: `P_μ(B ∩ {Φ₀ ∈ C}) = ∫_C P_x(B) μ(dx)`. In particular, for a countable
space, `P_μ(B ∩ {Φ₀ = x₀}) = μ(x₀) P_{x₀}(B)`. -/
theorem pathMeasure_inter_zero (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {B : Set (ℕ → X)} (hB : MeasurableSet B) {C : Set X} (hC : MeasurableSet C) :
    pathMeasure P μ (B ∩ {ω | ω 0 ∈ C}) = ∫⁻ x in C, pathKernel P x B ∂μ := by
  have := isMarkovKernel_pathKernel P
  have hm : MeasurableSet {ω : ℕ → X | ω 0 ∈ C} := measurable_pi_apply 0 hC
  rw [pathMeasure_eq_comp, Measure.bind_apply (hB.inter hm) (Kernel.aemeasurable _),
    ← lintegral_indicator hC]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ C
  · rw [indicator_of_mem hx]
    refine measure_inter_conull ?_
    have : {ω : ℕ → X | ω 0 ∈ C}ᶜ = {ω | ω 0 ∈ Cᶜ} := rfl
    rw [this, pathKernel_zero_mem P x hC.compl, indicator_of_notMem (by simpa using hx)]
  · rw [indicator_of_notMem hx]
    refine measure_mono_null inter_subset_right ?_
    rw [pathKernel_zero_mem P x hC, indicator_of_notMem hx]

/-- The law of `Φ₀` under `P_μ` is the initial distribution `μ`. -/
theorem pathMeasure_map_zero (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    (pathMeasure P μ).map (fun ω => ω 0) = μ := by
  ext C hC
  have := isMarkovKernel_pathKernel P
  have h := pathMeasure_inter_zero P μ MeasurableSet.univ hC
  rw [univ_inter] at h
  rw [Measure.map_apply (measurable_pi_apply 0 : Measurable fun ω : ℕ → X => ω 0) hC]
  exact h.trans (by simp)

/-! ### The natural filtration and the one-step identity -/

/-- The natural filtration `𝓕ₙ^Φ = σ(Φ₀, …, Φₙ)` of the coordinate process (MT p. 63). -/
abbrev natFilt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) :=
  Filtration.piLE (X := fun _ : ℕ => X)

/-- `Φₖ` is `𝓕ₖ^Φ`-measurable. -/
theorem measurable_coord_natFilt (k : ℕ) :
    Measurable[natFilt (X := X) k] fun ω : ℕ → X => ω k :=
  fun s hs => ⟨(fun x : Π _ : Set.Iic k, X => x ⟨k, Set.mem_Iic.2 le_rfl⟩) ⁻¹' s,
    measurable_pi_apply _ hs, rfl⟩

/-- `{Φₖ ∈ A} ∈ 𝓕ₙ^Φ` for `k ≤ n`. -/
theorem measurableSet_coord_natFilt {k n : ℕ} (hkn : k ≤ n) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet[natFilt (X := X) n] {ω : ℕ → X | ω k ∈ A} :=
  (natFilt (X := X)).mono hkn _ (measurable_coord_natFilt k hA)

/-- **The one-step Markov identity.** For `G ∈ 𝓕ₙ^Φ` and measurable `f ≥ 0`,
`∫_G f(Φₙ₊₁) dP_μ = ∫_G Pf(Φₙ) dP_μ`. -/
theorem setLIntegral_succ (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in G, f (ω (n + 1)) ∂pathMeasure P μ =
      ∫⁻ ω in G, ∫⁻ y, f y ∂P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_trajKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hG' := hG
  rw [natFilt, Filtration.piLE_eq_comap_frestrictLe] at hG'
  obtain ⟨T, hT, rfl⟩ := hG'
  have hc := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => X) (μ₀ := μ) (κ := trajKernel P) (a := n)
  have hfr := Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) n
  have hF : Measurable fun ω : ℕ → X => (Preorder.frestrictLe n ω, ω (n + 1)) :=
    hfr.prodMk (measurable_pi_apply _)
  have hpre : (Preorder.frestrictLe n ⁻¹' T : Set (ℕ → X)) =
      (fun ω : ℕ → X => (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹' (T ×ˢ univ) := by
    ext ω; simp
  have hf2 : Measurable fun p : (Π _ : Finset.Iic n, X) × X => f p.2 := hf.comp measurable_snd
  have hk : Measurable fun y : Π _ : Finset.Iic n, X => ∫⁻ z, f z ∂trajKernel P n y :=
    hf.lintegral_kernel
  calc ∫⁻ ω in Preorder.frestrictLe n ⁻¹' T, f (ω (n + 1)) ∂pathMeasure P μ
      = ∫⁻ p in T ×ˢ univ, f p.2 ∂((pathMeasure P μ).map
          fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) := by
        rw [setLIntegral_map (f := fun p => f p.2) (hT.prod MeasurableSet.univ) hf2 hF,
          hpre]
    _ = ∫⁻ p in T ×ˢ univ, f p.2 ∂(((pathMeasure P μ).map (Preorder.frestrictLe n)) ⊗ₘ
          trajKernel P n) := by
        rw [pathMeasure, hc]
    _ = ∫⁻ y in T, ∫⁻ z, f z ∂trajKernel P n y ∂((pathMeasure P μ).map
          (Preorder.frestrictLe n)) := by
        rw [Measure.setLIntegral_compProd (f := fun p => f p.2) hf2 hT MeasurableSet.univ]
        simp only [Measure.restrict_univ]
    _ = ∫⁻ ω in Preorder.frestrictLe n ⁻¹' T, ∫⁻ y, f y ∂P (ω n) ∂pathMeasure P μ := by
        rw [setLIntegral_map hT hk hfr]
        rfl

/-! ### Finite-dimensional distributions -/

/-- The nested integral of (3.20): `cylFn P n A y` is the probability, starting at `y`, that
`Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ`, namely `1_{A₀}(y) ∫_{A₁} P(y, dy₁) ⋯ P(y_{n−1}, Aₙ)`. -/
noncomputable def cylFn (P : Kernel X X) : ℕ → (ℕ → Set X) → X → ℝ≥0∞
  | 0, A => (A 0).indicator 1
  | n + 1, A => (A 0).indicator fun y => ∫⁻ z, cylFn P n (fun i => A (i + 1)) z ∂P y

/-- `cylFn` is measurable. -/
theorem measurable_cylFn (P : Kernel X X) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) : Measurable (cylFn P n A) := by
  induction n generalizing A with
  | zero => exact measurable_one.indicator (hA 0)
  | succ n ih =>
    exact (ih fun i => hA (i + 1)).lintegral_kernel.indicator (hA 0)

/-- The box `{Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ}`. -/
def boxSet (n : ℕ) (A : ℕ → Set X) : Set (ℕ → X) := {ω | ∀ i ≤ n, ω i ∈ A i}

/-- Boxes are measurable. -/
theorem measurableSet_boxSet (n : ℕ) {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (boxSet n A) := by
  have : boxSet n A = ⋂ i ∈ Finset.range (n + 1), {ω : ℕ → X | ω i ∈ A i} := by
    ext ω; simp [boxSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (hA i)

/-- The finite-dimensional distributions jointly with an event of the past:
for `G ∈ 𝓕ₙ^Φ`, `P_μ(G ∩ {Φₙ ∈ A₀, …, Φₙ₊ₘ ∈ Aₘ}) = ∫_G cylFn P m A (Φₙ) dP_μ`. -/
theorem measure_inter_shift_box (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) {n : ℕ}
    {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G) :
    pathMeasure P μ (G ∩ {ω | ∀ i ≤ m, ω (n + i) ∈ A i}) =
      ∫⁻ ω in G, cylFn P m A (ω n) ∂pathMeasure P μ := by
  induction m generalizing n G A with
  | zero =>
    have hset : {ω : ℕ → X | ∀ i ≤ 0, ω (n + i) ∈ A i} = (fun ω => ω n) ⁻¹' A 0 := by
      ext ω; simp
    have hm : MeasurableSet ((fun ω : ℕ → X => ω n) ⁻¹' A 0) := measurable_pi_apply n (hA 0)
    have hind : (fun ω : ℕ → X => cylFn P 0 A (ω n)) =
        ((fun ω : ℕ → X => ω n) ⁻¹' A 0).indicator 1 := by
      ext ω; by_cases h : ω n ∈ A 0 <;> simp [cylFn, h]
    rw [hset, hind, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_comm]
  | succ m ih =>
    set A' : ℕ → Set X := fun i => A (i + 1)
    have hA' : ∀ i, MeasurableSet (A' i) := fun i => hA (i + 1)
    have hm : MeasurableSet[natFilt n] {ω : ℕ → X | ω n ∈ A 0} :=
      measurableSet_coord_natFilt le_rfl (hA 0)
    have hG' : MeasurableSet[natFilt n] (G ∩ {ω : ℕ → X | ω n ∈ A 0}) := hG.inter hm
    have hset : G ∩ {ω : ℕ → X | ∀ i ≤ m + 1, ω (n + i) ∈ A i} =
        (G ∩ {ω | ω n ∈ A 0}) ∩ {ω | ∀ i ≤ m, ω (n + 1 + i) ∈ A' i} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, A']
      constructor
      · rintro ⟨hg, h⟩
        refine ⟨⟨hg, by simpa using h 0 (Nat.zero_le _)⟩, fun i hi => ?_⟩
        have := h (i + 1) (by omega)
        rwa [show n + (i + 1) = n + 1 + i by omega] at this
      · rintro ⟨⟨hg, h0⟩, h⟩
        refine ⟨hg, fun i hi => ?_⟩
        rcases i with _ | i
        · simpa using h0
        · have := h i (by omega)
          rwa [show n + 1 + i = n + (i + 1) by omega] at this
    have hmeas := measurable_cylFn P m hA'
    rw [hset, ih hA' ((natFilt (X := X)).mono (Nat.le_succ n) _ hG'),
      setLIntegral_succ P μ hG' hmeas]
    have hmn : MeasurableSet ((fun ω : ℕ → X => ω n) ⁻¹' A 0) := measurable_pi_apply n (hA 0)
    have hind : (fun ω : ℕ → X => cylFn P (m + 1) A (ω n)) =
        ((fun ω : ℕ → X => ω n) ⁻¹' A 0).indicator
          (fun ω => ∫⁻ y, cylFn P m A' y ∂P (ω n)) := by
      ext ω; by_cases h : ω n ∈ A 0 <;> simp [cylFn, h, A']
    rw [hind, setLIntegral_indicator hmn, inter_comm]
    rfl

/-- `P_x(Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ) = cylFn P n A x`. -/
theorem pathKernel_boxSet (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) : pathKernel P x (boxSet n A) = cylFn P n A x := by
  have h := measure_inter_shift_box P (Measure.dirac x) n hA (n := 0) MeasurableSet.univ
  simp only [univ_inter, Measure.restrict_univ, zero_add] at h
  rw [pathMeasure_dirac] at h
  rw [boxSet, h, ← lintegral_map (measurable_cylFn P n hA) (measurable_pi_apply 0),
    pathKernel_map_zero, lintegral_dirac' _ (measurable_cylFn P n hA)]

/-- Under `P_μ`, `P_μ(Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ) = ∫ cylFn P n A dμ`: this is (3.20). -/
theorem pathMeasure_boxSet (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) (n : ℕ)
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    pathMeasure P μ (boxSet n A) = ∫⁻ x, cylFn P n A x ∂μ := by
  have := isMarkovKernel_pathKernel P
  rw [pathMeasure_eq_comp, Measure.bind_apply (measurableSet_boxSet n hA)
    (Kernel.aemeasurable _)]
  exact lintegral_congr fun x => pathKernel_boxSet P x n hA

/-! ### Markov chains and Theorem 3.4.1 -/

variable {Ω : Type*} [MeasurableSpace Ω] (P : Kernel X X) (μ : Measure X) (pr : Measure Ω) in
/-- A process `Φ` on `(Ω, ℙ)` is a time-homogeneous Markov chain with transition kernel `P` and
initial distribution `μ` if its finite-dimensional distributions are given by (3.20)
(MT p. 61). -/
structure IsMarkovChain (Φ : ℕ → Ω → X) : Prop where
  /-- Each `Φₙ` is a random variable. -/
  measurable : ∀ n, Measurable (Φ n)
  /-- The finite-dimensional distributions are (3.20). -/
  fdd : ∀ n (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) →
    pr {ω | ∀ i ≤ n, Φ i ω ∈ A i} = ∫⁻ x, cylFn P n A x ∂μ

/-- **Theorem 3.4.1** (MT p. 60), existence. For every initial distribution `μ` and every
transition probability kernel `P`, the coordinate process on `(ℕ → X, P_μ)` is a Markov chain
with kernel `P` and initial distribution `μ`, and `P_μ` is a probability measure. -/
theorem theorem_3_4_1 (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (pathMeasure P μ) ∧
      IsMarkovChain P μ (pathMeasure P μ) (fun n ω => ω n) :=
  ⟨isProbabilityMeasure_pathMeasure P μ,
    ⟨fun n => measurable_pi_apply n, fun n _ hA => pathMeasure_boxSet P μ n hA⟩⟩

/-- Boxes generate the product σ-algebra on path space. -/
theorem generateFrom_boxSets :
    (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) = MeasurableSpace.generateFrom
      {S | ∃ n, ∃ A : ℕ → Set X, (∀ i, MeasurableSet (A i)) ∧ S = boxSet n A} := by
  refine le_antisymm ?_ ?_
  · rw [← generateFrom_squareCylinders]
    refine MeasurableSpace.generateFrom_le fun S hS => ?_
    obtain ⟨s, t, ht, rfl⟩ := hS
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨s.sup id, fun i => if i ∈ s then t i else univ, fun i => ?_, ?_⟩
    · by_cases hi : i ∈ s
      · simpa [hi] using ht i (mem_univ i)
      · simp [hi]
    · ext ω
      simp only [boxSet, Set.mem_pi, Finset.mem_coe, mem_ofPred_eq]
      constructor
      · intro h i _
        by_cases hi : i ∈ s
        · simpa [hi] using h i hi
        · simp [hi]
      · intro h i hi
        have := h i (Finset.le_sup (f := id) hi)
        simpa [hi] using this
  · refine MeasurableSpace.generateFrom_le fun S hS => ?_
    obtain ⟨n, A, hA, rfl⟩ := hS
    exact measurableSet_boxSet n hA

/-- Boxes form a π-system. -/
theorem isPiSystem_boxSets :
    IsPiSystem {S : Set (ℕ → X) | ∃ n, ∃ A : ℕ → Set X, (∀ i, MeasurableSet (A i)) ∧
      S = boxSet n A} := by
  rintro _ ⟨n, A, hA, rfl⟩ _ ⟨m, B, hB, rfl⟩ _
  refine ⟨max n m, fun i => (if i ≤ n then A i else univ) ∩ (if i ≤ m then B i else univ),
    fun i => ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_ <;> split_ifs <;> simp_all
  · ext ω
    simp only [boxSet, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ i _
      constructor <;> split_ifs with h
      · exact h1 i h
      · trivial
      · exact h2 i h
      · trivial
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · simpa [hi] using (h i (le_max_of_le_left hi)).1
      · simpa [hi] using (h i (le_max_of_le_right hi)).2

/-- **Theorem 3.4.1**, uniqueness: `P_μ` is the only probability measure on path space whose
finite-dimensional distributions are given by (3.20). -/
theorem theorem_3_4_1_unique (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure (ℕ → X)) [IsFiniteMeasure ν]
    (hν : ∀ n (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) →
      ν (boxSet n A) = ∫⁻ x, cylFn P n A x ∂μ) :
    ν = pathMeasure P μ := by
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨n, A, hA, rfl⟩
    rw [hν n A hA, pathMeasure_boxSet P μ n hA]
  · have hu : (univ : Set (ℕ → X)) = boxSet 0 (fun _ => univ) := by ext; simp [boxSet]
    rw [hu, hν 0 _ fun _ => MeasurableSet.univ,
      pathMeasure_boxSet P μ 0 fun _ => MeasurableSet.univ]

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- Every Markov chain with transition kernel `P` and initial distribution `μ` has law `P_μ`
on path space: the law of a Markov chain is determined by `P` and `μ`. -/
theorem law_eq_pathMeasure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {pr : Measure Ω} {Φ : ℕ → Ω → X} (h : IsMarkovChain P μ pr Φ) :
    pr.map (fun ω n => Φ n ω) = pathMeasure P μ := by
  have hΦ : Measurable fun ω n => Φ n ω := measurable_pi_iff.2 h.measurable
  have hbox : ∀ n (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) →
      pr.map (fun ω n => Φ n ω) (boxSet n A) = ∫⁻ x, cylFn P n A x ∂μ := fun n A hA => by
    rw [Measure.map_apply hΦ (measurableSet_boxSet n hA)]
    exact h.fdd n A hA
  have : IsFiniteMeasure (pr.map fun ω n => Φ n ω) := by
    refine ⟨?_⟩
    have hu : (univ : Set (ℕ → X)) = boxSet 0 (fun _ => univ) := by ext; simp [boxSet]
    rw [hu, hbox 0 _ fun _ => MeasurableSet.univ]
    simp [cylFn]
  exact theorem_3_4_1_unique P μ _ hbox

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition kernels, `n`-step kernels and their operators (MT §3.4.1–3.4.2)

Meyn and Tweedie, §3.4.1–3.4.2, pp. 59–62. A transition probability kernel on `X` is a Markov
kernel `P : Kernel X X` (p. 59); a general kernel on `X` is a `Kernel X X` (p. 60). The `n`-step
kernel `Pⁿ` is the `n`-th power in Mathlib's monoid of kernels, where `P * Q = P ∘ₖ Q` is "first
`Q`, then `P`"; powers of one kernel commute, so `Pⁿ` agrees with the book's `Pⁿ`.

* `IsSubstochasticKernel` (p. 59): `T(x, X) ≤ 1`.
* `pow_zero_apply` (3.21): `P⁰(x, A) = δ_x(A)`; `pow_succ_apply` (3.22):
  `Pⁿ⁺¹(x, A) = ∫ P(x, dy) Pⁿ(y, A)`; `isMarkovKernel_pow`: `Pⁿ` is a transition kernel.
* **Theorem 3.4.2** (`theorem_3_4_2`, p. 61): the Chapman–Kolmogorov equations
  `Pⁿ(x, A) = ∫ Pᵐ(x, dy) Pⁿ⁻ᵐ(y, A)`; `pow_add_eq` (p. 62): `Pᵐ⁺ⁿ = PᵐPⁿ`.
* `skeleton` (3.25), `skeleton_pow`: the `m`-skeleton has `n`-step kernel `Pᵐⁿ`.
* `sampledKernel` (`K_a = Σ a(n) Pⁿ`), `resolvent` (3.26) (`K_{a_ε} = (1 − ε) Σ εⁱ Pⁱ`) and
  `isMarkovKernel_sampledKernel`, `isMarkovKernel_resolvent`: they are transition kernels
  when `a` is a probability on `ℕ` and `0 ≤ ε < 1`.
* The operators of p. 62: `kfun P f = Pf` on nonnegative functions, `P ∘ₘ μ = μP` on measures,
  with `kfun_comp` (`P(Qf) = (PQ)f`), `measure_kernel_assoc` (`(μP)Q = μ(PQ)`), the duality
  `lintegral_kfun` (`∫ Pf dμ = ∫ f d(μP)`), `kfun_one` (`P1 = 1`), linearity and monotonicity;
  `kfunR` on bounded real functions, with `abs_kfunR_le` and `measurable_kfunR`.
* `indKernel` (p. 66): the kernel `I_B(x, A) = 1_{A ∩ B}(x)`, and `comp_indKernel_apply`:
  `(P I_B)(x, A) = P(x, A ∩ B)`.
* `potKernel` (3.30): `U = Σ_{n ≥ 1} Pⁿ`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Substochastic kernels and `n`-step kernels -/

/-- A substochastic transition kernel: `T(x, X) ≤ 1` for every `x` (MT p. 59). -/
def IsSubstochasticKernel (T : Kernel X X) : Prop := ∀ x, T x univ ≤ 1

/-- A transition probability kernel is substochastic. -/
theorem isSubstochasticKernel_of_markov (P : Kernel X X) [IsMarkovKernel P] :
    IsSubstochasticKernel P := fun x => by simp

/-- `Pⁿ` is a transition probability kernel. -/
theorem isMarkovKernel_pow (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (P ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((P ^ n) ∘ₖ P))

/-- (3.21): `P⁰(x, A) = δ_x(A)`. -/
theorem pow_zero_apply (P : Kernel X X) (x : X) : (P ^ 0) x = Measure.dirac x := by
  rw [pow_zero]; rfl

/-- (3.22): `Pⁿ⁺¹(x, A) = ∫ P(x, dy) Pⁿ(y, A)`. -/
theorem pow_succ_apply (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (P ^ (n + 1)) x A = ∫⁻ y, (P ^ n) y A ∂P x := by
  rw [pow_succ]
  exact Kernel.comp_apply' _ _ _ hA

/-- `Pⁿ⁺¹(x, A) = ∫ Pⁿ(x, dy) P(y, A)`. -/
theorem pow_succ_apply' (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (P ^ (n + 1)) x A = ∫⁻ y, P y A ∂(P ^ n) x :=
  Kernel.pow_succ_apply_eq_lintegral P n x hA

/-- **Theorem 3.4.2** (Chapman–Kolmogorov, MT p. 61). For `m ≤ n`,
`Pⁿ(x, A) = ∫ Pᵐ(x, dy) Pⁿ⁻ᵐ(y, A)`. -/
theorem theorem_3_4_2 (P : Kernel X X) {m n : ℕ} (hmn : m ≤ n) (x : X) {A : Set X}
    (hA : MeasurableSet A) : (P ^ n) x A = ∫⁻ y, (P ^ (n - m)) y A ∂(P ^ m) x := by
  have := Kernel.pow_add_apply_eq_lintegral P m (n - m) x hA
  rwa [Nat.add_sub_cancel' hmn] at this

/-- The Chapman–Kolmogorov equations in operator form (MT p. 62): `Pᵐ⁺ⁿ = PᵐPⁿ`, where `PᵐPⁿ`
is "first `Pᵐ`, then `Pⁿ`". -/
theorem pow_add_eq (P : Kernel X X) (m n : ℕ) : P ^ (m + n) = (P ^ n) ∘ₖ (P ^ m) := by
  rw [add_comm]; exact Kernel.pow_add P n m

/-- The `m`-skeleton: the chain with transition kernel `Pᵐ` (3.25), MT p. 62. -/
noncomputable abbrev skeleton (P : Kernel X X) (m : ℕ) : Kernel X X := P ^ m

/-- The `n`-step kernel of the `m`-skeleton is `Pᵐⁿ` (3.25). -/
theorem skeleton_pow (P : Kernel X X) (m n : ℕ) : skeleton P m ^ n = P ^ (m * n) :=
  (pow_mul P m n).symm

/-! ### Sampled kernels and resolvents -/

/-- The sampled kernel `K_a = Σₙ a(n) Pⁿ` for weights `a : ℕ → [0, ∞]` (MT p. 62; the
`K_a`-chains of Chapter 5). -/
noncomputable def sampledKernel (P : Kernel X X) (a : ℕ → ℝ≥0∞) : Kernel X X where
  toFun x := Measure.sum fun n => a n • (P ^ n) x
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum fun n => (Kernel.measurable_coe _ hs).const_mul _

/-- `K_a(x, A) = Σₙ a(n) Pⁿ(x, A)`. -/
theorem sampledKernel_apply (P : Kernel X X) (a : ℕ → ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) : sampledKernel P a x A = ∑' n, a n * (P ^ n) x A := by
  change (Measure.sum fun n => a n • (P ^ n) x) A = _
  rw [Measure.sum_apply _ hA]
  rfl

/-- `K_a` is a transition probability kernel when `a` is a probability on `ℕ`. -/
theorem isMarkovKernel_sampledKernel (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : ∑' n, a n = 1) : IsMarkovKernel (sampledKernel P a) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have := isMarkovKernel_pow P
  rw [sampledKernel_apply P a x MeasurableSet.univ]
  simpa using ha

/-- The resolvent `K_{a_ε} = (1 − ε) Σᵢ εⁱ Pⁱ` (3.26), MT p. 62. -/
noncomputable def resolvent (P : Kernel X X) (ε : ℝ≥0∞) : Kernel X X :=
  sampledKernel P fun n => (1 - ε) * ε ^ n

/-- (3.26): `K_{a_ε}(x, A) = (1 − ε) Σᵢ εⁱ Pⁱ(x, A)`. -/
theorem resolvent_apply (P : Kernel X X) (ε : ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) : resolvent P ε x A = (1 - ε) * ∑' i, ε ^ i * (P ^ i) x A := by
  rw [resolvent, sampledKernel_apply P _ x hA, ← ENNReal.tsum_mul_left]
  simp_rw [mul_assoc]

/-- The geometric weights `(1 − ε) εⁿ` sum to one for `ε < 1`. -/
theorem tsum_geometric_weights {ε : ℝ≥0∞} (hε : ε < 1) : ∑' n, (1 - ε) * ε ^ n = 1 := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_inv_cancel (tsub_pos_of_lt hε).ne' (by simp)

/-- The resolvent is a transition probability kernel for `ε < 1`. -/
theorem isMarkovKernel_resolvent (P : Kernel X X) [IsMarkovKernel P] {ε : ℝ≥0∞} (hε : ε < 1) :
    IsMarkovKernel (resolvent P ε) :=
  isMarkovKernel_sampledKernel P (tsum_geometric_weights hε)

/-! ### The operators `Pf` and `μP` -/

/-- `Pf(x) = ∫ P(x, dy) f(y)` for nonnegative `f` (MT p. 62). -/
noncomputable def kfun (P : Kernel X X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ := ∫⁻ y, f y ∂P x

/-- `Pf` is measurable for measurable `f`. -/
theorem measurable_kfun (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (kfun P f) := hf.lintegral_kernel

/-- `P 1_A (x) = P(x, A)`. -/
theorem kfun_indicator (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : X) :
    kfun P (A.indicator 1) x = P x A := lintegral_indicator_one hA

/-- `P1 = 1` for a transition probability kernel. -/
theorem kfun_one (P : Kernel X X) [IsMarkovKernel P] : kfun P 1 = 1 := by
  ext x; simp [kfun]

/-- `P` is monotone. -/
theorem kfun_mono (P : Kernel X X) {f g : X → ℝ≥0∞} (hfg : f ≤ g) : kfun P f ≤ kfun P g :=
  fun _ => lintegral_mono fun y => hfg y

/-- `P` is additive. -/
theorem kfun_add (P : Kernel X X) {f g : X → ℝ≥0∞} (hf : Measurable f) :
    kfun P (f + g) = kfun P f + kfun P g := by
  ext x; exact lintegral_add_left hf g

/-- `P` is positively homogeneous. -/
theorem kfun_const_mul (P : Kernel X X) (c : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    kfun P (fun y => c * f y) = fun x => c * kfun P f x := by
  ext x; exact lintegral_const_mul c hf

/-- `P(Qf) = (PQ)f`, where `PQ` is "first `P`, then `Q`", i.e. `Q ∘ₖ P`. -/
theorem kfun_comp (P Q : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    kfun P (kfun Q f) = kfun (Q ∘ₖ P) f := by
  ext x; exact (Kernel.lintegral_comp Q P x hf).symm

/-- `Pⁿ⁺¹f = P(Pⁿf)`. -/
theorem kfun_pow_succ (P : Kernel X X) (n : ℕ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    kfun (P ^ (n + 1)) f = kfun P (kfun (P ^ n) f) := by
  rw [kfun_comp P (P ^ n) hf, pow_succ]
  rfl

/-- `μP(A) = ∫ μ(dx) P(x, A)` (MT p. 62). -/
theorem measure_kernel_apply (μ : Measure X) (P : Kernel X X) {A : Set X}
    (hA : MeasurableSet A) : (P ∘ₘ μ) A = ∫⁻ x, P x A ∂μ :=
  Measure.bind_apply hA P.aemeasurable

/-- `(μP)Q = μ(PQ)`. -/
theorem measure_kernel_assoc (μ : Measure X) (P Q : Kernel X X) :
    Q ∘ₘ (P ∘ₘ μ) = (Q ∘ₖ P) ∘ₘ μ := Measure.comp_assoc

/-- Duality: `∫ Pf dμ = ∫ f d(μP)`. -/
theorem lintegral_kfun (μ : Measure X) (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, kfun P f x ∂μ = ∫⁻ y, f y ∂(P ∘ₘ μ) :=
  (Measure.lintegral_bind P.aemeasurable hf.aemeasurable).symm

/-- `μP` is a probability measure when `μ` is and `P` is Markov. -/
theorem isProbabilityMeasure_measure_kernel (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P] : IsProbabilityMeasure (P ∘ₘ μ) := by
  infer_instance

/-- `δ_x P = P(x, ·)`. -/
theorem dirac_kernel (P : Kernel X X) (x : X) : P ∘ₘ Measure.dirac x = P x :=
  Measure.dirac_bind P.measurable x

/-- `Pf(x) = ∫ P(x, dy) f(y)` for real `f` (MT p. 62). -/
noncomputable def kfunR (P : Kernel X X) (f : X → ℝ) (x : X) : ℝ := ∫ y, f y ∂P x

/-- `Pf` is measurable for measurable real `f`. -/
theorem measurable_kfunR (P : Kernel X X) [IsSFiniteKernel P] {f : X → ℝ}
    (hf : Measurable f) : Measurable (kfunR P f) :=
  (StronglyMeasurable.integral_kernel (κ := P) hf.stronglyMeasurable).measurable

/-- `|Pf| ≤ B` when `|f| ≤ B`. -/
theorem abs_kfunR_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (x : X) : |kfunR P f x| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P x) (f := f) (C := B)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  simpa [kfunR] using this

/-! ### The kernels `I_B` and `U` -/

/-- The kernel `I_B(x, A) = 1_{A ∩ B}(x)` (MT p. 66). -/
noncomputable def indKernel {B : Set X} (hB : MeasurableSet B) : Kernel X X :=
  Kernel.id.restrict hB

/-- `I_B(x, A) = 1_{A ∩ B}(x)`. -/
theorem indKernel_apply {B : Set X} (hB : MeasurableSet B) (x : X) {A : Set X}
    (hA : MeasurableSet A) : indKernel hB x A = (A ∩ B).indicator 1 x := by
  rw [indKernel, Kernel.restrict_apply' _ _ _ hA, Kernel.id_apply,
    Measure.dirac_apply' _ (hA.inter hB)]

/-- `(P I_B)(x, A) = P(x, A ∩ B)`: "move by `P`, then kill the path outside `B`". -/
theorem comp_indKernel_apply (P : Kernel X X) {B : Set X} (hB : MeasurableSet B) (x : X)
    {A : Set X} (hA : MeasurableSet A) : (indKernel hB ∘ₖ P) x A = P x (A ∩ B) := by
  rw [Kernel.comp_apply' _ _ _ hA]
  simp_rw [indKernel_apply hB _ hA]
  exact lintegral_indicator_one (hA.inter hB)

/-- `P I_B` is substochastic. -/
theorem isSubstochasticKernel_comp_indKernel (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) : IsSubstochasticKernel (indKernel hB ∘ₖ P) := fun x => by
  rw [comp_indKernel_apply P hB x MeasurableSet.univ]
  exact prob_le_one

/-- The potential kernel `U = Σ_{n ≥ 1} Pⁿ` (3.30), MT p. 64. -/
noncomputable def potKernel (P : Kernel X X) : Kernel X X := Kernel.sum fun n => P ^ (n + 1)

/-- (3.30): `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A)`. -/
theorem potKernel_apply (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    potKernel P x A = ∑' n, (P ^ (n + 1)) x A :=
  Kernel.sum_apply' _ _ hA

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Markov property (MT §3.4.2)

Meyn and Tweedie, §3.4.2, pp. 61–63. `shift n` is the shift `θⁿ` on paths,
`(θⁿω)ᵢ = ω_{n+i}` (p. 63), so `H ∘ θⁿ = θⁿH`.

* `pathMeasure_map_coord`, `pathKernel_map_coord` (3.8): the law of `Φₙ` under `P_μ` is `μPⁿ`,
  and `P_x(Φₙ ∈ A) = Pⁿ(x, A)`; `pathKernel_coord_chapmanKolmogorov` is (3.24).
* `markov_measure`: for `G ∈ 𝓕ₙ^Φ`, the law of `θⁿΦ` on `G` is `∫_G P_{Φₙ}(·) dP_μ`. This is the
  Markov property in its strongest form, as an identity of measures on path space.
* `markov_lintegral_mul`: `E_μ[F · H ∘ θⁿ] = E_μ[F · E_{Φₙ}[H]]` for `𝓕ₙ^Φ`-measurable `F ≥ 0`.
* `markov_lintegral`, `markov_setIntegral`: `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ` for
  nonnegative and for integrable `H`.
* `markov_property` (3.28), p. 63: `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for every
  measurable `H` with `θⁿH` integrable; `markov_property_bdd` for bounded `H`.
* **Proposition 3.4.3** (`proposition_3_4_3`, p. 63), (3.27):
  `E_μ[h(Φₙ₊₁, Φₙ₊₂, …) | Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]` for bounded measurable `h`.
* `isMarkovChain_of_step`: a process adapted to a filtration whose one-step conditional laws are
  given by `Q` is a Markov chain with kernel `Q`. Hence `skeleton_isMarkovChain` (3.25),
  p. 61: the `m`-skeleton `(Φ_{mn})ₙ` is a Markov chain with transition kernel `Pᵐ`.

**Corrections.** None. The book states (3.27) and (3.28) for bounded `h`; they hold for every
`h` with `θⁿH` integrable (`markov_property`).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The shift -/

/-- The shift `θⁿ` on paths: `(θⁿω)ᵢ = ω_{n+i}` (MT p. 63). -/
def shift (n : ℕ) (ω : ℕ → X) : ℕ → X := fun i => ω (n + i)

/-- The shift is measurable. -/
theorem measurable_shift (n : ℕ) : Measurable (shift (X := X) n) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (n + i)

omit [MeasurableSpace X] in
/-- `θ⁰ = id`. -/
@[simp] theorem shift_zero (ω : ℕ → X) : shift 0 ω = ω := by
  ext i; simp [shift]

omit [MeasurableSpace X] in
/-- `θᵐ ∘ θⁿ = θⁿ⁺ᵐ`. -/
theorem shift_shift (m n : ℕ) (ω : ℕ → X) : shift m (shift n ω) = shift (n + m) ω := by
  ext i; simp [shift, add_assoc]

omit [MeasurableSpace X] in
/-- `Φᵢ ∘ θⁿ = Φₙ₊ᵢ` (MT p. 63). -/
@[simp] theorem shift_apply (n i : ℕ) (ω : ℕ → X) : shift n ω i = ω (n + i) := rfl

/-! ### Integrals against `κ ∘ₘ ν` -/

/-- `∫ f d(κ ∘ₘ ν) = ∫ ∫ f dκ(x) ν(dx)` for integrable `f`. -/
theorem integral_measure_comp {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν] {f : Z → ℝ}
    (hf : Integrable f (κ ∘ₘ ν)) : ∫ z, f z ∂(κ ∘ₘ ν) = ∫ y, ∫ z, f z ∂κ y ∂ν := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-! ### The law of `Φₙ` -/

/-- (3.8): the law of `Φₙ` under `P_μ` is `μPⁿ`. -/
theorem pathMeasure_map_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (pathMeasure P μ).map (fun ω => ω n) = (P ^ n) ∘ₘ μ := by
  induction n with
  | zero => rw [pathMeasure_map_zero, pow_zero]; exact Measure.id_comp.symm
  | succ n ih =>
    ext A hA
    have hmA : Measurable (fun y => P y A) := Kernel.measurable_coe _ hA
    rw [Measure.map_apply (measurable_pi_apply (n + 1) : Measurable fun ω : ℕ → X => ω (n + 1))
      hA, ← lintegral_indicator_one (measurable_pi_apply (n + 1) hA)]
    have h1 := setLIntegral_succ P μ (n := n) MeasurableSet.univ
      (measurable_one.indicator hA : Measurable (A.indicator (1 : X → ℝ≥0∞)))
    simp only [Measure.restrict_univ, lintegral_indicator_one hA] at h1
    have h2 : ((fun ω : ℕ → X => ω (n + 1)) ⁻¹' A).indicator (1 : (ℕ → X) → ℝ≥0∞) =
        fun ω => A.indicator 1 (ω (n + 1)) := by
      ext ω; by_cases h : ω (n + 1) ∈ A <;> simp [h]
    rw [h2, h1, ← lintegral_map hmA (measurable_pi_apply n), ih, pow_succ',
      ← measure_kernel_apply _ _ hA, measure_kernel_assoc]
    rfl

/-- (3.8): `P_x(Φₙ ∈ ·) = Pⁿ(x, ·)`. -/
theorem pathKernel_map_coord (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) :
    (pathKernel P x).map (fun ω => ω n) = (P ^ n) x := by
  rw [← pathMeasure_dirac, pathMeasure_map_coord, dirac_kernel]

/-- `P_x(Φₙ ∈ A) = Pⁿ(x, A)`. -/
theorem pathKernel_coord_mem (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) {A : Set X}
    (hA : MeasurableSet A) : pathKernel P x {ω | ω n ∈ A} = (P ^ n) x A := by
  rw [← pathKernel_map_coord P x n,
    Measure.map_apply (measurable_pi_apply n : Measurable fun ω : ℕ → X => ω n) hA]
  rfl

/-- (3.24), MT p. 61: `P_x(Φₙ ∈ A) = ∫ P_x(Φₘ ∈ dy) P_y(Φₙ₋ₘ ∈ A)` for `m ≤ n`. -/
theorem pathKernel_coord_chapmanKolmogorov (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {m n : ℕ} (hmn : m ≤ n) {A : Set X} (hA : MeasurableSet A) :
    pathKernel P x {ω | ω n ∈ A} =
      ∫⁻ y, pathKernel P y {ω | ω (n - m) ∈ A} ∂(pathKernel P x).map (fun ω => ω m) := by
  simp_rw [pathKernel_coord_mem P _ _ hA, pathKernel_map_coord]
  exact theorem_3_4_2 P hmn x hA

/-! ### The Markov property -/

/-- **The Markov property as an identity of measures.** For `G ∈ 𝓕ₙ^Φ`, the law of the shifted
path `θⁿΦ` restricted to `G` is the mixture of the `P_y` over the law of `Φₙ` restricted to
`G`. -/
theorem markov_measure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G) :
    ((pathMeasure P μ).restrict G).map (shift n) =
      pathKernel P ∘ₘ (((pathMeasure P μ).restrict G).map fun ω => ω n) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have := isMarkovKernel_pathKernel P
  have hGm : MeasurableSet G := (natFilt (X := X)).le n _ hG
  have hn : Measurable fun ω : ℕ → X => ω n := measurable_pi_apply n
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨m, A, hA, rfl⟩
    have hB := measurableSet_boxSet m hA
    rw [Measure.map_apply (measurable_shift n) hB, Measure.restrict_apply
      (measurable_shift n hB), Measure.bind_apply hB (Kernel.aemeasurable _),
      lintegral_map (Kernel.measurable_coe _ hB) hn, inter_comm]
    simp_rw [pathKernel_boxSet P _ m hA]
    exact measure_inter_shift_box P μ m hA hG
  · rw [Measure.map_apply (measurable_shift n) MeasurableSet.univ,
      Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp [Measure.map_apply hn MeasurableSet.univ]

/-- **The Markov property** for nonnegative functionals: for `G ∈ 𝓕ₙ^Φ` and measurable
`H ≥ 0`, `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ`. -/
theorem markov_lintegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in G, H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω in G, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  rw [← lintegral_map hH (measurable_shift n), markov_measure P μ hG,
    Measure.lintegral_bind (Kernel.aemeasurable _) hH.aemeasurable,
    lintegral_map hH.lintegral_kernel (measurable_pi_apply n)]

/-- **The Markov property** with an `𝓕ₙ^Φ`-measurable weight: for `F ≥ 0` measurable for
`𝓕ₙ^Φ` and measurable `H ≥ 0`, `E_μ[F · H ∘ θⁿ] = E_μ[F · E_{Φₙ}[H]]`. -/
theorem markov_lintegral_mul (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {F : (ℕ → X) → ℝ≥0∞} (hF : Measurable[natFilt n] F)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, F ω * H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω, F ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have hle := (natFilt (X := X)).le n
  have hG : Measurable fun ω => H (shift n ω) := hH.comp (measurable_shift n)
  have hK : Measurable fun ω : ℕ → X => ∫⁻ ω', H ω' ∂pathKernel P (ω n) :=
    hH.lintegral_kernel.comp (measurable_pi_apply n)
  refine Measurable.ennreal_induction (motive := fun F => ∫⁻ ω, F ω * H (shift n ω)
      ∂pathMeasure P μ = ∫⁻ ω, F ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ)
    ?_ ?_ ?_ hF
  · intro c s hs
    have hs' : MeasurableSet s := hle _ hs
    have e1 : ∀ ω, s.indicator (fun _ => c) ω * H (shift n ω) =
        s.indicator (fun ω => c * H (shift n ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∀ ω, s.indicator (fun _ => c) ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) =
        s.indicator (fun ω => c * ∫⁻ ω', H ω' ∂pathKernel P (ω n)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    simp_rw [e1, e2, lintegral_indicator hs', lintegral_const_mul _ hG,
      lintegral_const_mul _ hK, markov_lintegral P μ hs hH]
  · intro f g _ hf hg ihf ihg
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => f ω * H (shift n ω)) ((hf.mono hle le_rfl).mul hG),
      lintegral_add_left (f := fun ω => f ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n))
        ((hf.mono hle le_rfl).mul hK), ihf, ihg]
  · intro f hf hmono ih
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun k ω => f k ω * H (shift n ω))
        (fun k => ((hf k).mono hle le_rfl).mul hG)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _),
      lintegral_iSup (f := fun k ω => f k ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n))
        (fun k => ((hf k).mono hle le_rfl).mul hK)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _)]
    simp_rw [ih]

/-- The unconditional form: `E_μ[H ∘ θⁿ] = E_μ[E_{Φₙ}[H]]`. -/
theorem markov_lintegral_univ (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  simpa using markov_lintegral P μ (n := n) MeasurableSet.univ hH

/-- **The Markov property** for integrable functionals: for `G ∈ 𝓕ₙ^Φ` and measurable `H` with
`H ∘ θⁿ` integrable on `G`, `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ`. -/
theorem markov_setIntegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : IntegrableOn (fun ω => H (shift n ω)) G (pathMeasure P μ)) :
    ∫ ω in G, H (shift n ω) ∂pathMeasure P μ =
      ∫ ω in G, ∫ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hmeas := markov_measure P μ hG
  have hi : Integrable H (((pathMeasure P μ).restrict G).map (shift n)) :=
    (integrable_map_measure hH.aestronglyMeasurable (measurable_shift n).aemeasurable).2 hint
  rw [hmeas] at hi
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  calc ∫ ω in G, H (shift n ω) ∂pathMeasure P μ
      = ∫ ω', H ω' ∂(((pathMeasure P μ).restrict G).map (shift n)) :=
        (integral_map (measurable_shift n).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ ω', H ω' ∂(pathKernel P ∘ₘ (((pathMeasure P μ).restrict G).map fun ω => ω n)) := by
        rw [hmeas]
    _ = ∫ y, ∫ ω', H ω' ∂pathKernel P y ∂(((pathMeasure P μ).restrict G).map fun ω => ω n) :=
        integral_measure_comp _ _ hi
    _ = ∫ ω in G, ∫ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        integral_map (measurable_pi_apply n).aemeasurable hk.aestronglyMeasurable

/-- `ω ↦ E_{Φₙ(ω)}[H]` is `𝓕ₙ^Φ`-strongly measurable. -/
theorem stronglyMeasurable_expect_coord (P : Kernel X X) [IsMarkovKernel P] (n : ℕ)
    {H : (ℕ → X) → ℝ} (hH : Measurable H) :
    StronglyMeasurable[natFilt n] fun ω : ℕ → X => ∫ ω', H ω' ∂pathKernel P (ω n) := by
  have := isMarkovKernel_pathKernel P
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  exact hk.comp_measurable (measurable_coord_natFilt n)

/-- `ω ↦ E_{Φₙ(ω)}[H]` is integrable when `H ∘ θⁿ` is. -/
theorem integrable_expect_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ)) :
    Integrable (fun ω : ℕ → X => ∫ ω', H ω' ∂pathKernel P (ω n)) (pathMeasure P μ) := by
  refine ⟨((stronglyMeasurable_expect_coord P n hH).mono
    ((natFilt (X := X)).le n)).aestronglyMeasurable, ?_⟩
  have hlin := markov_lintegral_univ P μ n (H := fun ω => ‖H ω‖ₑ) hH.enorm
  calc ∫⁻ ω, ‖∫ ω', H ω' ∂pathKernel P (ω n)‖ₑ ∂pathMeasure P μ
      ≤ ∫⁻ ω, ∫⁻ ω', ‖H ω'‖ₑ ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ‖H (shift n ω)‖ₑ ∂pathMeasure P μ := hlin.symm
    _ < ∞ := hint.2

/-- **The Markov property** (3.28), MT p. 63: `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for
measurable `H` with `θⁿH` integrable. -/
theorem markov_property (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ)) :
    (pathMeasure P μ)[fun ω => H (shift n ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', H ω' ∂pathKernel P (ω n) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hg := integrable_expect_coord P μ n hH hint
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((natFilt (X := X)).le n) hint
    (fun s _ _ => hg.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_expect_coord P n hH).aestronglyMeasurable).symm
  exact (markov_setIntegral P μ hs hH hint.integrableOn).symm

/-- `H ∘ θⁿ` is integrable for bounded measurable `H`. -/
theorem integrable_shift_of_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  exact Integrable.of_bound (hH.comp (measurable_shift n)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)

/-- (3.28) for bounded measurable `H`, as stated in MT p. 63. -/
theorem markov_property_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) :
    (pathMeasure P μ)[fun ω => H (shift n ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', H ω' ∂pathKernel P (ω n) :=
  markov_property P μ n hH (integrable_shift_of_bdd P μ n hH hB)

/-- **Proposition 3.4.3** (MT p. 63), (3.27): for bounded measurable `h` on path space,
`E_μ[h(Φₙ₊₁, Φₙ₊₂, …) | Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]`, `P_μ`-a.s. -/
theorem proposition_3_4_3 (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {h : (ℕ → X) → ℝ} (hh : Measurable h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    (pathMeasure P μ)[fun ω => h (shift (n + 1) ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', h (shift 1 ω') ∂pathKernel P (ω n) := by
  have := markov_property_bdd P μ n (hh.comp (measurable_shift 1)) (fun ω => hB (shift 1 ω))
  simp only [Function.comp_apply, shift_shift] at this
  exact this

/-! ### Markov chains from the one-step property; skeletons -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] in
/-- A process `Ψ` adapted to a filtration `𝓖`, with `Ψ₀ ∼ μ` and one-step conditional laws given
by `Q` (`∫_G f(Ψₙ₊₁) = ∫_G Qf(Ψₙ)` for `G ∈ 𝓖ₙ`), is a Markov chain with kernel `Q` and initial
distribution `μ`. -/
theorem isMarkovChain_of_step (Q : Kernel X X) (μ : Measure X) {pr : Measure Ω}
    {Ψ : ℕ → Ω → X} {𝓖 : Filtration ℕ mΩ} (hΨ : ∀ n, Measurable[𝓖 n] (Ψ n))
    (h0 : pr.map (Ψ 0) = μ)
    (hstep : ∀ n G, MeasurableSet[𝓖 n] G → ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ ω in G, f (Ψ (n + 1) ω) ∂pr = ∫⁻ ω in G, ∫⁻ y, f y ∂Q (Ψ n ω) ∂pr) :
    IsMarkovChain Q μ pr Ψ := by
  have hΨm : ∀ n, Measurable (Ψ n) := fun n => (hΨ n).mono (𝓖.le n) le_rfl
  have key : ∀ m (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) → ∀ n G, MeasurableSet[𝓖 n] G →
      pr (G ∩ {ω | ∀ i ≤ m, Ψ (n + i) ω ∈ A i}) = ∫⁻ ω in G, cylFn Q m A (Ψ n ω) ∂pr := by
    intro m
    induction m with
    | zero =>
      intro A hA n G hG
      have hset : {ω | ∀ i ≤ 0, Ψ (n + i) ω ∈ A i} = Ψ n ⁻¹' A 0 := by ext ω; simp
      have hm : MeasurableSet (Ψ n ⁻¹' A 0) := hΨm n (hA 0)
      have hind : (fun ω => cylFn Q 0 A (Ψ n ω)) = (Ψ n ⁻¹' A 0).indicator 1 := by
        ext ω; by_cases h : Ψ n ω ∈ A 0 <;> simp [cylFn, h]
      rw [hset, hind, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_comm]
    | succ m ih =>
      intro A hA n G hG
      set A' : ℕ → Set X := fun i => A (i + 1)
      have hA' : ∀ i, MeasurableSet (A' i) := fun i => hA (i + 1)
      have hG' : MeasurableSet[𝓖 n] (G ∩ Ψ n ⁻¹' A 0) := hG.inter (hΨ n (hA 0))
      have hset : G ∩ {ω | ∀ i ≤ m + 1, Ψ (n + i) ω ∈ A i} =
          (G ∩ Ψ n ⁻¹' A 0) ∩ {ω | ∀ i ≤ m, Ψ (n + 1 + i) ω ∈ A' i} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, A']
        constructor
        · rintro ⟨hg, h⟩
          refine ⟨⟨hg, by simpa using h 0 (Nat.zero_le _)⟩, fun i hi => ?_⟩
          have := h (i + 1) (by omega)
          rwa [show n + (i + 1) = n + 1 + i by omega] at this
        · rintro ⟨⟨hg, h0⟩, h⟩
          refine ⟨hg, fun i hi => ?_⟩
          rcases i with _ | i
          · simpa using h0
          · have := h i (by omega)
            rwa [show n + 1 + i = n + (i + 1) by omega] at this
      have hmeas := measurable_cylFn Q m hA'
      rw [hset, ih A' hA' (n + 1) _ (𝓖.mono (Nat.le_succ n) _ hG'),
        hstep n _ hG' _ hmeas]
      have hmn : MeasurableSet (Ψ n ⁻¹' A 0) := hΨm n (hA 0)
      have hind : (fun ω => cylFn Q (m + 1) A (Ψ n ω)) =
          (Ψ n ⁻¹' A 0).indicator (fun ω => ∫⁻ y, cylFn Q m A' y ∂Q (Ψ n ω)) := by
        ext ω; by_cases h : Ψ n ω ∈ A 0 <;> simp [cylFn, h, A']
      rw [hind, setLIntegral_indicator hmn, inter_comm]
  refine ⟨hΨm, fun n A hA => ?_⟩
  have := key n A hA 0 univ MeasurableSet.univ
  simp only [univ_inter, zero_add, Measure.restrict_univ] at this
  rw [this, ← lintegral_map (measurable_cylFn Q n hA) (hΨm 0), h0]

/-- The filtration `(𝓕_{mn}^Φ)ₙ` along the `m`-skeleton. -/
def skeletonFilt (m : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) where
  seq n := natFilt (X := X) (m * n)
  mono' _ _ hij := (natFilt (X := X)).mono (Nat.mul_le_mul_left m hij)
  le' n := (natFilt (X := X)).le (m * n)

/-- (3.25), MT p. 61: the `m`-skeleton `(Φ_{mn})ₙ` of the chain is a Markov chain with
transition kernel `Pᵐ`, under every `P_μ`. In particular `P_x(Φ_{mn} ∈ A) = Pᵐⁿ(x, A)`
(`pathKernel_coord_mem`). -/
theorem skeleton_isMarkovChain (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) :
    IsMarkovChain (skeleton P m) μ (pathMeasure P μ) (fun n ω => ω (m * n)) := by
  refine isMarkovChain_of_step (𝓖 := skeletonFilt m) _ μ
    (fun n => measurable_coord_natFilt (m * n)) (by simpa using pathMeasure_map_zero P μ)
    fun n G hG f hf => ?_
  have hH : Measurable fun ω : ℕ → X => f (ω m) := hf.comp (measurable_pi_apply m)
  have h := markov_lintegral P μ (n := m * n) hG hH
  simp only [shift_apply] at h
  rw [show m * (n + 1) = m * n + m by ring, h]
  refine setLIntegral_congr_fun ((skeletonFilt m).le n _ hG) fun ω _ => ?_
  rw [← lintegral_map hf (measurable_pi_apply m), pathKernel_map_coord]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stopping times and the strong Markov property (MT §3.4.3)

Meyn and Tweedie, §3.4.3, pp. 64–66. A stopping time for the chain is a stopping time
`ζ : (ℕ → X) → ℕ ∪ {∞}` (Mathlib's `WithTop ℕ`) for the natural filtration `𝓕ₙ^Φ` of the
coordinate process (p. 65). `𝓕_ζ^Φ` is Mathlib's `hζ.measurableSpace`.

* `iSup_natFilt`: `⋁ₙ 𝓕ₙ^Φ` is the product σ-algebra.
* `measurableSet_stoppedField_iff` (p. 66): `A ∈ 𝓕_ζ^Φ` iff `A` is an event and
  `A ∩ {ζ = n} ∈ 𝓕ₙ^Φ` for every `n`; this is the book's definition of `𝓕_ζ^Φ`.
* `stoppedState ζ = Φ_ζ` and `shiftAt ζ = θ^ζ` (p. 66), meaningful on `{ζ < ∞}`;
  `measurable_stoppedState`, `measurable_shiftAt`.
* `measurable_stoppedField_indicator`: `1_{ζ<∞} k(Φ_ζ)` is `𝓕_ζ^Φ`-measurable.
* `strong_markov_lintegral_mul`: the same with an `𝓕_ζ^Φ`-measurable weight `F ≥ 0`.
* `strong_markov_lintegral`, `strong_markov_measure`, `strong_markov_setIntegral`: for
  `A ∈ 𝓕_ζ^Φ`, `∫_{A ∩ {ζ<∞}} H ∘ θ^ζ dP_μ = ∫_{A ∩ {ζ<∞}} E_{Φ_ζ}[H] dP_μ`, for nonnegative and
  for integrable `H`, and as an identity of measures on path space.
* `strong_markov_property` (3.32): `E_μ[1_{ζ<∞} θ^ζH | 𝓕_ζ^Φ] = 1_{ζ<∞} E_{Φ_ζ}[H]`, `P_μ`-a.s.,
  for measurable `H` with `1_{ζ<∞} θ^ζH` integrable.
* `StrongMarkovProperty` (p. 66): the property (3.32) for every initial law, bounded measurable
  `H` and stopping time; **Proposition 3.4.6** (`proposition_3_4_6`, p. 66): every chain has it.

The proof is the book's: decompose over `{ζ = n}` and use the Markov property at each fixed
`n` (`markov_lintegral`, `markov_setIntegral`).

**Corrections.** The book writes (3.32) as an identity "on the set `{ζ < ∞}`" between
conditional expectations of `θ^ζH`, which is only defined on `{ζ < ∞}`. The precise statement
proved here multiplies both sides by `1_{ζ<∞}`, an `𝓕_ζ^Φ`-measurable factor.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The σ-algebra `𝓕_ζ^Φ` -/

/-- The natural filtration generates the product σ-algebra: `⋁ₙ 𝓕ₙ^Φ = B(X)^ℕ`. -/
theorem iSup_natFilt :
    ⨆ n, natFilt (X := X) n = (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) := by
  refine le_antisymm (iSup_le (natFilt (X := X)).le) ?_
  refine iSup_le fun i => ?_
  exact ((measurable_coord_natFilt i).comap_le).trans (le_iSup (fun n => natFilt (X := X) n) i)

omit [MeasurableSpace X] in
/-- On `{ζ ≤ i}`, `ζ` takes one of the values `0, …, i`. -/
theorem setOf_le_eq_biUnion (τ : (ℕ → X) → WithTop ℕ) (i : ℕ) :
    {ω | τ ω ≤ WithTop.some i} = ⋃ n ∈ Finset.range (i + 1), {ω | τ ω = n} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro h
    cases ht : τ ω with
    | top => rw [ht] at h; simp at h
    | coe t => rw [ht] at h; exact ⟨t, Nat.lt_succ_of_le (WithTop.coe_le_coe.1 h), rfl⟩
  · rintro ⟨n, hn, h⟩
    rw [h]; exact WithTop.coe_le_coe.2 (Nat.le_of_lt_succ hn)

omit [MeasurableSpace X] in
/-- `{ζ = ∞}` is the complement of `⋃ₙ {ζ = n}`. -/
theorem setOf_ne_top_eq_iUnion (τ : (ℕ → X) → WithTop ℕ) :
    {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, {ω | τ ω = n} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
    exact ⟨t, ht.symm⟩
  · rintro ⟨n, h⟩; rw [h]; exact WithTop.coe_ne_top

/-- `{ζ < ∞}` is an event. -/
theorem measurableSet_ne_top {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : MeasurableSet {ω | τ ω ≠ ⊤} := by
  rw [setOf_ne_top_eq_iUnion]
  exact MeasurableSet.iUnion fun n =>
    (natFilt (X := X)).le n _ (hτ.measurableSet_eq_of_countable n)

/-- (MT p. 66) `A ∈ 𝓕_ζ^Φ` iff `A` is an event with `A ∩ {ζ = n} ∈ 𝓕ₙ^Φ` for all `n`: Mathlib's
`𝓕_ζ` is the book's. -/
theorem measurableSet_stoppedField_iff {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) (A : Set (ℕ → X)) :
    MeasurableSet[hτ.measurableSpace] A ↔
      MeasurableSet A ∧ ∀ n : ℕ, MeasurableSet[natFilt n] (A ∩ {ω | τ ω = n}) := by
  rw [hτ.measurableSet, iSup_natFilt]
  refine and_congr Iff.rfl ⟨fun h n => ?_, fun h i => ?_⟩
  · have : A ∩ {ω | τ ω = n} = (A ∩ {ω | τ ω ≤ n}) ∩ {ω | τ ω = n} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨ha, he⟩; exact ⟨⟨ha, he.le⟩, he⟩
      · rintro ⟨⟨ha, _⟩, he⟩; exact ⟨ha, he⟩
    rw [this]
    exact (h n).inter (hτ.measurableSet_eq_of_countable n)
  · rw [setOf_le_eq_biUnion, inter_iUnion₂]
    refine Finset.measurableSet_biUnion _ fun n hn => ?_
    exact (natFilt (X := X)).mono (Nat.le_of_lt_succ (Finset.mem_range.1 hn)) _ (h n)

/-- `{ζ < ∞} ∈ 𝓕_ζ^Φ`. -/
theorem measurableSet_stoppedField_ne_top {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} := by
  rw [measurableSet_stoppedField_iff]
  refine ⟨measurableSet_ne_top hτ, fun n => ?_⟩
  have : {ω : ℕ → X | τ ω ≠ ⊤} ∩ {ω | τ ω = n} = {ω | τ ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_right_iff_imp]
    intro h; rw [h]; exact WithTop.coe_ne_top
  rw [this]
  exact hτ.measurableSet_eq_of_countable n

/-! ### `Φ_ζ` and `θ^ζ` -/

/-- `Φ_ζ = Φₙ` on `{ζ = n}` (MT p. 66); its value on `{ζ = ∞}` is irrelevant. -/
noncomputable def stoppedState (τ : (ℕ → X) → WithTop ℕ) (ω : ℕ → X) : X := ω (τ ω).untopA

/-- The shift `θ^ζ = θⁿ` on `{ζ = n}` (MT p. 66). -/
noncomputable def shiftAt (τ : (ℕ → X) → WithTop ℕ) (ω : ℕ → X) : ℕ → X := shift (τ ω).untopA ω

omit [MeasurableSpace X] in
/-- On `{ζ = n}`, `Φ_ζ = Φₙ`. -/
theorem stoppedState_of_eq {τ : (ℕ → X) → WithTop ℕ} {ω : ℕ → X} {n : ℕ} (h : τ ω = n) :
    stoppedState τ ω = ω n := by
  simp only [stoppedState, h]; rfl

omit [MeasurableSpace X] in
/-- On `{ζ = n}`, `θ^ζ = θⁿ`. -/
theorem shiftAt_of_eq {τ : (ℕ → X) → WithTop ℕ} {ω : ℕ → X} {n : ℕ} (h : τ ω = n) :
    shiftAt τ ω = shift n ω := by
  simp only [shiftAt, h]; rfl

/-- A function on path space that agrees with a measurable `Fₙ` on each `{ζ = n}` and with a
measurable `F_∞` on `{ζ = ∞}` is measurable. -/
theorem measurable_of_stopping_pieces {β : Type*} [MeasurableSpace β]
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ) {F : (ℕ → X) → β}
    (Fn : ℕ → (ℕ → X) → β) (Ftop : (ℕ → X) → β) (hFn : ∀ n, Measurable (Fn n))
    (hFtop : Measurable Ftop) (hn : ∀ (n : ℕ) ω, τ ω = n → F ω = Fn n ω)
    (htop : ∀ ω, τ ω = ⊤ → F ω = Ftop ω) : Measurable F := by
  intro S hS
  have hset : F ⁻¹' S = (⋃ n : ℕ, {ω | τ ω = n} ∩ Fn n ⁻¹' S) ∪
      ({ω | τ ω ≠ ⊤}ᶜ ∩ Ftop ⁻¹' S) := by
    ext ω
    simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq,
      mem_compl_iff, not_not]
    cases ht : τ ω with
    | top => simp [htop ω ht]
    | coe t =>
      simp only [WithTop.coe_ne_top, false_and, or_false]
      constructor
      · intro h; exact ⟨t, rfl, by rwa [← hn t ω ht]⟩
      · rintro ⟨k, hk, h⟩
        rw [WithTop.coe_inj.1 hk] at ht
        rwa [hn k ω ht]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun n => ?_)
    ((measurableSet_ne_top hτ).compl.inter (hFtop hS))
  exact ((natFilt (X := X)).le n _ (hτ.measurableSet_eq_of_countable n)).inter (hFn n hS)

/-- `Φ_ζ` is measurable. -/
theorem measurable_stoppedState {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : Measurable (stoppedState τ) :=
  measurable_of_stopping_pieces hτ (fun n ω => ω n) (fun ω => ω (⊤ : WithTop ℕ).untopA)
    (fun n => measurable_pi_apply n) (measurable_pi_apply _)
    (fun _ _ h => stoppedState_of_eq h) (fun ω h => by simp [stoppedState, h])

/-- `θ^ζ` is measurable. -/
theorem measurable_shiftAt {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : Measurable (shiftAt τ) :=
  measurable_of_stopping_pieces hτ (fun n ω => shift n ω) (fun ω => shift (⊤ : WithTop ℕ).untopA ω)
    (fun n => measurable_shift n) (measurable_shift _)
    (fun _ _ h => shiftAt_of_eq h) (fun ω h => by simp [shiftAt, h])

/-- `1_{ζ<∞} k(Φ_ζ)` is `𝓕_ζ^Φ`-measurable for measurable `k`. -/
theorem measurable_stoppedField_indicator {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {k : X → ℝ} (hk : Measurable k) :
    Measurable[hτ.measurableSpace]
      ({ω | τ ω ≠ ⊤}.indicator fun ω => k (stoppedState τ ω)) := by
  intro S hS
  rw [measurableSet_stoppedField_iff]
  refine ⟨((hk.comp (measurable_stoppedState hτ)).indicator (measurableSet_ne_top hτ)) hS,
    fun n => ?_⟩
  have : ({ω | τ ω ≠ ⊤}.indicator fun ω => k (stoppedState τ ω)) ⁻¹' S ∩ {ω | τ ω = n} =
      {ω | ω n ∈ k ⁻¹' S} ∩ {ω | τ ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hne : τ ω ≠ ⊤ := by rw [h2]; exact WithTop.coe_ne_top
      rw [indicator_of_mem (show ω ∈ {ω | τ ω ≠ ⊤} from hne), stoppedState_of_eq h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hne : τ ω ≠ ⊤ := by rw [h2]; exact WithTop.coe_ne_top
      rw [indicator_of_mem (show ω ∈ {ω | τ ω ≠ ⊤} from hne), stoppedState_of_eq h2]
      exact ⟨h1, h2⟩
  rw [this]
  exact (measurableSet_coord_natFilt le_rfl (hk hS)).inter (hτ.measurableSet_eq_of_countable n)

/-! ### The strong Markov property -/

omit [MeasurableSpace X] in
/-- `A ∩ {ζ < ∞}` is the disjoint union of the `A ∩ {ζ = n}`. -/
theorem inter_ne_top_eq_iUnion (τ : (ℕ → X) → WithTop ℕ) (A : Set (ℕ → X)) :
    A ∩ {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, A ∩ {ω | τ ω = n} := by
  rw [setOf_ne_top_eq_iUnion, inter_iUnion]

omit [MeasurableSpace X] in
/-- The pieces `A ∩ {ζ = n}` are pairwise disjoint. -/
theorem pairwise_disjoint_inter_eq (τ : (ℕ → X) → WithTop ℕ) (A : Set (ℕ → X)) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => A ∩ {ω | τ ω = n}) := by
  intro i j hij
  refine Set.disjoint_left.2 fun ω hi hj => hij ?_
  exact WithTop.coe_inj.1 (hi.2.symm.trans hj.2)

/-- **The strong Markov property** for nonnegative functionals: for a stopping time `ζ`,
`A ∈ 𝓕_ζ^Φ` and measurable `H ≥ 0`,
`∫_{A ∩ {ζ<∞}} H ∘ θ^ζ dP_μ = ∫_{A ∩ {ζ<∞}} E_{Φ_ζ}[H] dP_μ`. -/
theorem strong_markov_lintegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[hτ.measurableSpace] A) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω)
        ∂pathMeasure P μ := by
  rw [measurableSet_stoppedField_iff] at hA
  have hm : ∀ n : ℕ, MeasurableSet (A ∩ {ω | τ ω = n}) := fun n =>
    (natFilt (X := X)).le n _ (hA.2 n)
  rw [inter_ne_top_eq_iUnion, lintegral_iUnion hm (pairwise_disjoint_inter_eq τ A),
    lintegral_iUnion hm (pairwise_disjoint_inter_eq τ A)]
  refine tsum_congr fun n => ?_
  calc ∫⁻ ω in A ∩ {ω | τ ω = n}, H (shiftAt τ ω) ∂pathMeasure P μ
      = ∫⁻ ω in A ∩ {ω | τ ω = n}, H (shift n ω) ∂pathMeasure P μ :=
        setLIntegral_congr_fun (hm n) fun ω hω => by rw [shiftAt_of_eq hω.2]
    _ = ∫⁻ ω in A ∩ {ω | τ ω = n}, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        markov_lintegral P μ (hA.2 n) hH
    _ = _ := setLIntegral_congr_fun (hm n) fun ω hω => by rw [stoppedState_of_eq hω.2]

/-- **The strong Markov property** with an `𝓕_ζ^Φ`-measurable weight: for `F ≥ 0` measurable
for `𝓕_ζ^Φ` and measurable `H ≥ 0`,
`E_μ[F · H ∘ θ^ζ; ζ < ∞] = E_μ[F · E_{Φ_ζ}[H]; ζ < ∞]`. -/
theorem strong_markov_lintegral_mul (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {F : (ℕ → X) → ℝ≥0∞}
    (hF : Measurable[hτ.measurableSpace] F) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in {ω | τ ω ≠ ⊤}, F ω * H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫⁻ ω in {ω | τ ω ≠ ⊤}, F ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω)
        ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have hle := hτ.measurableSpace_le
  have hG : Measurable fun ω => H (shiftAt τ ω) := hH.comp (measurable_shiftAt hτ)
  have hK : Measurable fun ω : ℕ → X => ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) :=
    hH.lintegral_kernel.comp (measurable_stoppedState hτ)
  refine Measurable.ennreal_induction (motive := fun F => ∫⁻ ω in {ω | τ ω ≠ ⊤},
      F ω * H (shiftAt τ ω) ∂pathMeasure P μ = ∫⁻ ω in {ω | τ ω ≠ ⊤},
        F ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) ∂pathMeasure P μ) ?_ ?_ ?_ hF
  · intro c s hs
    have hs' : MeasurableSet s := hle _ hs
    have e1 : ∀ ω, s.indicator (fun _ => c) ω * H (shiftAt τ ω) =
        s.indicator (fun ω => c * H (shiftAt τ ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∀ ω, s.indicator (fun _ => c) ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) =
        s.indicator (fun ω => c * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    simp_rw [e1, e2, setLIntegral_indicator hs', lintegral_const_mul _ hG,
      lintegral_const_mul _ hK]
    rw [strong_markov_lintegral P μ hτ hs hH]
  · intro f g _ hf hg ihf ihg
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => f ω * H (shiftAt τ ω)) ((hf.mono hle le_rfl).mul hG),
      lintegral_add_left (f := fun ω => f ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω))
        ((hf.mono hle le_rfl).mul hK), ihf, ihg]
  · intro f hf hmono ih
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun k ω => f k ω * H (shiftAt τ ω))
        (fun k => ((hf k).mono hle le_rfl).mul hG)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _),
      lintegral_iSup (f := fun k ω => f k ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω))
        (fun k => ((hf k).mono hle le_rfl).mul hK)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _)]
    simp_rw [ih]

/-- **The strong Markov property as an identity of measures.** For `A ∈ 𝓕_ζ^Φ`, the law of the
post-`ζ` path `θ^ζΦ` on `A ∩ {ζ < ∞}` is the mixture of the `P_y` over the law of `Φ_ζ` on
`A ∩ {ζ < ∞}`. -/
theorem strong_markov_measure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map (shiftAt τ) =
      pathKernel P ∘ₘ (((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map
        (stoppedState τ)) := by
  have := isMarkovKernel_pathKernel P
  ext B hB
  have hi : Measurable (B.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hB
  have h := strong_markov_lintegral P μ hτ hA hi
  rw [Measure.map_apply (measurable_shiftAt hτ) hB, Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hB) (measurable_stoppedState hτ),
    ← lintegral_indicator_one (measurable_shiftAt hτ hB)]
  simp_rw [lintegral_indicator_one hB] at h
  exact h

/-- **The strong Markov property** for integrable functionals: for `A ∈ 𝓕_ζ^Φ` and measurable
`H` with `1_{ζ<∞} θ^ζH` integrable, `∫_{A ∩ {ζ<∞}} θ^ζH dP_μ = ∫_{A ∩ {ζ<∞}} E_{Φ_ζ}[H] dP_μ`. -/
theorem strong_markov_setIntegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[hτ.measurableSpace] A) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : IntegrableOn (fun ω => H (shiftAt τ ω)) (A ∩ {ω | τ ω ≠ ⊤}) (pathMeasure P μ)) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫ ω', H ω' ∂pathKernel P (stoppedState τ ω)
        ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hA' := (measurableSet_stoppedField_iff hτ A).1 hA
  have hAm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) := hA'.1.inter (measurableSet_ne_top hτ)
  have hmeas := strong_markov_measure P μ hτ hA
  have hi : Integrable H (((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map (shiftAt τ)) :=
    (integrable_map_measure hH.aestronglyMeasurable (measurable_shiftAt hτ).aemeasurable).2 hint
  rw [hmeas] at hi
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  calc ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, H (shiftAt τ ω) ∂pathMeasure P μ
      = ∫ ω', H ω' ∂(((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map (shiftAt τ)) :=
        (integral_map (measurable_shiftAt hτ).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ ω', H ω' ∂(pathKernel P ∘ₘ (((pathMeasure P μ).restrict
          (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedState τ))) := by rw [hmeas]
    _ = ∫ y, ∫ ω', H ω' ∂pathKernel P y ∂(((pathMeasure P μ).restrict
          (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedState τ)) := integral_measure_comp _ _ hi
    _ = _ := integral_map (measurable_stoppedState hτ).aemeasurable hk.aestronglyMeasurable

/-- **The strong Markov property** (3.32), MT p. 66: for a stopping time `ζ` and measurable `H`
with `1_{ζ<∞} θ^ζH` integrable, `E_μ[1_{ζ<∞} θ^ζH | 𝓕_ζ^Φ] = 1_{ζ<∞} E_{Φ_ζ}[H]`, `P_μ`-a.s. -/
theorem strong_markov_property (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable ({ω | τ ω ≠ ⊤}.indicator fun ω => H (shiftAt τ ω)) (pathMeasure P μ)) :
    (pathMeasure P μ)[{ω | τ ω ≠ ⊤}.indicator (fun ω => H (shiftAt τ ω)) | hτ.measurableSpace]
      =ᵐ[pathMeasure P μ]
        {ω | τ ω ≠ ⊤}.indicator fun ω => ∫ ω', H ω' ∂pathKernel P (stoppedState τ ω) := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hT := measurableSet_ne_top hτ
  have hk : Measurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    (StronglyMeasurable.integral_kernel hH.stronglyMeasurable).measurable
  have hgm := measurable_stoppedField_indicator hτ hk
  have hint' : IntegrableOn (fun ω => H (shiftAt τ ω)) {ω | τ ω ≠ ⊤} (pathMeasure P μ) :=
    (integrable_indicator_iff hT).1 hint
  -- integrability of the right-hand side
  have hg : Integrable ({ω | τ ω ≠ ⊤}.indicator fun ω => ∫ ω', H ω' ∂pathKernel P
      (stoppedState τ ω)) (pathMeasure P μ) := by
    refine ⟨(hgm.mono hτ.measurableSpace_le le_rfl).aestronglyMeasurable, ?_⟩
    have hlin := strong_markov_lintegral P μ hτ (A := univ) MeasurableSet.univ
      (H := fun ω => ‖H ω‖ₑ) hH.enorm
    simp only [univ_inter] at hlin
    rw [HasFiniteIntegral, lintegral_congr fun ω => enorm_indicator_eq_indicator_enorm _ ω,
      lintegral_indicator hT]
    calc ∫⁻ ω in {ω | τ ω ≠ ⊤}, ‖∫ ω', H ω' ∂pathKernel P (stoppedState τ ω)‖ₑ
          ∂pathMeasure P μ
        ≤ ∫⁻ ω in {ω | τ ω ≠ ⊤}, ∫⁻ ω', ‖H ω'‖ₑ ∂pathKernel P (stoppedState τ ω)
            ∂pathMeasure P μ := lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ω in {ω | τ ω ≠ ⊤}, ‖H (shiftAt τ ω)‖ₑ ∂pathMeasure P μ := hlin.symm
      _ < ∞ := hint'.2
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hint
    (fun s _ _ => hg.integrableOn) (fun s hs _ => ?_)
    (hgm.stronglyMeasurable).aestronglyMeasurable).symm
  have hsm : MeasurableSet s := hτ.measurableSpace_le _ hs
  rw [setIntegral_indicator hT, setIntegral_indicator hT]
  exact (strong_markov_setIntegral P μ hτ hs hH (hint'.mono_set inter_subset_right)).symm

variable (X) in
/-- The strong Markov property of a chain with transition kernel `P` (MT p. 66): (3.32) holds
for every initial distribution `μ`, every bounded measurable `H` on path space and every stopping
time `ζ` of the natural filtration. -/
def StrongMarkovProperty (P : Kernel X X) [IsMarkovKernel P] : Prop :=
  ∀ (μ : Measure X) [IsProbabilityMeasure μ] (H : (ℕ → X) → ℝ), Measurable H →
    (∃ B, ∀ ω, |H ω| ≤ B) → ∀ (τ : (ℕ → X) → WithTop ℕ)
    (hτ : IsStoppingTime (natFilt (X := X)) τ),
    (pathMeasure P μ)[{ω | τ ω ≠ ⊤}.indicator (fun ω => H (shiftAt τ ω)) | hτ.measurableSpace]
      =ᵐ[pathMeasure P μ]
        {ω | τ ω ≠ ⊤}.indicator fun ω => ∫ ω', H ω' ∂pathKernel P (stoppedState τ ω)

/-- **Proposition 3.4.6** (MT p. 66): a Markov chain with discrete time parameter always has the
strong Markov property. -/
theorem proposition_3_4_6 (P : Kernel X X) [IsMarkovKernel P] : StrongMarkovProperty X P := by
  intro μ _ H hH hB τ hτ
  obtain ⟨B, hB⟩ := hB
  have := isProbabilityMeasure_pathMeasure P μ
  refine strong_markov_property P μ hτ hH ?_
  refine (Integrable.of_bound (hH.comp (measurable_shiftAt hτ)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => ?_)).indicator (measurableSet_ne_top hτ)
  rw [Real.norm_eq_abs]; exact hB _

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Occupation, hitting and return times (MT §3.4.3)

Meyn and Tweedie, §3.4.3, pp. 64–67. For a measurable `A ⊆ X`:

* `occTime A = η_A = Σ_{n ≥ 1} 1_A(Φₙ)`, the occupation time (p. 64);
* `firstReturn A = τ_A = min{n ≥ 1 : Φₙ ∈ A}` and `firstHit A = σ_A = min{n ≥ 0 : Φₙ ∈ A}`
  (p. 64), both Mathlib's `hittingAfter`, valued in `ℕ ∪ {∞}`;
* `returnTimeK A k = τ_A(k)`, the time of the `k`-th visit to `A` after time `0` (3.29);
* `potKernel_eq_lintegral_occTime` (3.30): `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A) = E_x[η_A]`;
* `hitProb P A x = L(x, A) = P_x(τ_A < ∞)` (3.31), with `firstReturn_ne_top_iff`
  (`= P_x(Φ ever enters A)`) and `measurable_hitProb`;
* **Proposition 3.4.4** (`proposition_3_4_4`, p. 65): `τ_A` and `σ_A` are stopping times;
  `isStoppingTime_returnTimeK`: so are all the `τ_A(k)`;
* `pathKernel_first_step`: first-step analysis, `P_x(Φ₁ ∈ C, θΦ ∈ B) = ∫_C P(x, dy) P_y(B)`;
* `tabooKernel` (`(P I_{Aᶜ})ⁿ P`, p. 66) and the taboo probabilities `tabooProb`
  (`_AP^n(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)`, p. 67), with `tabooProb_one`, `tabooProb_succ` (3.33)
  and `tabooProb_eq_tabooKernel` (the operator form `_AP^n = (P I_{Aᶜ})^{n−1} P`);
* **Proposition 3.4.5** (`proposition_3_4_5_i`, `proposition_3_4_5_i_succ`,
  `proposition_3_4_5_ii`, p. 65) and its operator form `firstReturn_eq_tabooKernel`
  (`P_x(τ_A = k) = [(P I_{Aᶜ})^{k−1} P](x, A)`, p. 66);
* `hitProb_eq_tsum` (p. 66): `L(x, A) = Σ_k [(P I_{Aᶜ})^{k−1} P](x, A)`, and `hitProb_first_step`:
  `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`;
* `tabooPotKernel` (3.34): `U_A = Σ_{n ≥ 1} _APⁿ`, and `tabooPotKernel_self` (p. 67):
  `U_A(x, A) = L(x, A)`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Definitions -/

/-- The occupation time `η_A = Σ_{n ≥ 1} 1_A(Φₙ)`, the number of visits to `A` after time `0`
(MT p. 64). -/
noncomputable def occTime (A : Set X) (ω : ℕ → X) : ℝ≥0∞ := ∑' n, A.indicator 1 (ω (n + 1))

/-- The first return time `τ_A = min{n ≥ 1 : Φₙ ∈ A}` (`∞` if there is none), MT p. 64. -/
noncomputable def firstReturn (A : Set X) : (ℕ → X) → WithTop ℕ :=
  hittingAfter (fun n ω => ω n) A 1

/-- The first hitting time `σ_A = min{n ≥ 0 : Φₙ ∈ A}` (`∞` if there is none), MT p. 64. -/
noncomputable def firstHit (A : Set X) : (ℕ → X) → WithTop ℕ :=
  hittingAfter (fun n ω => ω n) A 0

/-- The `k`-th return time `τ_A(k)` (3.29), MT p. 64: `τ_A(0) = 0` and
`τ_A(k + 1) = min{n > τ_A(k) : Φₙ ∈ A}` (`∞` once a return fails). -/
noncomputable def returnTimeK (A : Set X) : ℕ → (ℕ → X) → WithTop ℕ
  | 0 => fun _ => 0
  | k + 1 => fun ω => WithTop.recTopCoe (C := fun _ => WithTop ℕ) ⊤
      (fun m => hittingAfter (fun n ω => ω n) A (m + 1) ω) (returnTimeK A k ω)

/-- The return probability `L(x, A) = P_x(τ_A < ∞)` (3.31), MT p. 64. -/
noncomputable def hitProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) : ℝ≥0∞ :=
  pathKernel P x {ω | firstReturn A ω ≠ ⊤}

/-! ### Pathwise facts -/

omit [MeasurableSpace X] in
/-- `τ_A(1) = τ_A`. -/
theorem returnTimeK_one (A : Set X) : returnTimeK A 1 = firstReturn A := rfl

omit [MeasurableSpace X] in
/-- On `{τ_A(k) = m}`, `τ_A(k + 1) = min{n ≥ m + 1 : Φₙ ∈ A}`. -/
theorem returnTimeK_succ_of_eq (A : Set X) {k m : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = WithTop.some m) :
    returnTimeK A (k + 1) ω = hittingAfter (fun n ω => ω n) A (m + 1) ω := by
  simp only [returnTimeK, h]
  rfl

omit [MeasurableSpace X] in
/-- On `{τ_A(k) = ∞}`, `τ_A(k + 1) = ∞`. -/
theorem returnTimeK_succ_of_top (A : Set X) {k : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = ⊤) : returnTimeK A (k + 1) ω = ⊤ := by
  simp only [returnTimeK, h]
  rfl

omit [MeasurableSpace X] in
/-- `τ_A < ∞` iff the chain enters `A` at some time `n ≥ 1` (MT (3.31)). -/
theorem firstReturn_ne_top_iff (A : Set X) (ω : ℕ → X) :
    firstReturn A ω ≠ ⊤ ↔ ∃ n, 1 ≤ n ∧ ω n ∈ A := by
  rw [firstReturn, ne_eq, hittingAfter_eq_top_iff]
  push Not
  rfl

omit [MeasurableSpace X] in
/-- `n ≤ τ_A` iff the chain avoids `A` at times `1, …, n − 1`. -/
theorem le_firstReturn_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    WithTop.some n ≤ firstReturn A ω ↔ ∀ j, 1 ≤ j → j < n → ω j ∉ A := by
  rw [firstReturn, ← not_lt, hittingAfter_lt_iff]
  simp only [mem_Ico, not_exists, not_and]
  exact ⟨fun h j h1 h2 hj => h j ⟨h1, h2⟩ hj, fun h j hj => h j hj.1 hj.2⟩

omit [MeasurableSpace X] in
/-- `τ_A ≥ 1`. -/
theorem one_le_firstReturn (A : Set X) (ω : ℕ → X) : WithTop.some 1 ≤ firstReturn A ω :=
  le_hittingAfter ω

omit [MeasurableSpace X] in
/-- `τ_A = n + 1` iff `τ_A ≥ n + 1` and `Φₙ₊₁ ∈ A`. -/
theorem firstReturn_eq_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    firstReturn A ω = WithTop.some (n + 1) ↔
      WithTop.some (n + 1) ≤ firstReturn A ω ∧ ω (n + 1) ∈ A := by
  constructor
  · intro h
    refine ⟨h.ge, ?_⟩
    have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A) (n := 1)
      (ω := ω) (by rw [← firstReturn, h]; exact WithTop.coe_ne_top)
    rw [← firstReturn, h] at this
    exact this
  · rintro ⟨hle, hA⟩
    exact le_antisymm (hittingAfter_le_of_mem (by omega) hA) hle

omit [MeasurableSpace X] in
/-- `τ_A ≥ n + 2` iff `Φ₁ ∉ A` and `τ_A ∘ θ ≥ n + 1`. -/
theorem le_firstReturn_succ_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    WithTop.some (n + 2) ≤ firstReturn A ω ↔
      ω 1 ∈ Aᶜ ∧ WithTop.some (n + 1) ≤ firstReturn A (shift 1 ω) := by
  rw [le_firstReturn_iff, le_firstReturn_iff]
  simp only [shift_apply, mem_compl_iff]
  constructor
  · intro h
    exact ⟨h 1 le_rfl (by omega), fun j hj1 hj2 => h (1 + j) (by omega) (by omega)⟩
  · rintro ⟨h1, h⟩ j hj1 hj2
    rcases Nat.lt_or_ge j 2 with hj | hj
    · rwa [show j = 1 by omega]
    · have := h (j - 1) (by omega) (by omega)
      rwa [show 1 + (j - 1) = j by omega] at this

omit [MeasurableSpace X] in
/-- `σ_A = 0` iff `Φ₀ ∈ A`. -/
theorem firstHit_eq_zero_iff (A : Set X) (ω : ℕ → X) :
    firstHit A ω = WithTop.some 0 ↔ ω 0 ∈ A := by
  constructor
  · intro h
    have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A) (n := 0)
      (ω := ω) (by rw [← firstHit, h]; exact WithTop.coe_ne_top)
    rw [← firstHit, h] at this
    exact this
  · intro h
    exact le_antisymm (hittingAfter_le_of_mem le_rfl h) (le_hittingAfter ω)

omit [MeasurableSpace X] in
/-- If `Φ₀ ∉ A` then `σ_A = τ_A`. -/
theorem firstHit_eq_firstReturn (A : Set X) {ω : ℕ → X} (h : ω 0 ∉ A) :
    firstHit A ω = firstReturn A ω := by
  refine le_antisymm ?_ ?_
  · rcases eq_or_ne (firstReturn A ω) ⊤ with ht | ht
    · rw [ht]; exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ht
      have h1 := (firstReturn_eq_iff A ω (m - 1)).1
      have hm1 : 1 ≤ m := by
        have := one_le_firstReturn A ω
        rw [← hm] at this
        exact WithTop.coe_le_coe.1 this
      rw [show m = m - 1 + 1 by omega] at hm
      rw [← hm]
      exact hittingAfter_le_of_mem (Nat.zero_le _) (h1 hm.symm).2
  · rcases eq_or_ne (firstHit A ω) ⊤ with ht | ht
    · rw [ht]; exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ht
      have hmem := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A)
        (n := 0) (ω := ω) ht
      rw [← firstHit, ← hm] at hmem
      have hm0 : m ≠ 0 := by rintro rfl; exact h hmem
      rw [← hm]
      exact hittingAfter_le_of_mem (by omega) hmem

/-! ### Measurability and Proposition 3.4.4 -/

/-- The coordinate process is adapted to its natural filtration. -/
theorem adapted_coord : Adapted (natFilt (X := X)) fun n (ω : ℕ → X) => ω n :=
  fun n => measurable_coord_natFilt n

/-- **Proposition 3.4.4** (MT p. 65): `τ_A` and `σ_A` are stopping times. -/
theorem proposition_3_4_4 {A : Set X} (hA : MeasurableSet A) :
    IsStoppingTime (natFilt (X := X)) (firstReturn A) ∧
      IsStoppingTime (natFilt (X := X)) (firstHit A) :=
  ⟨adapted_coord.isStoppingTime_hittingAfter hA, adapted_coord.isStoppingTime_hittingAfter hA⟩

/-- Every `τ_A(k)` is a stopping time. -/
theorem isStoppingTime_returnTimeK {A : Set X} (hA : MeasurableSet A) (k : ℕ) :
    IsStoppingTime (natFilt (X := X)) (returnTimeK A k) := by
  induction k with
  | zero => exact isStoppingTime_const _ 0
  | succ k ih =>
    intro i
    have hset : {ω | returnTimeK A (k + 1) ω ≤ WithTop.some i} =
        ⋃ m ∈ Finset.range (i + 1), {ω | returnTimeK A k ω = WithTop.some m} ∩
          {ω | hittingAfter (fun n (ω : ℕ → X) => ω n) A (m + 1) ω ≤ WithTop.some i} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Finset.mem_range, exists_prop]
      constructor
      · intro h
        cases hk : returnTimeK A k ω with
        | top => rw [returnTimeK_succ_of_top A hk] at h; simp at h
        | coe m =>
          rw [returnTimeK_succ_of_eq A hk] at h
          have hle := (le_hittingAfter (u := fun n (ω : ℕ → X) => ω n) (s := A)
            (n := m + 1) ω).trans h
          exact ⟨m, by have := WithTop.coe_le_coe.1 hle; omega, rfl, h⟩
      · rintro ⟨m, _, hm, h⟩
        rwa [returnTimeK_succ_of_eq A hm]
    rw [hset]
    refine Finset.measurableSet_biUnion _ fun m hm => ?_
    have hmi : m ≤ i := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
    exact ((natFilt (X := X)).mono hmi _ (ih.measurableSet_eq_of_countable m)).inter
      (adapted_coord.isStoppingTime_hittingAfter hA i)

/-- `{τ_A < ∞}` is an event. -/
theorem measurableSet_firstReturn_ne_top {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → X | firstReturn A ω ≠ ⊤} :=
  measurableSet_ne_top (proposition_3_4_4 hA).1

/-- `{τ_A = n}` is an event. -/
theorem measurableSet_firstReturn_eq {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω : ℕ → X | firstReturn A ω = WithTop.some n} :=
  (natFilt (X := X)).le n _ ((proposition_3_4_4 hA).1.measurableSet_eq_of_countable n)

/-- `{τ_A ≥ n}` is an event. -/
theorem measurableSet_le_firstReturn {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω : ℕ → X | WithTop.some n ≤ firstReturn A ω} := by
  have : {ω : ℕ → X | WithTop.some n ≤ firstReturn A ω} =
      ⋂ j ∈ Finset.range n, {ω | 1 ≤ j → ω j ∈ Aᶜ} := by
    ext ω
    simp only [mem_ofPred_eq, le_firstReturn_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact ⟨fun h j hj h1 => h j h1 hj, fun h j h1 hj => h j hj h1⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun j _ => ?_
  by_cases hj : 1 ≤ j
  · have : {ω : ℕ → X | 1 ≤ j → ω j ∈ Aᶜ} = {ω | ω j ∈ Aᶜ} := by ext; simp [hj]
    rw [this]
    exact (measurable_pi_apply j : Measurable fun ω : ℕ → X => ω j) hA.compl
  · simp [hj]

/-- `η_A` is measurable. -/
theorem measurable_occTime {A : Set X} (hA : MeasurableSet A) :
    Measurable (occTime (X := X) A) :=
  Measurable.tsum fun _ => (measurable_one.indicator hA).comp (measurable_pi_apply _)

/-- `x ↦ L(x, A)` is measurable. -/
theorem measurable_hitProb (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : Measurable (hitProb P A) :=
  Kernel.measurable_coe _ (measurableSet_firstReturn_ne_top hA)

/-! ### The potential kernel and occupation times -/

/-- (3.30), MT p. 64: `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A) = E_x[η_A]`. -/
theorem potKernel_eq_lintegral_occTime (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {A : Set X} (hA : MeasurableSet A) :
    potKernel P x A = ∫⁻ ω, occTime A ω ∂pathKernel P x := by
  unfold occTime
  rw [potKernel_apply P x hA,
    lintegral_tsum (f := fun n (ω : ℕ → X) => A.indicator 1 (ω (n + 1))) fun n =>
      ((measurable_one.indicator hA).comp (measurable_pi_apply (n + 1))).aemeasurable]
  refine tsum_congr fun n => ?_
  have hm : MeasurableSet {ω : ℕ → X | ω (n + 1) ∈ A} := measurable_pi_apply (n + 1) hA
  rw [← pathKernel_coord_mem P x (n + 1) hA, ← lintegral_indicator_one hm]
  rfl

/-! ### First-step analysis and taboo probabilities -/

/-- **First-step analysis.** `P_x(Φ₁ ∈ C, θΦ ∈ B) = ∫_C P(x, dy) P_y(B)`. -/
theorem pathKernel_first_step (P : Kernel X X) [IsMarkovKernel P] (x : X) {C : Set X}
    (hC : MeasurableSet C) {B : Set (ℕ → X)} (hB : MeasurableSet B) :
    pathKernel P x ({ω | ω 1 ∈ C} ∩ shift 1 ⁻¹' B) = ∫⁻ y in C, pathKernel P y B ∂P x := by
  have := isMarkovKernel_pathKernel P
  have hG : MeasurableSet[natFilt 1] {ω : ℕ → X | ω 1 ∈ C} :=
    measurableSet_coord_natFilt le_rfl hC
  have hGm : MeasurableSet {ω : ℕ → X | ω 1 ∈ C} := measurable_pi_apply 1 hC
  have hi : Measurable (B.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hB
  have h := markov_lintegral P (Measure.dirac x) hG hi
  rw [pathMeasure_dirac] at h
  have hsh : MeasurableSet (shift 1 ⁻¹' B) := measurable_shift 1 hB
  have e1 : ∫⁻ ω in {ω : ℕ → X | ω 1 ∈ C}, B.indicator 1 (shift 1 ω) ∂pathKernel P x =
      pathKernel P x ({ω | ω 1 ∈ C} ∩ shift 1 ⁻¹' B) := by
    calc ∫⁻ ω in {ω : ℕ → X | ω 1 ∈ C}, B.indicator 1 (shift 1 ω) ∂pathKernel P x
        = ∫⁻ ω in {ω : ℕ → X | ω 1 ∈ C}, (shift 1 ⁻¹' B).indicator 1 ω ∂pathKernel P x := rfl
      _ = _ := by rw [lintegral_indicator_one hsh, Measure.restrict_apply hsh, inter_comm]
  simp_rw [lintegral_indicator_one hB] at h
  have hk : Measurable fun y => pathKernel P y B := Kernel.measurable_coe _ hB
  rw [← e1, h, ← lintegral_indicator hGm]
  have e2 : ({ω : ℕ → X | ω 1 ∈ C}.indicator fun ω => pathKernel P (ω 1) B) =
      fun ω => C.indicator (fun y => pathKernel P y B) (ω 1) := by
    ext ω; by_cases h : ω 1 ∈ C <;> simp [h]
  rw [e2, ← lintegral_map (hk.indicator hC) (measurable_pi_apply 1), pathKernel_map_coord,
    pow_one, lintegral_indicator hC]

/-- The taboo kernel `(P I_{Aᶜ})ⁿ P` (MT p. 66): move by `P`, killing the path whenever it is in
`A`, `n` times, then move once more by `P`. -/
noncomputable def tabooKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    Kernel X X :=
  P ∘ₖ ((indKernel hA.compl ∘ₖ P) ^ n)

/-- `(P I_B)(x, ·) = P(x, ·)` restricted to `B`. -/
theorem comp_indKernel_eq_restrict (P : Kernel X X) {B : Set X} (hB : MeasurableSet B)
    (x : X) : (indKernel hB ∘ₖ P) x = (P x).restrict B := by
  ext C hC
  rw [comp_indKernel_apply P hB x hC, Measure.restrict_apply hC]

/-- `(P I_{Aᶜ})⁰ P = P`. -/
theorem tabooKernel_zero (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    tabooKernel P hA 0 = P := by
  rw [tabooKernel, pow_zero]
  exact Kernel.comp_id P

/-- (3.33), operator form: `[(P I_{Aᶜ})ⁿ⁺¹ P](x, B) = ∫_{Aᶜ} P(x, dy) [(P I_{Aᶜ})ⁿ P](y, B)`. -/
theorem tabooKernel_succ_apply (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n : ℕ)
    (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooKernel P hA (n + 1) x B = ∫⁻ y in Aᶜ, tabooKernel P hA n y B ∂P x := by
  rw [tabooKernel, pow_succ]
  change (P ∘ₖ (((indKernel hA.compl ∘ₖ P) ^ n) ∘ₖ (indKernel hA.compl ∘ₖ P))) x B = _
  rw [← Kernel.comp_assoc, Kernel.comp_apply' _ _ _ hB, comp_indKernel_eq_restrict]
  rfl

/-- The taboo probabilities `_APⁿ(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)` (MT p. 67). -/
noncomputable def tabooProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (n : ℕ) (x : X)
    (B : Set X) : ℝ≥0∞ :=
  pathKernel P x ({ω | ω n ∈ B} ∩ {ω | WithTop.some n ≤ firstReturn A ω})

/-- `_AP¹(x, B) = P(x, B)` (MT p. 67). -/
theorem tabooProb_one (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) {B : Set X}
    (hB : MeasurableSet B) : tabooProb P A 1 x B = P x B := by
  have : {ω : ℕ → X | WithTop.some 1 ≤ firstReturn A ω} = univ :=
    eq_univ_of_forall fun ω => one_le_firstReturn A ω
  rw [tabooProb, this, inter_univ, pathKernel_coord_mem P x 1 hB, pow_one]

/-- (3.33), MT p. 67: `_APⁿ⁺¹(x, B) = ∫_{Aᶜ} P(x, dy) _APⁿ(y, B)` for `n ≥ 1`. -/
theorem tabooProb_succ (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooProb P A (n + 2) x B = ∫⁻ y in Aᶜ, tabooProb P A (n + 1) y B ∂P x := by
  have hset : {ω : ℕ → X | ω (n + 2) ∈ B} ∩ {ω | WithTop.some (n + 2) ≤ firstReturn A ω} =
      {ω | ω 1 ∈ Aᶜ} ∩ shift 1 ⁻¹' ({ω | ω (n + 1) ∈ B} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, shift_apply,
      le_firstReturn_succ_iff A ω n]
    rw [show 1 + (n + 1) = n + 2 by omega]
    tauto
  rw [tabooProb, hset, pathKernel_first_step P x hA.compl
    (B := {ω | ω (n + 1) ∈ B} ∩ {ω | WithTop.some (n + 1) ≤ firstReturn A ω})
    ((measurable_pi_apply (n + 1) hB).inter (measurableSet_le_firstReturn hA (n + 1)))]
  rfl

/-- The operator form of the taboo probabilities (MT p. 67):
`_APⁿ⁺¹(x, B) = [(P I_{Aᶜ})ⁿ P](x, B)`. -/
theorem tabooProb_eq_tabooKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooProb P A (n + 1) x B = tabooKernel P hA n x B := by
  induction n generalizing x with
  | zero => rw [tabooProb_one P A x hB, tabooKernel_zero]
  | succ n ih =>
    rw [tabooProb_succ P hA n x hB, tabooKernel_succ_apply P hA n x hB]
    exact setLIntegral_congr_fun hA.compl fun y _ => ih y

/-! ### Proposition 3.4.5 -/

/-- `{τ_A = n + 1} = {Φₙ₊₁ ∈ A, τ_A ≥ n + 1}`, so `P_x(τ_A = n + 1) = _APⁿ⁺¹(x, A)`. -/
theorem firstReturn_eq_tabooProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (n : ℕ)
    (x : X) : pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 1)} =
      tabooProb P A (n + 1) x A := by
  rw [tabooProb]
  congr 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, firstReturn_eq_iff A ω n]
  tauto

/-- **Proposition 3.4.5 (i)**, first part (MT p. 65): `P_x(τ_A = 1) = P(x, A)`. -/
theorem proposition_3_4_5_i (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some 1} = P x A := by
  rw [firstReturn_eq_tabooProb P A 0 x, tabooProb_one P A x hA]

/-- **Proposition 3.4.5 (i)**, recursion (MT p. 65):
`P_x(τ_A = n + 1) = ∫_{Aᶜ} P(x, dy) P_y(τ_A = n)` for `n ≥ 1`. -/
theorem proposition_3_4_5_i_succ (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 2)} =
      ∫⁻ y in Aᶜ, pathKernel P y {ω | firstReturn A ω = WithTop.some (n + 1)} ∂P x := by
  rw [firstReturn_eq_tabooProb P A (n + 1) x, tabooProb_succ P hA n x hA]
  exact setLIntegral_congr_fun hA.compl fun y _ => (firstReturn_eq_tabooProb P A n y).symm

/-- The operator form of Proposition 3.4.5 (MT p. 66):
`P_x(τ_A = n + 1) = [(P I_{Aᶜ})ⁿ P](x, A)`. -/
theorem firstReturn_eq_tabooKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 1)} = tabooKernel P hA n x A := by
  rw [firstReturn_eq_tabooProb, tabooProb_eq_tabooKernel P hA n x hA]

/-- The iterated-integral form of Proposition 3.4.5 (i): `P_x(τ_A = n + 1)` is
`∫_{Aᶜ} P(x, dy₁) ∫_{Aᶜ} P(y₁, dy₂) ⋯ P(yₙ, A)`, the `n`-fold nested integral `nestedTaboo`. -/
noncomputable def nestedTaboo (P : Kernel X X) (A : Set X) : ℕ → X → ℝ≥0∞
  | 0 => fun x => P x A
  | n + 1 => fun x => ∫⁻ y in Aᶜ, nestedTaboo P A n y ∂P x

/-- `P_x(τ_A = n + 1)` equals the nested integral of Proposition 3.4.5 (i). -/
theorem firstReturn_eq_nestedTaboo (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 1)} = nestedTaboo P A n x := by
  induction n generalizing x with
  | zero => exact proposition_3_4_5_i P hA x
  | succ n ih =>
    rw [proposition_3_4_5_i_succ P hA n x]
    exact setLIntegral_congr_fun hA.compl fun y _ => ih y

/-- **Proposition 3.4.5 (ii)** (MT p. 65): `P_x(σ_A = 0) = 1_A(x)`, and for `x ∉ A`, `n ≥ 1`,
`P_x(σ_A = n) = P_x(τ_A = n)`. -/
theorem proposition_3_4_5_ii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    pathKernel P x {ω | firstHit A ω = WithTop.some 0} = A.indicator 1 x ∧
      (x ∉ A → ∀ n, 1 ≤ n → pathKernel P x {ω | firstHit A ω = WithTop.some n} =
        pathKernel P x {ω | firstReturn A ω = WithTop.some n}) := by
  refine ⟨?_, fun hx n _ => ?_⟩
  · have : {ω : ℕ → X | firstHit A ω = WithTop.some 0} = {ω | ω 0 ∈ A} := by
      ext ω; exact firstHit_eq_zero_iff A ω
    rw [this, pathKernel_zero_mem P x hA]
  · have hnull : pathKernel P x {ω : ℕ → X | ω 0 ∈ Aᶜ}ᶜ = 0 := by
      have : {ω : ℕ → X | ω 0 ∈ Aᶜ}ᶜ = {ω | ω 0 ∈ A} := by ext ω; simp
      rw [this, pathKernel_zero_mem P x hA, indicator_of_notMem hx]
    rw [← measure_inter_conull (s := {ω | firstHit A ω = WithTop.some n}) hnull,
      ← measure_inter_conull (s := {ω | firstReturn A ω = WithTop.some n}) hnull]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [← firstHit_eq_firstReturn A h2], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [firstHit_eq_firstReturn A h2], h2⟩

/-! ### The return probability `L` -/

/-- (MT p. 66): `L(x, A) = Σ_{k ≥ 1} P_x(τ_A = k) = Σ_{k ≥ 1} [(P I_{Aᶜ})^{k−1} P](x, A)`. -/
theorem hitProb_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    hitProb P A x = ∑' n, tabooKernel P hA n x A := by
  have hset : {ω : ℕ → X | firstReturn A ω ≠ ⊤} =
      ⋃ n : ℕ, {ω | firstReturn A ω = WithTop.some (n + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 h
      have h1 := one_le_firstReturn A ω
      rw [← hm] at h1
      have h1' := WithTop.coe_le_coe.1 h1
      exact ⟨m - 1, by rw [← hm, show m - 1 + 1 = m by omega]⟩
    · rintro ⟨n, h⟩; rw [h]; exact WithTop.coe_ne_top
  rw [hitProb, hset, measure_iUnion (fun i j hij => Set.disjoint_left.2 fun ω hi hj => hij
    (by have := hi.symm.trans hj; simpa using this))
    (fun n => measurableSet_firstReturn_eq hA (n + 1))]
  exact tsum_congr fun n => firstReturn_eq_tabooKernel P hA n x

/-- **First-step equation for `L`**: `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`. -/
theorem hitProb_first_step (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    hitProb P A x = P x A + ∫⁻ y in Aᶜ, hitProb P A y ∂P x := by
  have hset : {ω : ℕ → X | firstReturn A ω ≠ ⊤} =
      {ω | ω 1 ∈ A} ∪ ({ω | ω 1 ∈ Aᶜ} ∩ shift 1 ⁻¹' {ω | firstReturn A ω ≠ ⊤}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff,
      firstReturn_ne_top_iff, shift_apply]
    constructor
    · rintro ⟨n, hn, h⟩
      by_cases h1 : ω 1 ∈ A
      · exact Or.inl h1
      · refine Or.inr ⟨h1, n - 1, ?_, ?_⟩
        · by_contra h0
          exact h1 (by rwa [show n = 1 by omega] at h)
        · rwa [show 1 + (n - 1) = n by omega]
    · rintro (h | ⟨_, n, hn, h⟩)
      · exact ⟨1, le_rfl, h⟩
      · exact ⟨1 + n, by omega, h⟩
  have hdisj : Disjoint {ω : ℕ → X | ω 1 ∈ A}
      ({ω | ω 1 ∈ Aᶜ} ∩ shift 1 ⁻¹' {ω | firstReturn A ω ≠ ⊤}) :=
    Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1
  rw [hitProb, hset, measure_union hdisj ((measurable_pi_apply 1 hA.compl).inter
      (measurable_shift 1 (measurableSet_firstReturn_ne_top hA))),
    pathKernel_first_step P x hA.compl (measurableSet_firstReturn_ne_top hA),
    pathKernel_coord_mem P x 1 hA, pow_one]
  rfl

/-- The taboo potential kernel `U_A = Σ_{n ≥ 1} _APⁿ` (3.34), MT p. 67. -/
noncomputable def tabooPotKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    Kernel X X :=
  Kernel.sum fun n => tabooKernel P hA n

/-- (3.34): `U_A(x, B) = Σ_{n ≥ 1} _APⁿ(x, B)`. -/
theorem tabooPotKernel_apply (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooPotKernel P hA x B = ∑' n, tabooProb P A (n + 1) x B := by
  rw [tabooPotKernel, Kernel.sum_apply' _ _ hB]
  exact tsum_congr fun n => (tabooProb_eq_tabooKernel P hA n x hB).symm

/-- MT p. 67: `U_A(x, A) = L(x, A)`. -/
theorem tabooPotKernel_self (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) : tabooPotKernel P hA x A = hitProb P A x := by
  rw [tabooPotKernel, Kernel.sum_apply' _ _ hA, hitProb_eq_tsum P hA x]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov chains on a countable space (MT §3.2)

Meyn and Tweedie, §3.2, pp. 51–54. `X` is countable with all subsets measurable (measurable
singletons). Matrix entries are taken in `[0, ∞]`, where nonnegativity is automatic.

* `IsTransitionMatrix` (3.6): rows sum to one.
* `matPow` (3.7): the matrix powers `P⁰ = I`, `Pⁿ(x, z) = Σ_y P(x, y) Pⁿ⁻¹(y, z)`.
* `matKernel`: the kernel `P(x, A) = Σ_{y ∈ A} P(x, y)` of a matrix; `matKernel_singleton`,
  `matKernel_apply` (p. 53); `isMarkovKernel_matKernel`: a transition matrix gives a transition
  probability kernel; `matKernel_pow_singleton`: the kernel powers are the matrix powers, so
  `Pⁿ(x, A) = Σ_{y ∈ A} Pⁿ(x, y)` (`matKernel_pow_apply`).
* `IsMarkovChain.fdd_points` (3.3)–(3.4): a Markov chain with a transition matrix has the
  point finite-dimensional distributions of the countable-space definition (p. 52).
* **Theorem 3.2.1** (p. 54), for the chain `P_μ` built from a transition matrix:
  `theorem_3_2_1_fdd` (3.4), `P_μ(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯ P(xₙ₋₁, xₙ)`;
  `theorem_3_2_1` (3.5), `P_μ(Φₙ₊₁ = y | Φₙ = xₙ, …, Φ₀ = x₀) = P(xₙ, y)`;
  `pathMeasure_initial_coord` (3.8), `P_μ(Φ₀ = x, Φₙ = y) = μ(x) Pⁿ(x, y)`; and
  `pathMeasure_inter_initial` (3.1), `P_μ(Φ ∈ B, Φ₀ = x₀) = μ(x₀) P_{x₀}(Φ ∈ B)`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*}

/-! ### Transition matrices and their powers -/

/-- A Markov transition matrix (3.6), MT p. 53: every row sums to one. -/
def IsTransitionMatrix (p : X → X → ℝ≥0∞) : Prop := ∀ x, ∑' y, p x y = 1

open scoped Classical in
/-- The matrix powers (3.7), MT p. 53: `P⁰ = I` and `Pⁿ⁺¹(x, z) = Σ_y P(x, y) Pⁿ(y, z)`. -/
noncomputable def matPow (p : X → X → ℝ≥0∞) : ℕ → X → X → ℝ≥0∞
  | 0 => fun x z => if x = z then 1 else 0
  | n + 1 => fun x z => ∑' y, p x y * matPow p n y z

variable [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- The kernel of a matrix: `P(x, A) = Σ_{y ∈ A} P(x, y)` (MT p. 53). -/
noncomputable def matKernel (p : X → X → ℝ≥0∞) : Kernel X X :=
  Kernel.ofFunOfCountable fun x => Measure.sum fun y => p x y • Measure.dirac y

/-- `P(x, {y}) = P(x, y)`. -/
theorem matKernel_singleton (p : X → X → ℝ≥0∞) (x y : X) : matKernel p x {y} = p x y :=
  Measure.sum_smul_dirac_singleton

/-- `P(x, A) = Σ_{y ∈ A} P(x, y)`. -/
theorem matKernel_apply (p : X → X → ℝ≥0∞) (x : X) (A : Set X) :
    matKernel p x A = ∑' y, A.indicator (p x) y := by
  rw [← Measure.tsum_indicator_apply_singleton _ A
    (Set.Countable.measurableSet (Set.to_countable A))]
  simp_rw [matKernel_singleton]

/-- A transition matrix gives a transition probability kernel. -/
theorem isMarkovKernel_matKernel {p : X → X → ℝ≥0∞} (hp : IsTransitionMatrix p) :
    IsMarkovKernel (matKernel p) :=
  ⟨fun x => ⟨by rw [matKernel_apply]; simpa using hp x⟩⟩

/-- Every measure on `X` is determined by its values on points: `∫ f dν = Σ_x f(x) ν{x}`. -/
theorem lintegral_matKernel (p : X → X → ℝ≥0∞) (x : X) (f : X → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel p x = ∑' y, p x y * f y := by
  rw [lintegral_countable']
  simp_rw [matKernel_singleton, mul_comm]

/-- The kernel powers are the matrix powers: `Pⁿ(x, {z}) = Pⁿ(x, z)` (MT p. 53). -/
theorem matKernel_pow_singleton (p : X → X → ℝ≥0∞) (n : ℕ) (x z : X) :
    (matKernel p ^ n) x {z} = matPow p n x z := by
  classical
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton z), matPow]
    by_cases h : x = z <;> simp [h]
  | succ n ih =>
    rw [pow_succ_apply _ n x (measurableSet_singleton z), lintegral_matKernel]
    simp_rw [ih]
    rfl

/-- `Pⁿ(x, A) = Σ_{y ∈ A} Pⁿ(x, y)` (MT p. 53). -/
theorem matKernel_pow_apply (p : X → X → ℝ≥0∞) (n : ℕ) (x : X) (A : Set X) :
    (matKernel p ^ n) x A = ∑' y, A.indicator (matPow p n x) y := by
  rw [← Measure.tsum_indicator_apply_singleton _ A
    (Set.Countable.measurableSet (Set.to_countable A))]
  simp_rw [matKernel_pow_singleton]

/-- The powers of a transition matrix are transition matrices. -/
theorem isTransitionMatrix_matPow {p : X → X → ℝ≥0∞} (hp : IsTransitionMatrix p) (n : ℕ) :
    IsTransitionMatrix (matPow p n) := fun x => by
  have := isMarkovKernel_matKernel hp
  have := isMarkovKernel_pow (matKernel p) n
  have h := matKernel_pow_apply p n x univ
  simp only [measure_univ, indicator_univ] at h
  exact h.symm

/-! ### Theorem 3.2.1 -/

/-- The nested integral (3.20) at points is the product (3.4). -/
theorem cylFn_singletons (p : X → X → ℝ≥0∞) (n : ℕ) (x : ℕ → X) (y : X) :
    cylFn (matKernel p) n (fun i => {x i}) y =
      ({x 0} : Set X).indicator (fun _ => ∏ i ∈ Finset.range n, p (x i) (x (i + 1))) y := by
  induction n generalizing x y with
  | zero => simp only [cylFn, Finset.range_zero, Finset.prod_empty]; rfl
  | succ n ih =>
    simp only [cylFn]
    by_cases hy : y = x 0
    · subst hy
      simp only [mem_singleton_iff, indicator_of_mem]
      simp_rw [ih (fun i => x (i + 1))]
      rw [lintegral_indicator_const (measurableSet_singleton _), matKernel_singleton,
        Finset.prod_range_succ', mul_comm]
    · simp [hy]

/-- (3.4), MT p. 52: `P_μ(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯ P(xₙ₋₁, xₙ)`. -/
theorem theorem_3_2_1_fdd (p : X → X → ℝ≥0∞) [IsMarkovKernel (matKernel p)] (μ : Measure X)
    (n : ℕ) (x : ℕ → X) :
    pathMeasure (matKernel p) μ {ω | ∀ i ≤ n, ω i = x i} =
      μ {x 0} * ∏ i ∈ Finset.range n, p (x i) (x (i + 1)) := by
  have h := pathMeasure_boxSet (matKernel p) μ n (A := fun i => {x i})
    fun i => measurableSet_singleton _
  simp_rw [cylFn_singletons] at h
  rw [lintegral_indicator_const (measurableSet_singleton _), mul_comm] at h
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- The countable-space definition (3.3)–(3.4), MT p. 52: every Markov chain with transition
matrix `P` and initial distribution `μ` has `P(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯
P(xₙ₋₁, xₙ)`. -/
theorem IsMarkovChain.fdd_points {p : X → X → ℝ≥0∞} {μ : Measure X} {pr : Measure Ω}
    {Φ : ℕ → Ω → X} (h : IsMarkovChain (matKernel p) μ pr Φ) (n : ℕ) (x : ℕ → X) :
    pr {ω | ∀ i ≤ n, Φ i ω = x i} = μ {x 0} * ∏ i ∈ Finset.range n, p (x i) (x (i + 1)) := by
  have hf := h.fdd n (fun i => {x i}) fun i => measurableSet_singleton _
  simp only [mem_singleton_iff] at hf
  simp_rw [cylFn_singletons] at hf
  rw [hf, lintegral_indicator_const (measurableSet_singleton _), mul_comm]

/-- **Theorem 3.2.1** (MT p. 54), (3.5): for a transition matrix `P` and initial distribution
`μ`, the chain `P_μ` satisfies `P_μ(Φₙ₊₁ = y | Φₙ = xₙ, …, Φ₀ = x₀) = P(xₙ, y)` whenever the
conditioning event has positive probability. -/
theorem theorem_3_2_1 (p : X → X → ℝ≥0∞) [IsMarkovKernel (matKernel p)] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ℕ → X) (y : X)
    (hpos : pathMeasure (matKernel p) μ {ω | ∀ i ≤ n, ω i = x i} ≠ 0) :
    (pathMeasure (matKernel p) μ)[{ω | ω (n + 1) = y} | {ω | ∀ i ≤ n, ω i = x i}] =
      p (x n) y := by
  classical
  have := isProbabilityMeasure_pathMeasure (matKernel p) μ
  set x' : ℕ → X := fun i => if i = n + 1 then y else x i
  have hset : {ω : ℕ → X | ∀ i ≤ n, ω i = x i} ∩ {ω | ω (n + 1) = y} =
      {ω | ∀ i ≤ n + 1, ω i = x' i} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, x']
    constructor
    · rintro ⟨h, hy⟩ i hi
      rcases Nat.lt_or_ge i (n + 1) with hl | hl
      · simp only [show i ≠ n + 1 by omega, ite_false]; exact h i (by omega)
      · simp only [show i = n + 1 by omega, ite_true]; exact hy
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i (by omega); simpa [show i ≠ n + 1 by omega] using this
      · have := h (n + 1) le_rfl; simpa using this
  have hprod : ∏ i ∈ Finset.range (n + 1), p (x' i) (x' (i + 1)) =
      (∏ i ∈ Finset.range n, p (x i) (x (i + 1))) * p (x n) y := by
    rw [Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      simp only [x', show i ≠ n + 1 by omega, show i + 1 ≠ n + 1 by omega, ite_false]
    · simp [x']
  have hmeas : MeasurableSet {ω : ℕ → X | ∀ i ≤ n, ω i = x i} := by
    have : {ω : ℕ → X | ∀ i ≤ n, ω i = x i} = boxSet n (fun i => {x i}) := by
      ext ω; simp [boxSet]
    rw [this]; exact measurableSet_boxSet n fun i => measurableSet_singleton _
  have hc := theorem_3_2_1_fdd p μ n x
  have htop : μ {x 0} * ∏ i ∈ Finset.range n, p (x i) (x (i + 1)) ≠ ⊤ :=
    hc ▸ measure_ne_top _ _
  rw [hc] at hpos
  have hx0 : x' 0 = x 0 := by simp [x']
  rw [cond_apply hmeas, hset, theorem_3_2_1_fdd p μ (n + 1) x', hprod, hc, hx0,
    ← mul_assoc (μ {x 0}), ← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]

omit [Countable X] in
/-- (3.1), MT p. 51: `P_μ(Φ ∈ B, Φ₀ = x₀) = μ(x₀) P_{x₀}(Φ ∈ B)`. -/
theorem pathMeasure_inter_initial (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {B : Set (ℕ → X)} (hB : MeasurableSet B) (x₀ : X) :
    pathMeasure P μ (B ∩ {ω | ω 0 = x₀}) = μ {x₀} * pathKernel P x₀ B := by
  have h := pathMeasure_inter_zero P μ hB (measurableSet_singleton x₀)
  simp only [mem_singleton_iff] at h
  rw [h, lintegral_singleton, mul_comm]

/-- (3.8), MT p. 53: `P_μ(Φ₀ = x, Φₙ = y) = μ(x) Pⁿ(x, y)`. -/
theorem pathMeasure_initial_coord (p : X → X → ℝ≥0∞) [IsMarkovKernel (matKernel p)]
    (μ : Measure X) (n : ℕ) (x y : X) :
    pathMeasure (matKernel p) μ ({ω | ω n = y} ∩ {ω | ω 0 = x}) = μ {x} * matPow p n x y := by
  have hB : MeasurableSet {ω : ℕ → X | ω n = y} :=
    (measurable_pi_apply n : Measurable fun ω : ℕ → X => ω n) (measurableSet_singleton y)
  rw [pathMeasure_inter_initial _ μ hB x]
  congr 1
  have := pathKernel_coord_mem (matKernel p) x n (measurableSet_singleton y)
  simp only [mem_singleton_iff] at this
  rw [this, matKernel_pow_singleton]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Communication, communicating classes and absorbing sets (MT §4.1.2)

Meyn and Tweedie, §4.1.2, pp. 77–80, together with the facts about reaching sets and about
absorbing sets that §4.2 uses on a general space.

**Reaching a set** (any measurable space).
* `hitProb_pos_iff`: `L(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 1`; `pow_le_hitProb`:
  `Pⁿ(x, A) ≤ L(x, A)` for `n ≥ 1`; `potKernel_pos_iff`: the same for `U(x, A)`.
* `pow_add_pos_iff`: `P^{m+n}(x, A) > 0` iff `Pᵐ(x, {y : Pⁿ(y, A) > 0}) > 0`, the form of the
  Chapman–Kolmogorov equations used throughout the chapter.

**Absorbing sets** (MT p. 78 and p. 84): `IsAbsorbing P A` means `P(x, A) = 1` for `x ∈ A`.
`IsAbsorbing.pow_apply`: then `Pⁿ(x, A) = 1`, and `IsAbsorbing.hitProb_compl`: `L(x, Aᶜ) = 0`
for `x ∈ A`. `restrictKernel` is the kernel `P_A` restricted to the states of `A`, a Markov
kernel on `A` when `A` is absorbing (`isMarkovKernel_restrictKernel`), with
`P_Aⁿ(x, B) = Pⁿ(x, B)` (`restrictKernel_pow_apply`).

**Countable spaces** (measurable singletons).
* `Leads P x y` (`x → y`, p. 78): `x = y` or `L(x, {y}) > 0`; `leads_iff_exists_pow`: iff
  `Pⁿ(x, y) > 0` for some `n ≥ 0`; `pow_add_singleton_ge` (from (3.23)):
  `P^{n+m}(x, z) ≥ Pⁿ(x, y) Pᵐ(y, z)`.
* `Communicates P x y` (`x ↔ y`); **Proposition 4.1.1** (`proposition_4_1_1`, p. 78): `↔` is an
  equivalence relation, so the classes `commClass P x = C(x)` cover `X`, with `x ∈ C(x)`
  (`mem_commClass_self`, `iUnion_commClass`, `commClass_eq_or_disjoint`).
* `IsIrreducibleChain P` (p. 78): `C(x) = X` for some `x`; `isIrreducibleChain_iff`: all states
  communicate.
* `not_isAbsorbing_commClass_iff` (p. 78): `C(x)` is not absorbing iff `x → y` for some
  `y ∉ C(x)`.
* The decomposition (4.5), p. 78: `nonAbsorbingPart P = D` is the union of the classes that are
  not absorbing; `decomposition_4_5`: `X` is the union of the absorbing classes and `D`, and
  `decomposition_4_5_disjoint`: the pieces are disjoint.
* **Proposition 4.1.2** (`proposition_4_1_2`, p. 79): an absorbing communicating class `C`
  carries a transition kernel `P_C` with `P_C(x, y) = P(x, y)`, and the chain `Φ_C` with this
  kernel is irreducible.

**Corrections.** None. The heuristic of p. 79–80, that a chain started in `D` is either absorbed
or leaves every finite subset of `D`, is made rigorous only in Proposition 8.3.1 and is not
formalised here.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Reaching a set -/

omit [MeasurableSpace X] in
/-- The event "the chain enters `A` at some time `n ≥ 1`" is the union of the events
`{Φₙ₊₁ ∈ A}`. -/
theorem firstReturn_ne_top_eq_iUnion (A : Set X) :
    {ω : ℕ → X | firstReturn A ω ≠ ⊤} = ⋃ n : ℕ, {ω | ω (n + 1) ∈ A} := by
  ext ω
  rw [mem_ofPred_eq, firstReturn_ne_top_iff, mem_iUnion]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by omega, h⟩

/-- `Pⁿ⁺¹(x, A) ≤ L(x, A)`: the chain is in `A` at time `n + 1` only if it enters `A`. -/
theorem pow_le_hitProb (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (n : ℕ) (x : X) : (P ^ (n + 1)) x A ≤ hitProb P A x := by
  rw [hitProb, firstReturn_ne_top_eq_iUnion, ← pathKernel_coord_mem P x _ hA]
  exact measure_mono (subset_iUnion (fun n => {ω : ℕ → X | ω (n + 1) ∈ A}) n)

/-- **`L(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 1`** (MT p. 78 and p. 82). -/
theorem hitProb_pos_iff (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (x : X) : 0 < hitProb P A x ↔ ∃ n, 0 < (P ^ (n + 1)) x A := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h0 : pathKernel P x (⋃ n : ℕ, {ω : ℕ → X | ω (n + 1) ∈ A}) = 0 :=
      measure_iUnion_null fun n => by
        rw [pathKernel_coord_mem P x _ hA]
        exact nonpos_iff_eq_zero.1 (hc n)
    rw [hitProb, firstReturn_ne_top_eq_iUnion, h0] at h
    exact lt_irrefl _ h
  · rintro ⟨n, hn⟩
    exact hn.trans_le (pow_le_hitProb P hA n x)

/-- `L(x, A) ≤ 1`. -/
theorem hitProb_le_one (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    hitProb P A x ≤ 1 := by
  have := isMarkovKernel_pathKernel P
  exact prob_le_one

/-- `U(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 1`. -/
theorem potKernel_pos_iff (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : X) :
    0 < potKernel P x A ↔ ∃ n, 0 < (P ^ (n + 1)) x A := by
  rw [potKernel_apply P x hA, pos_iff_ne_zero, Ne, ENNReal.tsum_eq_zero]
  push Not
  simp_rw [pos_iff_ne_zero]

/-- **Chapman–Kolmogorov, positivity form**: `P^{m+n}(x, A) > 0` iff
`Pᵐ(x, {y : Pⁿ(y, A) > 0}) > 0`. -/
theorem pow_add_pos_iff (P : Kernel X X) (m n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    0 < (P ^ (m + n)) x A ↔ 0 < (P ^ m) x {y | 0 < (P ^ n) y A} := by
  rw [Kernel.pow_add_apply_eq_lintegral P m n x hA,
    lintegral_pos_iff_support (Kernel.measurable_coe _ hA)]
  have : Function.support (fun y => (P ^ n) y A) = {y | 0 < (P ^ n) y A} := by
    ext y
    simp [Function.mem_support, pos_iff_ne_zero]
  rw [this]

/-- The set `{y : Pⁿ(y, A) > 0}` is measurable. -/
theorem measurableSet_pow_pos (P : Kernel X X) (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet {y | 0 < (P ^ n) y A} :=
  measurableSet_lt measurable_const (Kernel.measurable_coe _ hA)

/-! ### Absorbing sets -/

/-- A set `A` is *absorbing* if `P(x, A) = 1` for every `x ∈ A` (MT p. 78 and p. 84). -/
def IsAbsorbing (P : Kernel X X) (A : Set X) : Prop := ∀ x ∈ A, P x A = 1

/-- From a point of an absorbing set the chain stays in it: `Pⁿ(x, A) = 1` for `x ∈ A`. -/
theorem IsAbsorbing.pow_apply {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) (n : ℕ) {x : X} (hx : x ∈ A) :
    (P ^ n) x A = 1 := by
  induction n with
  | zero => rw [pow_zero_apply, Measure.dirac_apply' _ hA, indicator_of_mem hx, Pi.one_apply]
  | succ n ih =>
    have := isMarkovKernel_pow P (n + 1)
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = ∫⁻ _ in A, 1 ∂(P ^ n) x := by rw [setLIntegral_const, one_mul, ih]
      _ = ∫⁻ y in A, P y A ∂(P ^ n) x :=
          setLIntegral_congr_fun hA fun y hy => (hAbs y hy).symm
      _ ≤ ∫⁻ y, P y A ∂(P ^ n) x := setLIntegral_le_lintegral _ _
      _ = (P ^ (n + 1)) x A := (pow_succ_apply' P n x hA).symm

/-- From a point of an absorbing set, `Pⁿ(x, Aᶜ) = 0`. -/
theorem IsAbsorbing.pow_compl {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) (n : ℕ) {x : X} (hx : x ∈ A) :
    (P ^ n) x Aᶜ = 0 := by
  have := isMarkovKernel_pow P n
  rw [prob_compl_eq_zero_iff hA]
  exact hAbs.pow_apply hA n hx

/-- From a point of an absorbing set, the chain never leaves it: `L(x, Aᶜ) = 0`. -/
theorem IsAbsorbing.hitProb_compl {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) {x : X} (hx : x ∈ A) :
    hitProb P Aᶜ x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA.compl x).1 (pos_iff_ne_zero.2 h)
  rw [hAbs.pow_compl hA (n + 1) hx] at hn
  exact lt_irrefl _ hn

/-- From a point of an absorbing set `A`, no set disjoint from `A` is reached. -/
theorem IsAbsorbing.hitProb_eq_zero {P : Kernel X X} [IsMarkovKernel P] {A B : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) (hB : Disjoint A B) {x : X} (hx : x ∈ A) :
    hitProb P B x = 0 := by
  refine nonpos_iff_eq_zero.1 ?_
  rw [← hAbs.hitProb_compl hA hx]
  exact measure_mono fun ω hω => by
    obtain ⟨n, hn, h⟩ := (firstReturn_ne_top_iff B ω).1 hω
    exact (firstReturn_ne_top_iff Aᶜ ω).2 ⟨n, hn, fun h' => hB.ne_of_mem h' h rfl⟩

/-! ### The kernel restricted to an absorbing set -/

/-- The kernel `P_A` restricted to the states in `A` (MT p. 79 and p. 85):
`P_A(x, B) = P(x, B)` for `x ∈ A` and `B ⊆ A`. -/
noncomputable def restrictKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    Kernel A A :=
  (P.comap Subtype.val measurable_subtype_coe).comapRight (MeasurableEmbedding.subtype_coe hA)

/-- `P_A(x, B) = P(x, B)`. -/
theorem restrictKernel_apply (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : A)
    {B : Set A} (hB : MeasurableSet B) : restrictKernel P hA x B = P x (Subtype.val '' B) := by
  rw [restrictKernel, Kernel.comapRight_apply' _ _ _ hB, Kernel.comap_apply]

/-- `P_A(x, ·)` is `P(x, ·)` pulled back to `A`. -/
theorem restrictKernel_apply_eq (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : A) :
    restrictKernel P hA x = (P x).comap Subtype.val := by
  rw [restrictKernel, Kernel.comapRight_apply, Kernel.comap_apply]

/-- `P_A` is a transition probability kernel on `A` when `A` is absorbing (MT p. 79, p. 85). -/
theorem isMarkovKernel_restrictKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (hAbs : IsAbsorbing P A) : IsMarkovKernel (restrictKernel P hA) :=
  Kernel.IsMarkovKernel.comapRight _ _ fun x => by
    rw [Kernel.comap_apply, Subtype.range_coe]
    exact hAbs x x.2

/-- Integrals against `P_A(x, ·)` are integrals against `P(x, ·)` when `A` is absorbing. -/
theorem lintegral_restrictKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) (x : A) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂restrictKernel P hA x = ∫⁻ y, g y ∂P x := by
  rw [restrictKernel_apply_eq, ← lintegral_map hg measurable_subtype_coe,
    map_comap_subtype_coe hA, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  have : {a | ¬ a ∈ A} = Aᶜ := rfl
  rw [this, prob_compl_eq_zero_iff hA]
  exact hAbs x x.2

/-- The `n`-step kernel of `P_A` is `Pⁿ` restricted to `A`: `P_Aⁿ(x, B) = Pⁿ(x, B)`. -/
theorem restrictKernel_pow_apply (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) (n : ℕ) (x : A) {B : Set A}
    (hB : MeasurableSet B) : (restrictKernel P hA ^ n) x B = (P ^ n) x (Subtype.val '' B) := by
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, pow_zero_apply, Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB']
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem (mem_image_of_mem _ hx)]
      rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem]
      rintro ⟨y, hy, hyx⟩
      exact hx (Subtype.ext hyx ▸ hy)
  | succ n ih =>
    rw [pow_succ_apply _ n x hB, pow_succ_apply _ n _ hB']
    simp_rw [ih]
    exact lintegral_restrictKernel P hA hAbs x (g := fun y => (P ^ n) y (Subtype.val '' B))
      (Kernel.measurable_coe _ hB')

/-! ### Communication on a countable space -/

variable [MeasurableSingletonClass X]

/-- `x` *leads to* `y`, `x → y` (MT p. 78): `L(x, y) > 0`, with the convention `x → x`. -/
def Leads (P : Kernel X X) [IsMarkovKernel P] (x y : X) : Prop :=
  x = y ∨ 0 < hitProb P {y} x

/-- `x → y` iff `Pⁿ(x, y) > 0` for some `n ≥ 0` (MT p. 78). -/
theorem leads_iff_exists_pow (P : Kernel X X) [IsMarkovKernel P] (x y : X) :
    Leads P x y ↔ ∃ n, 0 < (P ^ n) x {y} := by
  rw [Leads, hitProb_pos_iff P (measurableSet_singleton y)]
  constructor
  · rintro (rfl | ⟨n, hn⟩)
    · exact ⟨0, by rw [pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton x)]; exact one_pos⟩
    · exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · left
      rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton y)] at hn
      by_contra hxy
      rw [indicator_of_notMem (by simpa using hxy)] at hn
      exact lt_irrefl _ hn
    · exact Or.inr ⟨n, hn⟩

/-- (3.23), MT p. 78: `P^{n+m}(x, z) ≥ Pⁿ(x, y) Pᵐ(y, z)`. -/
theorem pow_add_singleton_ge (P : Kernel X X) (n m : ℕ) (x y z : X) :
    (P ^ n) x {y} * (P ^ m) y {z} ≤ (P ^ (n + m)) x {z} := by
  rw [Kernel.pow_add_apply_eq_lintegral P n m x (measurableSet_singleton z), mul_comm]
  calc (P ^ m) y {z} * (P ^ n) x {y} = ∫⁻ b in {y}, (P ^ m) b {z} ∂(P ^ n) x :=
        (lintegral_singleton (fun b => (P ^ m) b {z}) y).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- `→` is transitive (MT p. 78). -/
theorem Leads.trans {P : Kernel X X} [IsMarkovKernel P] {x y z : X} (hxy : Leads P x y)
    (hyz : Leads P y z) : Leads P x z := by
  rw [leads_iff_exists_pow] at hxy hyz ⊢
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  exact ⟨n + m, (ENNReal.mul_pos hn.ne' hm.ne').trans_le (pow_add_singleton_ge P n m x y z)⟩

omit [MeasurableSingletonClass X] in
/-- `x → x`. -/
theorem Leads.refl (P : Kernel X X) [IsMarkovKernel P] (x : X) : Leads P x x := Or.inl rfl

/-- `x` and `y` *communicate*, `x ↔ y` (MT p. 78): `x → y` and `y → x`. -/
def Communicates (P : Kernel X X) [IsMarkovKernel P] (x y : X) : Prop :=
  Leads P x y ∧ Leads P y x

/-- **Proposition 4.1.1** (MT p. 78): `↔` is an equivalence relation. -/
theorem proposition_4_1_1 (P : Kernel X X) [IsMarkovKernel P] : Equivalence (Communicates P) :=
  ⟨fun x => ⟨Leads.refl P x, Leads.refl P x⟩, fun h => ⟨h.2, h.1⟩,
    fun h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩⟩

/-- The communicating class `C(x) = {y : x ↔ y}` (MT p. 78). -/
def commClass (P : Kernel X X) [IsMarkovKernel P] (x : X) : Set X := {y | Communicates P x y}

/-- `x ∈ C(x)`. -/
theorem mem_commClass_self (P : Kernel X X) [IsMarkovKernel P] (x : X) : x ∈ commClass P x :=
  (proposition_4_1_1 P).refl x

/-- The communicating classes cover `X` (Proposition 4.1.1). -/
theorem iUnion_commClass (P : Kernel X X) [IsMarkovKernel P] :
    ⋃ x, commClass P x = univ :=
  eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_commClass_self P x⟩

/-- Two communicating classes are equal or disjoint (Proposition 4.1.1). -/
theorem commClass_eq_or_disjoint (P : Kernel X X) [IsMarkovKernel P] (x y : X) :
    commClass P x = commClass P y ∨ Disjoint (commClass P x) (commClass P y) := by
  have he := proposition_4_1_1 P
  by_cases h : Communicates P x y
  · left
    ext z
    exact ⟨fun hz => he.trans (he.symm h) hz, fun hz => he.trans h hz⟩
  · right
    exact Set.disjoint_left.2 fun z hx hy => h (he.trans hx (he.symm hy))

/-- `y ∈ C(x)` iff `C(x) = C(y)`. -/
theorem commClass_eq_iff (P : Kernel X X) [IsMarkovKernel P] (x y : X) :
    commClass P x = commClass P y ↔ y ∈ commClass P x := by
  have he := proposition_4_1_1 P
  constructor
  · intro h
    rw [h]
    exact mem_commClass_self P y
  · intro h
    ext z
    exact ⟨fun hz => he.trans (he.symm h) hz, fun hz => he.trans h hz⟩

/-- An *irreducible* chain on a countable space (MT p. 78): `C(x) = X` for some `x`. -/
def IsIrreducibleChain (P : Kernel X X) [IsMarkovKernel P] : Prop := ∃ x, commClass P x = univ

/-- A chain is irreducible iff all states communicate. -/
theorem isIrreducibleChain_iff (P : Kernel X X) [IsMarkovKernel P] [Nonempty X] :
    IsIrreducibleChain P ↔ ∀ x y, Communicates P x y := by
  have he := proposition_4_1_1 P
  constructor
  · rintro ⟨x₀, hx₀⟩ x y
    have hx : x ∈ commClass P x₀ := hx₀ ▸ mem_univ x
    have hy : y ∈ commClass P x₀ := hx₀ ▸ mem_univ y
    exact he.trans (he.symm hx) hy
  · intro h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact ⟨x₀, eq_univ_of_forall fun y => h x₀ y⟩

/-- The set `D` of states whose communicating class is not absorbing (MT (4.5), p. 78). -/
def nonAbsorbingPart (P : Kernel X X) [IsMarkovKernel P] : Set X :=
  {x | ¬ IsAbsorbing P (commClass P x)}

/-- `D` is a union of communicating classes: with `x`, it contains all of `C(x)`. -/
theorem commClass_subset_nonAbsorbingPart (P : Kernel X X) [IsMarkovKernel P] {x : X}
    (hx : x ∈ nonAbsorbingPart P) : commClass P x ⊆ nonAbsorbingPart P := fun y hy => by
  change ¬ IsAbsorbing P (commClass P y)
  rwa [← (commClass_eq_iff P x y).2 hy]

/-- **The decomposition (4.5)** (MT p. 78): `X = ⋃_{C(x) absorbing} C(x) ∪ D`. -/
theorem decomposition_4_5 (P : Kernel X X) [IsMarkovKernel P] :
    (⋃ x ∈ {x | IsAbsorbing P (commClass P x)}, commClass P x) ∪ nonAbsorbingPart P = univ := by
  refine eq_univ_of_forall fun y => ?_
  by_cases hy : IsAbsorbing P (commClass P y)
  · exact Or.inl (mem_biUnion hy (mem_commClass_self P y))
  · exact Or.inr hy

/-- The pieces of (4.5) are disjoint: distinct absorbing classes are disjoint, and every
absorbing class is disjoint from `D`. -/
theorem decomposition_4_5_disjoint (P : Kernel X X) [IsMarkovKernel P] :
    (∀ x y, commClass P x ≠ commClass P y → Disjoint (commClass P x) (commClass P y)) ∧
      Disjoint (⋃ x ∈ {x | IsAbsorbing P (commClass P x)}, commClass P x)
        (nonAbsorbingPart P) := by
  refine ⟨fun x y h => (commClass_eq_or_disjoint P x y).resolve_left h, ?_⟩
  refine Set.disjoint_left.2 fun z hz hD => ?_
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
  exact hD (by rwa [← (commClass_eq_iff P x z).2 hzx])

variable [Countable X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- On a countable space with measurable singletons every set is measurable. -/
theorem measurableSet_of_countable [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Set X) : MeasurableSet A :=
  (Set.to_countable A).measurableSet

omit [MeasurableSingletonClass X] in
/-- A positive mass on a countable set sits on one of its points. -/
theorem exists_singleton_pos_of_pos (μ : Measure X) {A : Set X} (h : 0 < μ A) :
    ∃ y ∈ A, 0 < μ {y} := by
  by_contra hc
  push Not at hc
  have : μ (⋃ y ∈ A, {y}) = 0 :=
    (measure_biUnion_null_iff (Set.to_countable A)).2 fun y hy => nonpos_iff_eq_zero.1 (hc y hy)
  rw [biUnion_of_singleton] at this
  exact lt_irrefl _ (this ▸ h)

/-- MT p. 78: `C(x)` is not absorbing iff `x → y` for some state `y ∉ C(x)`. -/
theorem not_isAbsorbing_commClass_iff (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    ¬ IsAbsorbing P (commClass P x) ↔ ∃ y ∉ commClass P x, Leads P x y := by
  have hC := measurableSet_of_countable (commClass P x)
  constructor
  · intro h
    simp only [IsAbsorbing, not_forall] at h
    obtain ⟨z, hz, hz1⟩ := h
    have hpos : 0 < P z (commClass P x)ᶜ := by
      rw [pos_iff_ne_zero, Ne, prob_compl_eq_zero_iff hC]
      exact hz1
    obtain ⟨y, hy, hzy⟩ := exists_singleton_pos_of_pos (P z) hpos
    refine ⟨y, hy, hz.1.trans ((leads_iff_exists_pow P z y).2 ⟨1, by rwa [pow_one]⟩)⟩
  · rintro ⟨y, hy, hxy⟩ hAbs
    obtain ⟨n, hn⟩ := (leads_iff_exists_pow P x y).1 hxy
    have h0 := hAbs.pow_compl hC n (mem_commClass_self P x)
    have : (P ^ n) x {y} ≤ (P ^ n) x (commClass P x)ᶜ :=
      measure_mono (singleton_subset_iff.2 hy)
    rw [h0] at this
    exact lt_irrefl _ (hn.trans_le this)

/-- **Proposition 4.1.2** (MT p. 79). If `C = C(x)` is an absorbing communicating class, the
matrix `P_C` (`P` restricted to the states of `C`) is a transition matrix, `P_C(y, z) = P(y, z)`,
and the chain `Φ_C` it defines on `C` is irreducible. -/
theorem proposition_4_1_2 (P : Kernel X X) [IsMarkovKernel P] (x : X)
    (hAbs : IsAbsorbing P (commClass P x)) :
    ∃ _ : IsMarkovKernel (restrictKernel P (measurableSet_of_countable (commClass P x))),
      (∀ y z : commClass P x,
        restrictKernel P (measurableSet_of_countable (commClass P x)) y {z} = P y {(z : X)}) ∧
      IsIrreducibleChain (restrictKernel P (measurableSet_of_countable (commClass P x))) := by
  set C := commClass P x with hCdef
  have hC := measurableSet_of_countable C
  have hM := isMarkovKernel_restrictKernel P hC hAbs
  refine ⟨hM, fun y z => ?_, ?_⟩
  · rw [restrictKernel_apply P hC y (measurableSet_singleton z), image_singleton]
  · have he := proposition_4_1_1 P
    have hlead : ∀ y z : C, Leads (restrictKernel P hC) y z := fun y z => by
      have hyz : Leads P y z := (he.trans (he.symm y.2) z.2).1
      obtain ⟨n, hn⟩ := (leads_iff_exists_pow P y z).1 hyz
      refine (leads_iff_exists_pow _ y z).2 ⟨n, ?_⟩
      rw [restrictKernel_pow_apply P hC hAbs n y (measurableSet_singleton z), image_singleton]
      exact hn
    exact ⟨⟨x, mem_commClass_self P x⟩, eq_univ_of_forall fun z =>
      ⟨hlead _ z, hlead z _⟩⟩

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# φ-irreducibility (MT §4.2.1)

Meyn and Tweedie, §4.2.1, pp. 81–83. Throughout, `X` is an arbitrary measurable space: none of
the results needs a countably generated σ-algebra.

* `IsPhiIrreducible P φ` (p. 82): `φ(A) > 0` implies `L(x, A) > 0` for every `x`.
* `resolventHalf P = K_{a_{1/2}}` (4.9), with `resolventHalf_apply`:
  `K_{a_{1/2}}(x, A) = Σₙ Pⁿ(x, A) 2^{-(n+1)}`; `isMarkovKernel_resolventHalf`: it is a
  transition kernel; `resolventHalf_pos_iff`: `K_{a_{1/2}}(x, A) > 0` iff `Pⁿ(x, A) > 0` for
  some `n ≥ 0`; `resolventHalf_eq_zero_iff`, `resolventHalf_equiv` (p. 82): `K_{a_{1/2}}(x, ·)`
  is a probability measure equivalent to `I(x, ·) + U(x, ·)`.
* `hitProb_pos_of_compl` (the proof of Proposition 4.2.1): if `L(y, A) > 0` for every `y ∉ A`,
  then `L(x, A) > 0` for every `x`.
* **Proposition 4.2.1** (`proposition_4_2_1`, p. 82): φ-irreducibility is equivalent to each of
  (i) `U(x, A) > 0`, (ii) `Pⁿ(x, A) > 0` for some `n ≥ 1`, (iii) `K_{a_{1/2}}(x, A) > 0`,
  whenever `φ(A) > 0`.
* `IsPhiIrreducible.mono` (p. 82–83): a measure absolutely continuous with respect to an
  irreducibility measure (for instance a restriction, or an equivalent probability measure) is
  an irreducibility measure; `isPhiIrreducible_zero`: the zero measure is one for every chain.
* `isPhiIrreducible_dirac_of_leads` (p. 82): if every state leads to `x*`, the chain is
  `δ_{x*}`-irreducible; `isPhiIrreducible_dirac_iff`: this happens iff `L(x, {x*}) > 0` for all
  `x`.
* `isIrreducibleChain_iff_count` (p. 83): on a countable space, irreducibility in the sense of
  §4.1 is counting-measure irreducibility.

**Corrections.** None. The book's convention `x → x` (p. 78) does not give `L(x*, {x*}) > 0`
directly, but `isPhiIrreducible_dirac_of_leads` shows the claim of p. 82 holds as stated.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **φ-irreducibility** (MT p. 82): whenever `φ(A) > 0`, `L(x, A) > 0` for every `x ∈ X`. -/
def IsPhiIrreducible (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) : Prop :=
  ∀ A, MeasurableSet A → 0 < φ A → ∀ x, 0 < hitProb P A x

/-! ### The resolvent `K_{a_{1/2}}` -/

/-- The kernel `K_{a_{1/2}} = Σₙ 2^{-(n+1)} Pⁿ` (4.9), MT p. 82: the resolvent `K_{a_ε}` of
(3.26) with `ε = 1/2`. -/
noncomputable abbrev resolventHalf (P : Kernel X X) : Kernel X X := resolvent P 2⁻¹

/-- (4.9): `K_{a_{1/2}}(x, A) = Σₙ Pⁿ(x, A) 2^{-(n+1)}`. -/
theorem resolventHalf_apply (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    resolventHalf P x A = ∑' n, (P ^ n) x A * 2⁻¹ ^ (n + 1) := by
  rw [resolventHalf, resolvent, sampledKernel_apply P _ x hA]
  refine tsum_congr fun n => ?_
  rw [ENNReal.one_sub_inv_two, pow_succ, mul_comm, mul_comm (2⁻¹ ^ n)]

/-- `K_{a_{1/2}}` is a transition probability kernel. -/
theorem isMarkovKernel_resolventHalf (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovKernel (resolventHalf P) :=
  isMarkovKernel_resolvent P (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)

/-- `K_{a_{1/2}}(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 0`. -/
theorem resolventHalf_pos_iff (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    0 < resolventHalf P x A ↔ ∃ n, 0 < (P ^ n) x A := by
  rw [resolventHalf_apply P x hA, pos_iff_ne_zero, Ne, ENNReal.tsum_eq_zero]
  push Not
  refine exists_congr fun n => ?_
  rw [mul_ne_zero_iff, pos_iff_ne_zero]
  exact and_iff_left (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))

/-- `K_{a_{1/2}}(x, A) = 0` iff `I(x, A) + U(x, A) = Σ_{n ≥ 0} Pⁿ(x, A) = 0` (MT p. 82). -/
theorem resolventHalf_eq_zero_iff (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    resolventHalf P x A = 0 ↔ Measure.dirac x A + potKernel P x A = 0 := by
  have h1 := resolventHalf_pos_iff P x hA
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← pos_iff_ne_zero, ← pos_iff_ne_zero, h1,
    add_pos_iff, potKernel_pos_iff P hA x]
  constructor
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · left
      rwa [pow_zero_apply] at hn
    · exact Or.inr ⟨n, hn⟩
  · rintro (h | ⟨n, hn⟩)
    · exact ⟨0, by rwa [pow_zero_apply]⟩
    · exact ⟨n + 1, hn⟩

/-- MT p. 82: `K_{a_{1/2}}(x, ·)` is equivalent to `I(x, ·) + U(x, ·)`: they have the same null
sets. -/
theorem resolventHalf_equiv (P : Kernel X X) (x : X) :
    resolventHalf P x ≪ Measure.dirac x + potKernel P x ∧
      Measure.dirac x + potKernel P x ≪ resolventHalf P x := by
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun A hA h => ?_
    rw [Measure.add_apply] at h
    exact (resolventHalf_eq_zero_iff P x hA).2 h
  · refine Measure.AbsolutelyContinuous.mk fun A hA h => ?_
    rw [Measure.add_apply]
    exact (resolventHalf_eq_zero_iff P x hA).1 h

/-! ### Proposition 4.2.1 -/

/-- The step in the proof of Proposition 4.2.1 (MT p. 82): if `L(y, A) > 0` for every `y ∉ A`,
then `L(x, A) > 0` for every `x`, by `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`. -/
theorem hitProb_pos_of_compl (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (h : ∀ y ∉ A, 0 < hitProb P A y) (x : X) : 0 < hitProb P A x := by
  rw [hitProb_first_step P hA x]
  by_cases hx : P x A = 0
  · have hc : P x Aᶜ = 1 := by rw [prob_compl_eq_one_sub hA, hx, tsub_zero]
    refine add_pos_iff.2 (Or.inr ?_)
    rw [setLIntegral_pos_iff (measurable_hitProb P hA)]
    have : Function.support (hitProb P A) ∩ Aᶜ = Aᶜ :=
      inter_eq_right.2 fun y hy => (h y hy).ne'
    rw [this, hc]
    exact one_pos
  · exact add_pos_iff.2 (Or.inl (pos_iff_ne_zero.2 hx))

/-- **Proposition 4.2.1** (MT p. 82). The chain is φ-irreducible iff, whenever `φ(A) > 0`,
for every `x`: (i) `U(x, A) > 0`; equivalently (ii) `Pⁿ(x, A) > 0` for some `n ≥ 1`;
equivalently (iii) `K_{a_{1/2}}(x, A) > 0`. -/
theorem proposition_4_2_1 (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) :
    (IsPhiIrreducible P φ ↔
      ∀ A, MeasurableSet A → 0 < φ A → ∀ x, 0 < potKernel P x A) ∧
    (IsPhiIrreducible P φ ↔
      ∀ A, MeasurableSet A → 0 < φ A → ∀ x, ∃ n, 0 < (P ^ (n + 1)) x A) ∧
    (IsPhiIrreducible P φ ↔
      ∀ A, MeasurableSet A → 0 < φ A → ∀ x, 0 < resolventHalf P x A) := by
  refine ⟨?_, ?_, ?_⟩
  · refine forall₄_congr fun A hA _ x => ?_
    rw [hitProb_pos_iff P hA, potKernel_pos_iff P hA]
  · exact forall₄_congr fun A hA _ x => hitProb_pos_iff P hA x
  · constructor
    · intro h A hA hφ x
      obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA x).1 (h A hA hφ x)
      exact (resolventHalf_pos_iff P x hA).2 ⟨n + 1, hn⟩
    · intro h A hA hφ
      refine hitProb_pos_of_compl P hA fun y hy => ?_
      obtain ⟨n, hn⟩ := (resolventHalf_pos_iff P y hA).1 (h A hA hφ y)
      rcases n with _ | n
      · rw [pow_zero_apply, Measure.dirac_apply' _ hA, indicator_of_notMem hy] at hn
        exact absurd hn (lt_irrefl _)
      · exact (hitProb_pos_iff P hA y).2 ⟨n, hn⟩

/-! ### Elementary facts about irreducibility measures -/

/-- MT pp. 82–83: a measure absolutely continuous with respect to an irreducibility measure is an
irreducibility measure. In particular any restriction of an irreducibility measure, and any
measure equivalent to one, is an irreducibility measure. -/
theorem IsPhiIrreducible.mono {P : Kernel X X} [IsMarkovKernel P] {φ φ' : Measure X}
    (h : IsPhiIrreducible P φ) (hφ : φ' ≪ φ) : IsPhiIrreducible P φ' :=
  fun A hA hpos => h A hA (pos_iff_ne_zero.2 fun h0 => hpos.ne' (hφ h0))

/-- A restriction of an irreducibility measure is an irreducibility measure (MT p. 82). -/
theorem IsPhiIrreducible.restrict {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (h : IsPhiIrreducible P φ) (B : Set X) : IsPhiIrreducible P (φ.restrict B) :=
  h.mono Measure.absolutelyContinuous_restrict

/-- Every chain is `0`-irreducible: the definition is vacuous for the zero measure. -/
theorem isPhiIrreducible_zero (P : Kernel X X) [IsMarkovKernel P] :
    IsPhiIrreducible P (0 : Measure X) :=
  fun A _ h => absurd h (by simp)

/-- `δ_{x*}`-irreducibility: the chain is `δ_{x*}`-irreducible iff `L(x, {x*}) > 0` for all
`x`. -/
theorem isPhiIrreducible_dirac_iff (P : Kernel X X) [IsMarkovKernel P] [MeasurableSingletonClass X]
    (xs : X) : IsPhiIrreducible P (Measure.dirac xs) ↔ ∀ x, 0 < hitProb P {xs} x := by
  constructor
  · intro h x
    exact h {xs} (measurableSet_singleton xs) (by simp) x
  · intro h A hA hpos x
    rw [Measure.dirac_apply' _ hA] at hpos
    have hxs : xs ∈ A := by
      by_contra hc
      rw [indicator_of_notMem hc] at hpos
      exact lt_irrefl _ hpos
    exact (h x).trans_le (measure_mono fun ω hω => by
      obtain ⟨n, hn, h'⟩ := (firstReturn_ne_top_iff {xs} ω).1 hω
      exact (firstReturn_ne_top_iff A ω).2 ⟨n, hn, (mem_singleton_iff.1 h') ▸ hxs⟩)

/-- MT p. 82: on a countable space, if `x → x*` for every state `x`, the chain is
`δ_{x*}`-irreducible. (For `x = x*` the convention `x* → x*` is not a return to `x*`; the
return follows from the other states, as in the proof of Proposition 4.2.1.) -/
theorem isPhiIrreducible_dirac_of_leads (P : Kernel X X) [IsMarkovKernel P]
    [MeasurableSingletonClass X] (xs : X) (h : ∀ x, Leads P x xs) :
    IsPhiIrreducible P (Measure.dirac xs) := by
  rw [isPhiIrreducible_dirac_iff]
  refine hitProb_pos_of_compl P (measurableSet_singleton xs) fun y hy => ?_
  exact (h y).resolve_left hy

/-- MT p. 83: on a countable space, irreducibility in the sense of §4.1 is
irreducibility with respect to counting measure. -/
theorem isIrreducibleChain_iff_count (P : Kernel X X) [IsMarkovKernel P]
    [MeasurableSingletonClass X] [Nonempty X] :
    IsIrreducibleChain P ↔ IsPhiIrreducible P Measure.count := by
  rw [isIrreducibleChain_iff]
  constructor
  · intro h A hA hpos x
    obtain ⟨y, hy⟩ : A.Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty.1 hc, measure_empty] at hpos
      exact lt_irrefl _ hpos
    have hy' : 0 < hitProb P {y} x := by
      have := isPhiIrreducible_dirac_of_leads P y fun z => (h z y).1
      exact this {y} (measurableSet_singleton y) (by simp) x
    exact hy'.trans_le (measure_mono fun ω hω => by
      obtain ⟨n, hn, h'⟩ := (firstReturn_ne_top_iff {y} ω).1 hω
      exact (firstReturn_ne_top_iff A ω).2 ⟨n, hn, (mem_singleton_iff.1 h') ▸ hy⟩)
  · intro h x y
    have hl : ∀ a b : X, Leads P a b := fun a b =>
      Or.inr (h {b} (measurableSet_singleton b) (by simp) a)
    exact ⟨hl x y, hl y x⟩

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Maximal irreducibility measures, full and absorbing sets (MT §4.0, §4.2.2)

Meyn and Tweedie, Theorem 4.0.1 (p. 75) and §4.2.2, pp. 82–85. `X` is an arbitrary measurable
space and the irreducibility measure `φ` an arbitrary nonzero measure: neither a countably
generated σ-algebra nor σ-finiteness of `φ` is needed.

* `exists_finite_equiv_of_ac`: a measure `φ ≪ μ`, `μ` finite, has an equivalent finite measure
  (`μ` restricted to the complement of a largest `φ`-null set); `exists_prob_equiv`: hence every
  nonzero irreducibility measure has an equivalent probability measure, the reduction "without
  loss of generality `φ(X) = 1`" of p. 83.
* `maxIrrMeasure P φ = ψ` (4.10): `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)`;
  `isPhiIrreducible_maxIrrMeasure` (i), `ac_maxIrrMeasure` (ii), `maxIrrMeasure_hitSet_null`
  (iii), and
  `maxIrrMeasure_comp_pow_le`: the inequality `ψPᵐ ≤ 2ᵐ ψ` of the proof.
* `IsMaximalIrreducibility P ψ` (p. 84): `ψ ≠ 0` is an irreducibility measure and every
  irreducibility measure is absolutely continuous with respect to it.
* **Proposition 4.2.2** (`proposition_4_2_2`, p. 83): a nonzero irreducibility measure `φ` gives a
  probability measure `ψ` with (i)–(iv); `proposition_4_2_2_maximal`: `ψ` is maximal.
* **Theorem 4.0.1** (`theorem_4_0_1`, p. 75) and `theorem_4_0_1_unique`: existence and
  essential uniqueness of the maximal irreducibility measure.
* `posSets ψ = B⁺(X)` and `posSets_eq_of_maximal`: `B⁺(X)` does not depend on the choice of `ψ`
  (p. 84); `IsFull ψ A` (p. 84).
* **Proposition 4.2.3** (p. 84): (i) `proposition_4_2_3_i`, every non-empty absorbing set is full;
  (ii) `proposition_4_2_3_ii`, every full set contains a non-empty absorbing (and full) set.
* `IsAbsorbingIrreducibleSet` (p. 85) and **Proposition 4.2.4** (`proposition_4_2_4`, p. 85):
  the chain restricted to an absorbing set is a chain on that set, irreducible for the
  restricted measure.
* `isMaximalIrreducibility_count` (p. 83): for an irreducible chain on a countable space,
  counting measure is a maximal irreducibility measure.

**Corrections.**
* Proposition 4.2.2 and Theorem 4.0.1 need `φ ≠ 0`: every chain is `0`-irreducible, but the
  identity chain on `Bool` is `ψ`-irreducible for no probability measure `ψ`
  (`proposition_4_2_2_zero_counterexample`). In (iv) the measure `φ'` must be nonzero, and
  need not be finite.
* Proposition 4.2.3 (i) needs the absorbing set to be non-empty: `∅` is absorbing but full for no
  nonzero `ψ` (`proposition_4_2_3_i_counterexample`). Part (i) holds for every irreducibility
  measure, not only for a maximal one.
* Proposition 4.2.4 does not need Proposition 4.2.3: the restricted chain is irreducible for the
  restriction of any irreducibility measure.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A positive mass on a countable union sits on one of the sets. -/
theorem exists_measure_pos_of_iUnion {μ : Measure X} {s : ℕ → Set X}
    (h : 0 < μ (⋃ n, s n)) : ∃ n, 0 < μ (s n) := by
  by_contra hc
  push Not at hc
  rw [measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)] at h
  exact lt_irrefl _ h

/-- `{y : K_{a_{1/2}}(y, A) > 0} = ⋃ₙ {y : Pⁿ(y, A) > 0}`. -/
theorem setOf_resolventHalf_pos (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    {y | 0 < resolventHalf P y A} = ⋃ n, {y | 0 < (P ^ n) y A} := by
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  exact resolventHalf_pos_iff P y hA

/-- `Ā = {y : L(y, A) > 0} = ⋃ₙ {y : Pⁿ⁺¹(y, A) > 0}`. -/
theorem setOf_hitProb_pos (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) :
    {y | 0 < hitProb P A y} = ⋃ n, {y | 0 < (P ^ (n + 1)) y A} := by
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  exact hitProb_pos_iff P hA y

/-- `Ā = {y : L(y, A) > 0}` is measurable. -/
theorem measurableSet_hitProb_pos (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : MeasurableSet {y | 0 < hitProb P A y} :=
  measurableSet_lt measurable_const (measurable_hitProb P hA)

/-! ### Equivalent probability measures -/

/-- **Exhaustion.** If `φ ≪ μ` with `μ` finite, then `μ` restricted to the complement of a
largest `φ`-null set is a finite measure equivalent to `φ`. No σ-finiteness of `φ` is needed. -/
theorem exists_finite_equiv_of_ac {φ μ : Measure X} [IsFiniteMeasure μ] (h : φ ≪ μ) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ ν ≪ φ ∧ φ ≪ ν := by
  set N : Set (Set X) := {B | MeasurableSet B ∧ φ B = 0}
  set S : Set ℝ≥0∞ := μ '' N
  have hSne : S.Nonempty := ⟨μ ∅, ∅, ⟨MeasurableSet.empty, measure_empty⟩, rfl⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne (OrderTop.bddAbove S)
  choose B hB hBu using huS
  set Bs := ⋃ n, B n
  have hBs : MeasurableSet Bs := MeasurableSet.iUnion fun n => (hB n).1
  have hφBs : φ Bs = 0 := measure_iUnion_null fun n => (hB n).2
  have hge : sSup S ≤ μ Bs :=
    le_of_tendsto' hu fun n => (hBu n) ▸ measure_mono (subset_iUnion B n)
  refine ⟨μ.restrict Bsᶜ, inferInstance, ?_, ?_⟩
  · refine Measure.AbsolutelyContinuous.mk fun A hA hφA => ?_
    rw [Measure.restrict_apply hA, ← sdiff_eq]
    have h1 : μ (A ∪ Bs) ≤ μ Bs :=
      (le_sSup (show μ (A ∪ Bs) ∈ S from
        ⟨A ∪ Bs, ⟨hA.union hBs, measure_union_null hφA hφBs⟩, rfl⟩)).trans hge
    rw [← sdiff_union_self, measure_union disjoint_sdiff_left hBs] at h1
    have h2 : μ (A \ Bs) + μ Bs ≤ 0 + μ Bs := by rwa [zero_add]
    exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right (measure_ne_top μ Bs)).1 h2)
  · refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    rw [Measure.restrict_apply hA] at h0
    rw [← inter_union_compl A Bs]
    exact measure_union_null (measure_mono_null inter_subset_right hφBs) (h h0)

/-- Every nonzero irreducibility measure is equivalent to a probability measure, which is again
an irreducibility measure (MT p. 83: "without loss of generality `φ(X) = 1`"). -/
theorem exists_prob_equiv (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ φ₀ : Measure X, IsProbabilityMeasure φ₀ ∧ φ₀ ≪ φ ∧ φ ≪ φ₀ := by
  have hne : (univ : Set X).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    exact h0 (Measure.measure_univ_eq_zero.1 (hc ▸ measure_empty))
  obtain ⟨x₀, -⟩ := hne
  have := isMarkovKernel_resolventHalf P
  have hac : φ ≪ resolventHalf P x₀ := Measure.AbsolutelyContinuous.mk fun A hA hK => by
    by_contra hc
    have := (proposition_4_2_1 P φ).2.2.1 hφ A hA (pos_iff_ne_zero.2 hc) x₀
    exact this.ne' hK
  obtain ⟨ν, hνf, hνφ, hφν⟩ := exists_finite_equiv_of_ac hac
  have hν0 : ν univ ≠ 0 := fun h => h0 (Measure.measure_univ_eq_zero.1 (hφν h))
  refine ⟨(ν univ)⁻¹ • ν, ⟨?_⟩, Measure.smul_absolutelyContinuous.trans hνφ,
    hφν.trans (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.2 (measure_ne_top ν _)))⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hν0 (measure_ne_top ν _)]

/-! ### The measure `ψ` of (4.10) -/

/-- The measure `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)` of (4.10), MT p. 83. -/
noncomputable def maxIrrMeasure (P : Kernel X X) (φ : Measure X) : Measure X :=
  resolventHalf P ∘ₘ φ

/-- (4.10): `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)`. -/
theorem maxIrrMeasure_apply (P : Kernel X X) (φ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : maxIrrMeasure P φ A = ∫⁻ y, resolventHalf P y A ∂φ :=
  measure_kernel_apply φ _ hA

/-- `ψ(X) = φ(X)`; in particular `ψ` is a probability measure when `φ` is (MT p. 83). -/
theorem maxIrrMeasure_univ (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) :
    maxIrrMeasure P φ univ = φ univ := by
  have := isMarkovKernel_resolventHalf P
  rw [maxIrrMeasure_apply P φ MeasurableSet.univ]
  simp

/-- `ψ` is a probability measure when `φ` is. -/
theorem isProbabilityMeasure_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsProbabilityMeasure φ] : IsProbabilityMeasure (maxIrrMeasure P φ) :=
  ⟨by rw [maxIrrMeasure_univ, measure_univ]⟩

/-- **Proposition 4.2.2 (i)** for the measure (4.10): if `φ` is an irreducibility measure, so is
`ψ`. -/
theorem isPhiIrreducible_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) : IsPhiIrreducible P (maxIrrMeasure P φ) := by
  intro A hA hpos x
  rw [maxIrrMeasure_apply P φ hA, lintegral_pos_iff_support (Kernel.measurable_coe _ hA)] at hpos
  have hsupp : Function.support (fun y => resolventHalf P y A) = {y | 0 < resolventHalf P y A} := by
    ext y
    simp [Function.mem_support, pos_iff_ne_zero]
  rw [hsupp, setOf_resolventHalf_pos P hA] at hpos
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hpos
  obtain ⟨m, hm⟩ := (hitProb_pos_iff P (measurableSet_pow_pos P n hA) x).1
    (hφ _ (measurableSet_pow_pos P n hA) hn x)
  refine (hitProb_pos_iff P hA x).2 ⟨m + n, ?_⟩
  rw [show m + n + 1 = (m + 1) + n by omega]
  exact (pow_add_pos_iff P (m + 1) n x hA).2 hm

/-- **Proposition 4.2.2 (ii)** for the measure (4.10): if `φ ≠ 0`, every irreducibility measure
is absolutely continuous with respect to `ψ`. -/
theorem ac_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P] {φ φ' : Measure X} (h0 : φ ≠ 0)
    (hφ' : IsPhiIrreducible P φ') : φ' ≪ maxIrrMeasure P φ := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hψ => ?_
  by_contra hc
  have hK := (proposition_4_2_1 P φ').2.2.1 hφ' A hA (pos_iff_ne_zero.2 hc)
  have hpos : 0 < ∫⁻ y, resolventHalf P y A ∂φ := by
    rw [lintegral_pos_iff_support (Kernel.measurable_coe _ hA)]
    have : Function.support (fun y => resolventHalf P y A) = univ :=
      eq_univ_of_forall fun y => (hK y).ne'
    rw [this, pos_iff_ne_zero]
    exact fun h => h0 (Measure.measure_univ_eq_zero.1 h)
  rw [maxIrrMeasure_apply P φ hA] at hψ
  exact hpos.ne' hψ

/-- **Proposition 4.2.2 (iii)** for the measure (4.10): if `ψ(A) = 0` then
`ψ{y : L(y, A) > 0} = 0`. -/
theorem maxIrrMeasure_hitSet_null (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    {A : Set X} (hA : MeasurableSet A) (h : maxIrrMeasure P φ A = 0) :
    maxIrrMeasure P φ {y | 0 < hitProb P A y} = 0 := by
  have hA' := measurableSet_hitProb_pos P hA
  rw [maxIrrMeasure_apply P φ hA, lintegral_eq_zero_iff (Kernel.measurable_coe _ hA)] at h
  rw [maxIrrMeasure_apply P φ hA', lintegral_eq_zero_iff (Kernel.measurable_coe _ hA')]
  filter_upwards [h] with y hy
  by_contra hne
  obtain ⟨n, hn⟩ := (resolventHalf_pos_iff P y hA').1 (pos_iff_ne_zero.2 hne)
  rw [setOf_hitProb_pos P hA] at hn
  obtain ⟨m, hm⟩ := exists_measure_pos_of_iUnion hn
  have hK : 0 < resolventHalf P y A :=
    (resolventHalf_pos_iff P y hA).2 ⟨_, (pow_add_pos_iff P n (m + 1) y hA).2 hm⟩
  exact hK.ne' hy

/-- The inequality in the proof of Proposition 4.2.2 (iii) (MT p. 84):
`∫ ψ(dy) Pᵐ(y, A) ≤ 2ᵐ ψ(A)`, i.e. `ψPᵐ ≤ 2ᵐ ψ`. -/
theorem maxIrrMeasure_comp_pow_le (P : Kernel X X) (φ : Measure X) (m : ℕ) {A : Set X}
    (hA : MeasurableSet A) : ((P ^ m) ∘ₘ maxIrrMeasure P φ) A ≤ 2 ^ m * maxIrrMeasure P φ A := by
  rw [measure_kernel_apply _ _ hA, maxIrrMeasure_apply P φ hA, maxIrrMeasure,
    Measure.lintegral_bind (Kernel.aemeasurable _) (Kernel.measurable_coe _ hA).aemeasurable,
    ← lintegral_const_mul _ (Kernel.measurable_coe _ hA)]
  refine lintegral_mono fun y => ?_
  set a : ℕ → ℝ≥0∞ := fun n => (1 - 2⁻¹) * 2⁻¹ ^ n with ha
  have hK : resolventHalf P y = Measure.sum fun n => a n • (P ^ n) y := rfl
  rw [hK, lintegral_sum_measure, Measure.sum_apply _ hA]
  simp_rw [lintegral_smul_measure, Measure.smul_apply, smul_eq_mul]
  have h2 : ∀ n, a n = 2 ^ m * a (n + m) := fun n => by
    simp only [ha, pow_add]
    have : (2 : ℝ≥0∞) ^ m * 2⁻¹ ^ m = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    calc ((1 : ℝ≥0∞) - 2⁻¹) * 2⁻¹ ^ n = (1 - 2⁻¹) * 2⁻¹ ^ n * (2 ^ m * 2⁻¹ ^ m) := by
          rw [this, mul_one]
      _ = _ := by ring
  calc ∑' n, a n * ∫⁻ z, (P ^ m) z A ∂(P ^ n) y
      = ∑' n, 2 ^ m * (a (n + m) * (P ^ (n + m)) y A) := by
        refine tsum_congr fun n => ?_
        rw [← Kernel.pow_add_apply_eq_lintegral P n m y hA, h2 n, mul_assoc]
    _ = 2 ^ m * ∑' n, a (n + m) * (P ^ (n + m)) y A := ENNReal.tsum_mul_left
    _ ≤ 2 ^ m * ∑' k, a k * (P ^ k) y A :=
        mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m)
          (fun k => a k * (P ^ k) y A)) _

/-! ### Maximal irreducibility measures -/

/-- A *maximal irreducibility measure* (MT pp. 83–84): a nonzero irreducibility measure `ψ` such
that every irreducibility measure is absolutely continuous with respect to `ψ`. The chain is
*ψ-irreducible* when `ψ` is such a measure. -/
def IsMaximalIrreducibility (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  ψ ≠ 0 ∧ IsPhiIrreducible P ψ ∧ ∀ φ : Measure X, IsPhiIrreducible P φ → φ ≪ ψ

/-- The measure (4.10) of a nonzero irreducibility measure is maximal. -/
theorem isMaximalIrreducibility_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P]
    {φ : Measure X} (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    IsMaximalIrreducibility P (maxIrrMeasure P φ) := by
  refine ⟨fun h => h0 ?_, isPhiIrreducible_maxIrrMeasure P hφ,
    fun φ' h => ac_maxIrrMeasure P h0 h⟩
  rw [← Measure.measure_univ_eq_zero, ← maxIrrMeasure_univ P φ, h, Measure.coe_zero,
    Pi.zero_apply]

/-- **Proposition 4.2.2 (ii)** for a maximal `ψ`: `φ'` is an irreducibility measure iff
`φ' ≪ ψ`. -/
theorem IsMaximalIrreducibility.isPhiIrreducible_iff {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (φ' : Measure X) :
    IsPhiIrreducible P φ' ↔ φ' ≪ ψ :=
  ⟨hψ.2.2 φ', fun h => hψ.2.1.mono h⟩

/-- Any two maximal irreducibility measures are equivalent (MT p. 84). -/
theorem IsMaximalIrreducibility.equiv {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hψ' : IsMaximalIrreducibility P ψ') :
    ψ ≪ ψ' ∧ ψ' ≪ ψ :=
  ⟨hψ'.2.2 ψ hψ.2.1, hψ.2.2 ψ' hψ'.2.1⟩

/-- A measure equivalent to a maximal irreducibility measure is maximal. -/
theorem IsMaximalIrreducibility.of_equiv {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (h1 : ψ ≪ ψ') (h2 : ψ' ≪ ψ) :
    IsMaximalIrreducibility P ψ' := by
  refine ⟨fun h => hψ.1 ?_, hψ.2.1.mono h2, fun φ hφ => (hψ.2.2 φ hφ).trans h1⟩
  rw [← Measure.measure_univ_eq_zero]
  exact h1 (by rw [h]; rfl)

/-- **Proposition 4.2.2 (iii)** for a maximal `ψ`: if `ψ(A) = 0` then
`ψ{y : L(y, A) > 0} = 0`. -/
theorem IsMaximalIrreducibility.hitSet_null {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A)
    (h : ψ A = 0) : ψ {y | 0 < hitProb P A y} = 0 := by
  have hψ₁ := isMaximalIrreducibility_maxIrrMeasure P hψ.2.1 hψ.1
  obtain ⟨h1, h2⟩ := hψ.equiv hψ₁
  exact h1 (maxIrrMeasure_hitSet_null P ψ hA (h2 h))

/-- **Proposition 4.2.2** (MT p. 83). If the chain is `φ`-irreducible for a nonzero measure `φ`,
there is a probability measure `ψ` such that (i) the chain is `ψ`-irreducible; (ii) the chain is
`φ'`-irreducible iff `φ' ≪ ψ`; (iii) `ψ(A) = 0` implies `ψ{y : L(y, A) > 0} = 0`; (iv) `ψ` is
equivalent to `ψ'(A) = ∫ φ'(dy) K_{a_{1/2}}(y, A)` for every nonzero irreducibility measure
`φ'`. -/
theorem proposition_4_2_2 (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ ψ : Measure X, IsProbabilityMeasure ψ ∧ IsPhiIrreducible P ψ ∧
      (∀ φ' : Measure X, IsPhiIrreducible P φ' ↔ φ' ≪ ψ) ∧
      (∀ A, MeasurableSet A → ψ A = 0 → ψ {y | 0 < hitProb P A y} = 0) ∧
      (∀ φ' : Measure X, IsPhiIrreducible P φ' → φ' ≠ 0 →
        maxIrrMeasure P φ' ≪ ψ ∧ ψ ≪ maxIrrMeasure P φ') := by
  obtain ⟨φ₀, hφ₀, h1, h2⟩ := exists_prob_equiv P hφ h0
  have hφ₀0 : φ₀ ≠ 0 := IsProbabilityMeasure.ne_zero φ₀
  have hmax := isMaximalIrreducibility_maxIrrMeasure P (hφ.mono h1) hφ₀0
  refine ⟨maxIrrMeasure P φ₀, isProbabilityMeasure_maxIrrMeasure P φ₀, hmax.2.1,
    hmax.isPhiIrreducible_iff, fun A hA h => hmax.hitSet_null hA h, fun φ' hφ' h0' => ?_⟩
  exact hmax.equiv (isMaximalIrreducibility_maxIrrMeasure P hφ' h0') |>.symm

/-- The measure of Proposition 4.2.2 is the construction (4.10) applied to a probability measure
`φ₀` equivalent to `φ`, and it is a maximal irreducibility measure. -/
theorem proposition_4_2_2_maximal (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ φ₀ : Measure X, IsProbabilityMeasure φ₀ ∧ φ₀ ≪ φ ∧ φ ≪ φ₀ ∧
      IsMaximalIrreducibility P (maxIrrMeasure P φ₀) := by
  obtain ⟨φ₀, hφ₀, h1, h2⟩ := exists_prob_equiv P hφ h0
  exact ⟨φ₀, hφ₀, h1, h2,
    isMaximalIrreducibility_maxIrrMeasure P (hφ.mono h1) (IsProbabilityMeasure.ne_zero φ₀)⟩

/-- **Correction to Proposition 4.2.2.** The hypothesis `φ ≠ 0` is needed: the identity chain on
`Bool` is `0`-irreducible, but it is `ψ`-irreducible for no probability measure `ψ`. -/
theorem proposition_4_2_2_zero_counterexample :
    IsPhiIrreducible (Kernel.id : Kernel Bool Bool) 0 ∧
      ¬ ∃ ψ : Measure Bool, IsProbabilityMeasure ψ ∧ IsPhiIrreducible Kernel.id ψ := by
  refine ⟨isPhiIrreducible_zero _, ?_⟩
  rintro ⟨ψ, hψ, hirr⟩
  have hAbs : ∀ b : Bool, IsAbsorbing (Kernel.id : Kernel Bool Bool) {b} := fun b x hx => by
    rw [Kernel.id_apply, Measure.dirac_apply_of_mem hx]
  have hb : ∀ b : Bool, ψ {b}ᶜ = 0 := fun b => by
    by_contra h
    have := hirr {b}ᶜ (measurableSet_singleton b).compl (pos_iff_ne_zero.2 h) b
    rw [(hAbs b).hitProb_compl (measurableSet_singleton b) (mem_singleton b)] at this
    exact lt_irrefl _ this
  have hu : (univ : Set Bool) = {true}ᶜ ∪ {false}ᶜ := by
    ext b
    cases b <;> simp
  have : ψ univ = 0 := by rw [hu]; exact measure_union_null (hb true) (hb false)
  rw [measure_univ] at this
  exact one_ne_zero this

/-! ### Full and absorbing sets -/

/-- `B⁺(X) = {A ∈ B(X) : ψ(A) > 0}` (MT p. 84). -/
def posSets (ψ : Measure X) : Set (Set X) := {A | MeasurableSet A ∧ 0 < ψ A}

/-- `B⁺(X)` does not depend on the choice of maximal irreducibility measure (MT p. 84). -/
theorem posSets_eq_of_maximal {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hψ' : IsMaximalIrreducibility P ψ') :
    posSets ψ = posSets ψ' := by
  obtain ⟨h1, h2⟩ := hψ.equiv hψ'
  ext A
  simp only [posSets, mem_ofPred_eq, pos_iff_ne_zero]
  exact and_congr_right fun _ => ⟨fun h h' => h (h1 h'), fun h h' => h (h2 h')⟩

/-- A set `A` is *full* if `ψ(Aᶜ) = 0` (MT p. 84). -/
def IsFull (ψ : Measure X) (A : Set X) : Prop := ψ Aᶜ = 0

/-- **Proposition 4.2.3 (i)** (MT p. 84): a non-empty absorbing set is full, for every
irreducibility measure. -/
theorem proposition_4_2_3_i {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {A : Set X} (hA : MeasurableSet A) (hne : A.Nonempty)
    (hAbs : IsAbsorbing P A) : IsFull φ A := by
  by_contra h
  obtain ⟨x, hx⟩ := hne
  have := hφ Aᶜ hA.compl (pos_iff_ne_zero.2 h) x
  rw [hAbs.hitProb_compl hA hx] at this
  exact lt_irrefl _ this

/-- **Correction to Proposition 4.2.3 (i).** The empty set is absorbing, but it is full for no
nonzero measure. -/
theorem proposition_4_2_3_i_counterexample (P : Kernel X X) {ψ : Measure X} (hψ : ψ ≠ 0) :
    IsAbsorbing P ∅ ∧ ¬ IsFull ψ ∅ := by
  refine ⟨fun x hx => absurd hx (notMem_empty x), fun h => hψ ?_⟩
  rw [IsFull, compl_empty] at h
  exact Measure.measure_univ_eq_zero.1 h

/-- **Proposition 4.2.3 (ii)** (MT p. 84): for a maximal irreducibility measure `ψ`, every full
set `A` contains a non-empty absorbing set, namely
`B = {y : Σ_{n ≥ 0} Pⁿ(y, Aᶜ) = 0} = {y : K_{a_{1/2}}(y, Aᶜ) = 0}`; `B` is also full. -/
theorem proposition_4_2_3_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hfull : IsFull ψ A) :
    ∃ B ⊆ A, B.Nonempty ∧ MeasurableSet B ∧ IsAbsorbing P B ∧ IsFull ψ B := by
  set B := {y | resolventHalf P y Aᶜ = 0} with hBdef
  have hAc := hA.compl
  have hBm : MeasurableSet B :=
    (Kernel.measurable_coe _ hAc) (measurableSet_singleton 0)
  have hBc : Bᶜ = {y | 0 < resolventHalf P y Aᶜ} := by
    ext y
    simp [hBdef, pos_iff_ne_zero]
  have hBA : B ⊆ A := fun y hy => by
    by_contra hyA
    have : 0 < resolventHalf P y Aᶜ := (resolventHalf_pos_iff P y hAc).2
      ⟨0, by rw [pow_zero_apply, Measure.dirac_apply_of_mem hyA]; exact one_pos⟩
    exact this.ne' hy
  have hBfull : IsFull ψ B := by
    have hsub : Bᶜ ⊆ Aᶜ ∪ {y | 0 < hitProb P Aᶜ y} := fun y hy => by
      rw [hBc] at hy
      obtain ⟨n, hn⟩ := (resolventHalf_pos_iff P y hAc).1 hy
      rcases n with _ | n
      · left
        rw [pow_zero_apply, Measure.dirac_apply' _ hAc] at hn
        by_contra hc
        rw [indicator_of_notMem hc] at hn
        exact lt_irrefl _ hn
      · exact Or.inr ((hitProb_pos_iff P hAc y).2 ⟨n, hn⟩)
    exact measure_mono_null hsub (measure_union_null hfull (hψ.hitSet_null hAc hfull))
  refine ⟨B, hBA, ?_, hBm, ?_, hBfull⟩
  · by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    rw [IsFull, hc, compl_empty] at hBfull
    exact hψ.1 (Measure.measure_univ_eq_zero.1 hBfull)
  · intro y hy
    rw [← prob_compl_eq_zero_iff hBm]
    by_contra hc
    rw [hBc, setOf_resolventHalf_pos P hAc] at hc
    obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion (pos_iff_ne_zero.2 hc)
    have h1 : 0 < (P ^ (1 + n)) y Aᶜ := (pow_add_pos_iff P 1 n y hAc).2 (by rwa [pow_one])
    exact ((resolventHalf_pos_iff P y hAc).2 ⟨_, h1⟩).ne' hy

/-- **Theorem 4.0.1** (MT p. 75). If the chain is `φ`-irreducible for a nonzero `φ`, there is a
maximal irreducibility probability measure `ψ`, with `φ ≪ ψ`, such that (i) `ψ(A) > 0` implies
`L(x, A) > 0` for every `x`; (ii) `ψ(A) = 0` implies `ψ(Ā) = 0`, `Ā = {y : L(y, A) > 0}`;
(iii) if `ψ(Aᶜ) = 0` then `A = A₀ ∪ N` with `A₀` absorbing and `ψ(N) = 0`. -/
theorem theorem_4_0_1 (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ ψ : Measure X, IsMaximalIrreducibility P ψ ∧ IsProbabilityMeasure ψ ∧ φ ≪ ψ ∧
      (∀ A, MeasurableSet A → 0 < ψ A → ∀ x, 0 < hitProb P A x) ∧
      (∀ A, MeasurableSet A → ψ A = 0 → ψ {y | 0 < hitProb P A y} = 0) ∧
      (∀ A, MeasurableSet A → ψ Aᶜ = 0 →
        ∃ A₀ N : Set X, A = A₀ ∪ N ∧ MeasurableSet A₀ ∧ IsAbsorbing P A₀ ∧ ψ N = 0) := by
  obtain ⟨φ₀, hφ₀, h1, h2, hmax⟩ := proposition_4_2_2_maximal P hφ h0
  refine ⟨maxIrrMeasure P φ₀, hmax, isProbabilityMeasure_maxIrrMeasure P φ₀, hmax.2.2 φ hφ,
    hmax.2.1, fun A hA h => hmax.hitSet_null hA h, fun A hA hfull => ?_⟩
  obtain ⟨B, hBA, -, hBm, hBabs, hBfull⟩ := proposition_4_2_3_ii hmax hA hfull
  refine ⟨B, A \ B, (union_sdiff_cancel hBA).symm, hBm, hBabs,
    measure_mono_null (fun y hy => hy.2) hBfull⟩

/-- **Theorem 4.0.1**, uniqueness: the maximal irreducibility measure is essentially unique. -/
theorem theorem_4_0_1_unique {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hψ' : IsMaximalIrreducibility P ψ') :
    ψ ≪ ψ' ∧ ψ' ≪ ψ :=
  hψ.equiv hψ'

/-! ### Restriction to an absorbing set -/

/-- An *absorbing ψ-irreducible set* (MT p. 85): `C` is absorbing and `ψ(B) > 0` implies
`L(x, B) > 0` for every `x ∈ C`. -/
def IsAbsorbingIrreducibleSet (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (C : Set X) :
    Prop :=
  IsAbsorbing P C ∧ ∀ B, MeasurableSet B → 0 < ψ B → ∀ x ∈ C, 0 < hitProb P B x

/-- **Proposition 4.2.4** (MT p. 85). The kernel `P_A` restricted to an absorbing set `A` is a
transition kernel on `A` (so the chain `Φ_A` exists, Theorem 3.4.1), and if the chain is
`φ`-irreducible then `Φ_A` is irreducible for the restriction of `φ` to `A`. -/
theorem proposition_4_2_4 (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) :
    ∃ _ : IsMarkovKernel (restrictKernel P hA), ∀ φ : Measure X, IsPhiIrreducible P φ →
      IsPhiIrreducible (restrictKernel P hA) (φ.comap Subtype.val) := by
  have hM := isMarkovKernel_restrictKernel P hA hAbs
  refine ⟨hM, fun φ hφ B hB hpos x => ?_⟩
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
  rw [comap_subtype_coe_apply hA] at hpos
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hB' x).1 (hφ _ hB' hpos x)
  refine (hitProb_pos_iff _ hB x).2 ⟨n, ?_⟩
  rwa [restrictKernel_pow_apply P hA hAbs (n + 1) x hB]

/-- For a maximal `ψ` and a non-empty absorbing `A`, the restriction of `ψ` to `A` is nonzero,
so Proposition 4.2.4 gives a nontrivial irreducibility measure for `Φ_A`; `A` is an absorbing
`ψ`-irreducible set. -/
theorem proposition_4_2_4_nonzero {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hne : A.Nonempty)
    (hAbs : IsAbsorbing P A) :
    ψ.comap (Subtype.val : A → X) ≠ 0 ∧ IsAbsorbingIrreducibleSet P ψ A := by
  refine ⟨fun h => hψ.1 ?_, hAbs, fun B hB hpos x _ => hψ.2.1 B hB hpos x⟩
  have hfull := proposition_4_2_3_i hψ.2.1 hA hne hAbs
  have hAψ : ψ A = 0 := by
    have := congrArg (fun μ : Measure A => μ univ) h
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rwa [comap_subtype_coe_apply hA, image_univ, Subtype.range_coe] at this
  rw [← Measure.measure_univ_eq_zero, ← union_compl_self A]
  exact measure_union_null hAψ hfull

/-- MT p. 83: for an irreducible chain on a countable space, counting measure is a maximal
irreducibility measure. -/
theorem isMaximalIrreducibility_count [MeasurableSingletonClass X] [Countable X] [Nonempty X]
    (P : Kernel X X) [IsMarkovKernel P] (h : IsIrreducibleChain P) :
    IsMaximalIrreducibility P Measure.count := by
  refine ⟨fun h0 => ?_, (isIrreducibleChain_iff_count P).1 h, fun φ _ => ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty X›
    have := congrArg (fun μ : Measure X => μ {x}) h0
    simp at this
  · exact Measure.AbsolutelyContinuous.mk fun A _ hA => by
      rw [Measure.count_eq_zero_iff.1 hA, measure_empty]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Accessibility and uniform accessibility (MT §4.2.3)

Meyn and Tweedie, §4.2.3, pp. 85–87.

* `IsAccessibleFrom P A B` (p. 86): `L(x, B) > 0` for every `x ∈ A`.
* `UnifAccessible P A B`, written `A ⇝ B` (4.11), p. 86: `inf_{x ∈ A} L(x, B) ≥ δ > 0`.
* `hitProb_ge_mul`: `L(x, C) ≥ L(x, B) · inf_{y ∈ B} L(y, C)`, from the strong Markov property at
  the first return time to `B`; **Lemma 4.2.5** (`lemma_4_2_5`, p. 86): `⇝` is transitive.
* `hitSet P A = Ā`, `hitSetLevel P A m = Ā(m) = {x : Σ_{n=1}^m Pⁿ(x, A) ≥ m⁻¹}` and
  `noHitSet P A = A⁰ = [Ā]ᶜ` (p. 86).
* **Lemma 4.2.6** (`lemma_4_2_6`, p. 86): `Ā = ⋃ₘ Ā(m)` and `Ā(m) ⇝ A`; `lemma_4_2_6_bound`:
  `L(x, A) ≥ P_x(τ_A ≤ m) ≥ m⁻²` on `Ā(m)`.
* `countable_cover_unifAccessible` (p. 87): for a `φ`-irreducible chain and `φ(A) > 0`, the sets
  `Ā(m)` are a countable cover of `X`, from each of which `A` is uniformly accessible.

The book proves Lemma 4.2.5 with the taboo potential `U_B` of (3.34); the proof here uses the
strong Markov property (Proposition 3.4.6) at `τ_B`, which is the same decomposition.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- `B` is *accessible* from `A` (MT p. 86): `L(x, B) > 0` for every `x ∈ A`. -/
def IsAccessibleFrom (P : Kernel X X) [IsMarkovKernel P] (A B : Set X) : Prop :=
  ∀ x ∈ A, 0 < hitProb P B x

/-- `B` is *uniformly accessible* from `A`, `A ⇝ B` (4.11), MT p. 86: there is `δ > 0` with
`L(x, B) ≥ δ` for every `x ∈ A`. -/
def UnifAccessible (P : Kernel X X) [IsMarkovKernel P] (A B : Set X) : Prop :=
  ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ A, δ ≤ hitProb P B x

/-- Uniform accessibility implies accessibility. -/
theorem UnifAccessible.isAccessibleFrom {P : Kernel X X} [IsMarkovKernel P] {A B : Set X}
    (h : UnifAccessible P A B) : IsAccessibleFrom P A B := by
  obtain ⟨δ, hδ, h⟩ := h
  exact fun x hx => hδ.trans_le (h x hx)

omit [MeasurableSpace X] in
/-- On `{τ_B < ∞}`, `Φ_{τ_B} ∈ B`. -/
theorem stoppedState_firstReturn_mem (B : Set X) {ω : ℕ → X} (hω : firstReturn B ω ≠ ⊤) :
    stoppedState (firstReturn B) ω ∈ B :=
  hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := B) (n := 1) hω

/-- **First passage through `B`.** If `L(y, C) ≥ δ` for every `y ∈ B`, then
`L(x, C) ≥ δ L(x, B)`: by the strong Markov property at `τ_B`,
`L(x, C) ≥ P_x(τ_B < ∞, θ^{τ_B}Φ enters C) = E_x[L(Φ_{τ_B}, C); τ_B < ∞]`. -/
theorem hitProb_ge_mul (P : Kernel X X) [IsMarkovKernel P] {B C : Set X}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {δ : ℝ≥0∞}
    (hδ : ∀ y ∈ B, δ ≤ hitProb P C y) (x : X) : δ * hitProb P B x ≤ hitProb P C x := by
  have hτ := (proposition_3_4_4 hB).1
  set S : Set (ℕ → X) := {ω | firstReturn C ω ≠ ⊤} with hS
  have hSm : MeasurableSet S := measurableSet_firstReturn_ne_top hC
  have hT : MeasurableSet {ω : ℕ → X | firstReturn B ω ≠ ⊤} :=
    measurableSet_firstReturn_ne_top hB
  have hH : Measurable (S.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hSm
  have hsm := strong_markov_lintegral P (Measure.dirac x) hτ MeasurableSet.univ hH
  rw [pathMeasure_dirac] at hsm
  simp only [univ_inter] at hsm
  simp_rw [lintegral_indicator_one hSm] at hsm
  calc δ * hitProb P B x
      = ∫⁻ _ in {ω | firstReturn B ω ≠ ⊤}, δ ∂pathKernel P x := by
        rw [setLIntegral_const]
        rfl
    _ ≤ ∫⁻ ω in {ω | firstReturn B ω ≠ ⊤},
          pathKernel P (stoppedState (firstReturn B) ω) S ∂pathKernel P x :=
        setLIntegral_mono ((measurable_hitProb P hC).comp (measurable_stoppedState hτ))
          fun ω hω => hδ _ (stoppedState_firstReturn_mem B hω)
    _ = ∫⁻ ω in {ω | firstReturn B ω ≠ ⊤},
          S.indicator 1 (shiftAt (firstReturn B) ω) ∂pathKernel P x := hsm.symm
    _ ≤ ∫⁻ ω in {ω | firstReturn B ω ≠ ⊤}, S.indicator 1 ω ∂pathKernel P x := by
        refine setLIntegral_mono' hT fun ω hω => ?_
        by_cases h : shiftAt (firstReturn B) ω ∈ S
        · rw [indicator_of_mem h]
          obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (show firstReturn B ω ≠ ⊤ from hω)
          rw [shiftAt_of_eq hk.symm] at h
          obtain ⟨n, hn, hnC⟩ := (firstReturn_ne_top_iff C _).1 h
          have hmem : ω ∈ S := (firstReturn_ne_top_iff C ω).2 ⟨k + n, by omega, hnC⟩
          rw [indicator_of_mem hmem]
          exact le_rfl
        · rw [indicator_of_notMem h]
          exact zero_le
    _ ≤ ∫⁻ ω, S.indicator 1 ω ∂pathKernel P x := setLIntegral_le_lintegral _ _
    _ = hitProb P C x := lintegral_indicator_one hSm

/-- **Lemma 4.2.5** (MT p. 86): if `A ⇝ B` and `B ⇝ C`, then `A ⇝ C`. -/
theorem lemma_4_2_5 {P : Kernel X X} [IsMarkovKernel P] {A B C : Set X}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hAB : UnifAccessible P A B)
    (hBC : UnifAccessible P B C) : UnifAccessible P A C := by
  obtain ⟨δ₁, h₁, hA⟩ := hAB
  obtain ⟨δ₂, h₂, hB'⟩ := hBC
  refine ⟨δ₂ * δ₁, ENNReal.mul_pos h₂.ne' h₁.ne', fun x hx => ?_⟩
  calc δ₂ * δ₁ ≤ δ₂ * hitProb P B x := by gcongr; exact hA x hx
    _ ≤ hitProb P C x := hitProb_ge_mul P hB hC hB' x

/-! ### The sets `Ā`, `Ā(m)` and `A⁰` -/

/-- `Ā = {x : L(x, A) > 0}`, the set from which `A` is accessible (MT p. 86). -/
def hitSet (P : Kernel X X) [IsMarkovKernel P] (A : Set X) : Set X := {x | 0 < hitProb P A x}

/-- `Ā(m) = {x : Σ_{n=1}^m Pⁿ(x, A) ≥ m⁻¹}` (MT p. 86). -/
def hitSetLevel (P : Kernel X X) (A : Set X) (m : ℕ) : Set X :=
  {x | (m : ℝ≥0∞)⁻¹ ≤ ∑ n ∈ Finset.range m, (P ^ (n + 1)) x A}

/-- `A⁰ = {x : L(x, A) = 0}`, the set from which `A` is not accessible (MT p. 86). -/
def noHitSet (P : Kernel X X) [IsMarkovKernel P] (A : Set X) : Set X := {x | hitProb P A x = 0}

/-- `A⁰ = [Ā]ᶜ` (MT p. 86). -/
theorem noHitSet_eq_compl (P : Kernel X X) [IsMarkovKernel P] (A : Set X) :
    noHitSet P A = (hitSet P A)ᶜ := by
  ext x
  simp [noHitSet, hitSet, pos_iff_ne_zero]

/-- `Ā(m)` is measurable. -/
theorem measurableSet_hitSetLevel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (m : ℕ) :
    MeasurableSet (hitSetLevel P A m) :=
  measurableSet_le measurable_const
    (Finset.measurable_sum _ fun _ _ => Kernel.measurable_coe _ hA)

/-- The bound in the proof of Lemma 4.2.6 (MT p. 87): on `Ā(m)`,
`L(x, A) ≥ P_x(τ_A ≤ m) ≥ m⁻²`. -/
theorem lemma_4_2_6_bound (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {m : ℕ} {x : X} (hx : x ∈ hitSetLevel P A m) :
    (m : ℝ≥0∞)⁻¹ ^ 2 ≤ pathKernel P x {ω | firstReturn A ω ≤ WithTop.some m} ∧
      pathKernel P x {ω | firstReturn A ω ≤ WithTop.some m} ≤ hitProb P A x := by
  refine ⟨?_, measure_mono fun ω hω => ne_top_of_le_ne_top WithTop.coe_ne_top hω⟩
  have hm : m ≠ 0 := by
    rintro rfl
    simp [hitSetLevel] at hx
  have hle : ∀ n < m, (P ^ (n + 1)) x A ≤ pathKernel P x {ω | firstReturn A ω ≤ WithTop.some m} :=
    fun n hn => by
      rw [← pathKernel_coord_mem P x _ hA]
      refine measure_mono fun ω hω => ?_
      have := hittingAfter_le_of_mem (u := fun n (ω : ℕ → X) => ω n) (s := A) (n := 1)
        (i := n + 1) (by omega) hω
      exact this.trans (WithTop.coe_le_coe.2 (by omega))
  by_contra hc
  push Not at hc
  have hlt : ∑ n ∈ Finset.range m, (P ^ (n + 1)) x A <
      ∑ _n ∈ Finset.range m, (m : ℝ≥0∞)⁻¹ ^ 2 :=
    ENNReal.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hm) fun n hn =>
      (hle n (Finset.mem_range.1 hn)).trans_lt hc
  have hsum : ∑ _n ∈ Finset.range m, (m : ℝ≥0∞)⁻¹ ^ 2 = (m : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hm) (ENNReal.natCast_ne_top m), one_mul]
  rw [hsum] at hlt
  exact absurd hx (not_le.2 hlt)

/-- **Lemma 4.2.6** (MT p. 86): `Ā = ⋃ₘ Ā(m)`, and `Ā(m) ⇝ A` for each `m`. -/
theorem lemma_4_2_6 (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) :
    hitSet P A = ⋃ m, hitSetLevel P A m ∧ ∀ m, UnifAccessible P (hitSetLevel P A m) A := by
  refine ⟨?_, fun m => ⟨(m : ℝ≥0∞)⁻¹ ^ 2, ?_, fun x hx =>
    (lemma_4_2_6_bound P hA hx).1.trans (lemma_4_2_6_bound P hA hx).2⟩⟩
  · ext x
    simp only [hitSet, mem_ofPred_eq, mem_iUnion, hitSetLevel]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA x).1 h
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hn.ne'
      refine ⟨max (n + 1) k, ?_⟩
      calc ((max (n + 1) k : ℕ) : ℝ≥0∞)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.2 (Nat.cast_le.2 (le_max_right _ _))
        _ ≤ (P ^ (n + 1)) x A := hk.le
        _ ≤ ∑ j ∈ Finset.range (max (n + 1) k), (P ^ (j + 1)) x A :=
            Finset.single_le_sum (f := fun j => (P ^ (j + 1)) x A) (fun _ _ => zero_le)
              (Finset.mem_range.2 (by omega))
    · rintro ⟨m, hm⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
      have hpos : 0 < ∑ j ∈ Finset.range m, (P ^ (j + 1)) x A :=
        (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m)).trans_le hm
      obtain ⟨j, -, hj⟩ := Finset.sum_pos_iff.1 hpos
      exact (hitProb_pos_iff P hA x).2 ⟨j, hj⟩
  · exact ENNReal.pow_pos (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m)) 2

/-- MT p. 87: if the chain is `φ`-irreducible and `φ(A) > 0`, then `Ā = X`, so the sets `Ā(m)`
form a countable cover of `X` from each of which `A` is uniformly accessible. -/
theorem countable_cover_unifAccessible {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {A : Set X} (hA : MeasurableSet A) (hpos : 0 < φ A) :
    ⋃ m, hitSetLevel P A m = univ ∧ ∀ m, UnifAccessible P (hitSetLevel P A m) A := by
  refine ⟨?_, (lemma_4_2_6 P hA).2⟩
  rw [← (lemma_4_2_6 P hA).1]
  exact eq_univ_of_forall fun x => hφ A hA hpos x

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Atoms (MT Chapter 5 introduction and §5.1)

Meyn and Tweedie, pp. 96–98.

* `IsAtom P α` (p. 96): `α` is measurable and `P(x, ·)` is the same measure `ν` for every
  `x ∈ α`; `isAtom_singleton`: a single point is an atom.
* `IsAccessibleAtom P ψ α` (p. 96): an atom with `ψ(α) > 0` for a maximal irreducibility
  measure `ψ`; `IsMaximalIrreducibility.pos_iff_hitProb_pos`: for maximal `ψ`, `ψ(α) > 0` iff
  `L(x, α) > 0` for every `x`, so accessibility does not depend on the choice of `ψ`.
* `exists_pow_comp_pos`: from any nonzero initial law, a `φ`-irreducible chain reaches a set of
  positive `φ`-measure with positive probability: `ρPᵐ⁺¹(B) > 0` for some `m`.
* `hitProb_pos_of_exists_pow`: if every state reaches `α` (time `0` allowed), then
  `L(x, α) > 0` for every `x`.
* `pow_succ_ge_of_atom`: the bound `Pⁿ⁺¹(x, A) ≥ Pⁿ(x, α) ν(A)` of the proof of Proposition 5.1.1.
* **Proposition 5.1.1** (`proposition_5_1_1`, p. 97): if `Σₙ Pⁿ(x, α) > 0` for every `x`, then the
  chain is `ν`-irreducible with `ν = P(α, ·)`, `L(x, α) > 0` for every `x`, and `α` is an
  accessible atom for every maximal irreducibility measure.
* `hitProb_atom_eq`: `L(·, A)` is constant on an atom; **Proposition 5.1.2**
  (`proposition_5_1_2`, p. 98): if `L(x, A) > 0` for some `x ∈ α`, then `α ⇝ A`.

**Corrections.** None. In Proposition 5.1.1 the sum may include `n = 0`: the conclusion
`L(x, α) > 0` holds also for `x ∈ α`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- An *atom* (MT p. 96): a measurable set `α` such that `P(x, ·) = ν` for every `x ∈ α`, for
one measure `ν`. -/
def IsAtom (P : Kernel X X) (α : Set X) : Prop :=
  MeasurableSet α ∧ ∃ ν : Measure X, ∀ x ∈ α, P x = ν

/-- A single point is an atom (MT p. 96), when points are measurable. -/
theorem isAtom_singleton [MeasurableSingletonClass X] (P : Kernel X X) (x : X) :
    IsAtom P {x} :=
  ⟨measurableSet_singleton x, P x, fun y hy => by rw [mem_singleton_iff.1 hy]⟩

/-- An *accessible atom* (MT p. 96): an atom `α` with `ψ(α) > 0`, where `ψ` is a maximal
irreducibility measure. -/
def IsAccessibleAtom (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (α : Set X) : Prop :=
  IsAtom P α ∧ IsMaximalIrreducibility P ψ ∧ 0 < ψ α

/-- For a maximal irreducibility measure `ψ`, `ψ(A) > 0` iff `L(x, A) > 0` for every `x`. -/
theorem IsMaximalIrreducibility.pos_iff_hitProb_pos {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) :
    0 < ψ A ↔ ∀ x, 0 < hitProb P A x := by
  refine ⟨fun h => hψ.2.1 A hA h, fun h => ?_⟩
  rw [pos_iff_ne_zero]
  intro h0
  have := hψ.hitSet_null hA h0
  have hu : {y | 0 < hitProb P A y} = univ := eq_univ_of_forall h
  rw [hu, Measure.measure_univ_eq_zero] at this
  exact hψ.1 this

/-- The bound in the proof of Proposition 5.1.1 (MT p. 97): if `P(y, ·) = ν` on `α`, then
`Pⁿ⁺¹(x, A) ≥ ∫_α Pⁿ(x, dy) P(y, A) = Pⁿ(x, α) ν(A)`. -/
theorem pow_succ_ge_of_atom (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) {ν : Measure X}
    (hν : ∀ y ∈ α, P y = ν) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (P ^ n) x α * ν A ≤ (P ^ (n + 1)) x A := by
  rw [pow_succ_apply' P n x hA]
  calc (P ^ n) x α * ν A = ∫⁻ y in α, P y A ∂(P ^ n) x := by
        rw [setLIntegral_congr_fun hα (fun y hy => by rw [hν y hy]), setLIntegral_const,
          mul_comm]
    _ ≤ ∫⁻ y, P y A ∂(P ^ n) x := setLIntegral_le_lintegral _ _

/-- If the chain is `φ`-irreducible, then from any nonzero initial law `ρ` it reaches a set of
positive `φ`-measure: `ρPᵐ⁺¹(B) > 0` for some `m`. -/
theorem exists_pow_comp_pos {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {ρ : Measure X} (hρ : ρ ≠ 0) {B : Set X} (hB : MeasurableSet B)
    (hpos : 0 < φ B) :
    ∃ m, 0 < ((P ^ (m + 1) : Kernel X X) ∘ₘ ρ) B := by
  by_contra hc
  push Not at hc
  have hz : ∀ m, ∀ᵐ y ∂ρ, (P ^ (m + 1)) y B = 0 := fun m => by
    have := nonpos_iff_eq_zero.1 (hc m)
    rw [measure_kernel_apply ρ _ hB, lintegral_eq_zero_iff (Kernel.measurable_coe _ hB)] at this
    exact this
  rw [← ae_all_iff] at hz
  have : ∀ᵐ y ∂ρ, False := hz.mono fun y hy => by
    obtain ⟨m, hm⟩ := (hitProb_pos_iff P hB y).1 (hφ B hB hpos y)
    exact (hm.ne' (hy m)).elim
  exact hρ (ae_eq_bot.1 (by simpa using this))

/-- If every state reaches `α` (with `n = 0` allowed), then every state enters `α` at some time
`n ≥ 1`: `L(x, α) > 0` for every `x`. -/
theorem hitProb_pos_of_exists_pow (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (h : ∀ x, ∃ n, 0 < (P ^ n) x α) (x : X) : 0 < hitProb P α x := by
  refine hitProb_pos_of_compl P hα (fun y hy => ?_) x
  obtain ⟨n, hn⟩ := h y
  rcases n with _ | n
  · rw [pow_zero_apply, Measure.dirac_apply' _ hα, indicator_of_notMem hy] at hn
    exact absurd hn (lt_irrefl _)
  · exact (hitProb_pos_iff P hα y).2 ⟨n, hn⟩

/-- **Proposition 5.1.1** (MT p. 97). Let `α` be an atom, `P(x, ·) = ν` for `x ∈ α`, and suppose
`Σₙ Pⁿ(x, α) > 0` for every `x`. Then the chain is `ν`-irreducible, `L(x, α) > 0` for every `x`,
and `α` is an accessible atom: `ψ(α) > 0` for every maximal irreducibility measure `ψ`. -/
theorem proposition_5_1_1 (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : MeasurableSet α)
    {ν : Measure X} (hν : ∀ y ∈ α, P y = ν) (h : ∀ x, ∃ n, 0 < (P ^ n) x α) :
    IsPhiIrreducible P ν ∧ (∀ x, 0 < hitProb P α x) ∧
      ∀ ψ : Measure X, IsMaximalIrreducibility P ψ → IsAccessibleAtom P ψ α := by
  have hL := hitProb_pos_of_exists_pow P hα h
  refine ⟨fun A hA hpos x => ?_, hL, fun ψ hψ =>
    ⟨⟨hα, ν, hν⟩, hψ, (hψ.pos_iff_hitProb_pos hα).2 hL⟩⟩
  obtain ⟨n, hn⟩ := h x
  exact (ENNReal.mul_pos hn.ne' hpos.ne').trans_le
    ((pow_succ_ge_of_atom P hα hν n x hA).trans (pow_le_hitProb P hA n x))

/-- `L(·, A)` is constant on an atom: by the first-step equation,
`L(y, A) = ν(A) + ∫_{Aᶜ} ν(dz) L(z, A)` for every `y ∈ α`. -/
theorem hitProb_atom_eq (P : Kernel X X) [IsMarkovKernel P] {α : Set X} {ν : Measure X}
    (hν : ∀ y ∈ α, P y = ν) {A : Set X} (hA : MeasurableSet A) {x y : X} (hx : x ∈ α)
    (hy : y ∈ α) : hitProb P A y = hitProb P A x := by
  rw [hitProb_first_step P hA x, hitProb_first_step P hA y, hν x hx, hν y hy]

/-- **Proposition 5.1.2** (MT p. 98). If `α` is an atom and `L(x, A) > 0` for some `x ∈ α`, then
`α ⇝ A`: `L(y, A) = L(x, A)` for every `y ∈ α`. -/
theorem proposition_5_1_2 (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {A : Set X} (hA : MeasurableSet A) {x : X} (hx : x ∈ α) (hpos : 0 < hitProb P A x) :
    UnifAccessible P α A := by
  obtain ⟨-, ν, hν⟩ := hα
  exact ⟨hitProb P A x, hpos, fun y hy => (hitProb_atom_eq P hν hA hx hy).ge⟩

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Specific transition matrices (MT §3.3)

Meyn and Tweedie, §3.3, pp. 54–59. Each matrix is shown to be a Markov transition matrix
(3.6), so Theorem 3.2.1 (`theorem_3_2_1`, with `isMarkovKernel_matKernel`) builds the chain.

* §3.3.1, `fwdRecMatrix`: the forward recurrence time chain `V⁺` (p. 54), with state `k`
  standing for `V⁺ = k + 1`; `isTransitionMatrix_fwdRecMatrix`.
* §3.3.1, `ptail` (3.9) and `bwdRecMatrix` (3.10): the backward recurrence time chain `V⁻`
  (p. 55); `bwdRecMatrix_rowSum` (rows sum to one on `{x : p̄(x) ≠ 0}`),
  `ptail_ne_zero_of_bwdRecMatrix` (this set is closed, so it is the state space), and
  `ptail_ne_zero_iff` (it is `{0, …, M − 1}`, `M = sup{m : p(m) > 0}`).
* §3.3.2, `rwMatrix` (3.11): the random walk on `ℤ`, `P(x, y) = Γ(y − x)`;
  `isTransitionMatrix_rwMatrix`, `rwMatrix_translate` (translation invariance), `rw_step_law`.
* §3.3.2, `rwhlMatrix` (3.13)–(3.14): the random walk on the half line `ℤ₊`,
  `P(x, y) = Γ(y − x)` for `y > 0` and `P(x, 0) = Γ(−∞, −x]`; `isTransitionMatrix_rwhlMatrix`.
* §3.3.2, `storage_increment_singleton`: the increment law of the simple storage model,
  `P(S − J = x) = Σᵢ H(i) G(i − x)`; see the correction below.
* §3.3.3, `poissonWeight` (3.14)–(3.15), (3.19): `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)`, with
  `tsum_poissonWeight` (`Σⱼ pⱼ = 1`).
* **Proposition 3.3.1** (`proposition_3_3_1`, p. 56): the GI/M/1 matrix `giM1Matrix` is a
  transition matrix, and it is the random walk on a half line with `Γ(k) = p_{1−k}`.
* **Proposition 3.3.2** (`proposition_3_3_2`, p. 57): the M/G/1 matrix `mG1Matrix` is a transition
  matrix.
* **Proposition 3.3.3** (`proposition_3_3_3`, p. 58): the linear model on `ℚ` has transition
  matrix `P(r, q) = Γ(q − αr)`.

**Corrections.**
* The displayed matrix for `V⁻` (p. 55) puts `b(x + 1)`, `b(j) = p(j + 1)/p̄(j)`, in row `x`,
  column `0`; by (3.10) the entry is `p(x + 1)/p̄(x) = b(x)`. With `p(1) = p(2) = 1/2` the display
  gives `P(0, 0) = b(1) = 1` but (3.10) gives `1/2` (`bwdRecMatrix_display_counterexample`). The
  matrix is `bwdRecMatrix` (rows `b(0), b(1), …`).
* The storage-model formula `Γ(x) = Σᵢ H(i) G(x + i)` (p. 56) has the wrong sign: with input
  `S ∼ H` and release `J ∼ G`, `P(S − J = x) = Σᵢ H(i) G(i − x)` (`storage_increment_singleton`).
  With `H = δ₀`, `G = δ₁` the book's formula gives `Γ(1) = 1`, while `S − J = −1` surely
  (`storage_increment_counterexample`).
* (3.19) is stated for `j ≥ 1` in the display but for every `j ≥ 0` in the text; `q₀` is needed
  (it is the first column), and `poissonWeight` is defined for all `j ≥ 0`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal NNReal

/-! ### Forward and backward recurrence time chains -/

/-- The forward recurrence time chain `V⁺` (MT p. 54) for a renewal increment law `p` on
`{1, 2, …}`. State `k` stands for `V⁺ = k + 1`: from `V⁺ = 1` the chain jumps to `j` with
probability `p(j)`, and from `V⁺ = k + 1 > 1` it moves to `k`. -/
noncomputable def fwdRecMatrix (p : ℕ → ℝ≥0∞) (k j : ℕ) : ℝ≥0∞ :=
  if k = 0 then p (j + 1) else if j + 1 = k then 1 else 0

/-- The forward recurrence time matrix is a transition matrix when `p` is a probability on
`{1, 2, …}`. -/
theorem isTransitionMatrix_fwdRecMatrix {p : ℕ → ℝ≥0∞} (hp : ∑' j, p (j + 1) = 1) :
    IsTransitionMatrix (fwdRecMatrix p) := fun k => by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [fwdRecMatrix] using hp
  · simp only [fwdRecMatrix, Nat.pos_iff_ne_zero.1 hk, ite_false]
    rw [tsum_eq_single (k - 1) fun j hj => by simp only [ite_eq_right_iff]; omega]
    simp only [ite_eq_left_iff]
    omega

/-- The tail `p̄(n) = Σ_{j ≥ n + 1} p(j)` (3.9), MT p. 54. -/
noncomputable def ptail (p : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := ∑' j, p (j + n + 1)

/-- `p̄(n) = p(n + 1) + p̄(n + 1)`. -/
theorem ptail_eq (p : ℕ → ℝ≥0∞) (n : ℕ) : ptail p n = p (n + 1) + ptail p (n + 1) := by
  rw [ptail, tsum_eq_zero_add' ENNReal.summable, ptail]
  congr 1
  · simp
  · exact tsum_congr fun j => by ring_nf

/-- `p̄(x) ≠ 0` iff `p(m) > 0` for some `m > x`, i.e. iff `x < M = sup{m : p(m) > 0}`. -/
theorem ptail_ne_zero_iff (p : ℕ → ℝ≥0∞) (x : ℕ) : ptail p x ≠ 0 ↔ ∃ m, x < m ∧ p m ≠ 0 := by
  rw [ptail, ne_eq, ENNReal.tsum_eq_zero]
  push Not
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j + x + 1, by omega, hj⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m - x - 1, by rwa [show m - x - 1 + x + 1 = m by omega]⟩

/-- The backward recurrence time chain `V⁻` (3.10), MT p. 55:
`P(x, x + 1) = p̄(x + 1)/p̄(x)` and `P(x, 0) = p(x + 1)/p̄(x)`. -/
noncomputable def bwdRecMatrix (p : ℕ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if y = x + 1 then ptail p (x + 1) / ptail p x else if y = 0 then p (x + 1) / ptail p x else 0

/-- The rows of the backward recurrence matrix sum to one on `{x : 0 < p̄(x) < ∞}`. -/
theorem bwdRecMatrix_rowSum (p : ℕ → ℝ≥0∞) {x : ℕ} (h0 : ptail p x ≠ 0) (ht : ptail p x ≠ ⊤) :
    ∑' y, bwdRecMatrix p x y = 1 := by
  rw [tsum_eq_sum (s := {0, x + 1}) fun y hy => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    simp [bwdRecMatrix, hy.1, hy.2]]
  rw [Finset.sum_pair (by omega)]
  simp only [bwdRecMatrix, show (0 : ℕ) ≠ x + 1 by omega, ite_false, ite_true]
  rw [ENNReal.div_add_div_same, ← ptail_eq, ENNReal.div_self h0 ht]

/-- The set `{x : p̄(x) ≠ 0}` is closed for `V⁻` (when `p̄(0) ≠ 0`), so it is the state space
`{0, …, M − 1}` of MT p. 55. -/
theorem ptail_ne_zero_of_bwdRecMatrix (p : ℕ → ℝ≥0∞) (h00 : ptail p 0 ≠ 0) {x y : ℕ}
    (h : bwdRecMatrix p x y ≠ 0) : ptail p y ≠ 0 := by
  by_cases hy : y = x + 1
  · subst hy
    simp only [bwdRecMatrix, ite_true] at h
    exact fun h' => h (by simp [h'])
  · by_cases hy0 : y = 0
    · subst hy0; exact h00
    · simp [bwdRecMatrix, hy, hy0] at h

/-- The `V⁻` matrix has `P(x, 0) = b(x)`, with `b(j) = p(j + 1)/p̄(j)`. -/
theorem bwdRecMatrix_zero (p : ℕ → ℝ≥0∞) (x : ℕ) :
    bwdRecMatrix p x 0 = p (x + 1) / ptail p x := by
  simp [bwdRecMatrix]

/-- The renewal law with `p(1) = p(2) = 1/2`. -/
noncomputable def halfHalf (j : ℕ) : ℝ≥0∞ := if j = 1 ∨ j = 2 then 2⁻¹ else 0

/-- **Correction** (MT p. 55): the displayed `V⁻` matrix has `b(1) = p(2)/p̄(1)` in row `0`,
column `0`, but (3.10) gives `P(0, 0) = p(1)/p̄(0)`. For `p(1) = p(2) = 1/2` these are `1` and
`1/2`. -/
theorem bwdRecMatrix_display_counterexample :
    bwdRecMatrix halfHalf 0 0 ≠ halfHalf 2 / ptail halfHalf 1 := by
  have h0 : ptail halfHalf 0 = 1 := by
    rw [ptail, tsum_eq_sum (s := {0, 1}) fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp only [halfHalf]; split_ifs with h
      · exfalso; omega
      · rfl]
    simp [halfHalf, ENNReal.inv_two_add_inv_two]
  have h1 : ptail halfHalf 1 = 2⁻¹ := by
    rw [ptail, tsum_eq_single 0 fun j hj => by
      simp only [halfHalf]; split_ifs with h
      · exfalso; omega
      · rfl]
    simp [halfHalf]
  have e1 : halfHalf (0 + 1) = 2⁻¹ := by simp [halfHalf]
  have e2 : halfHalf 2 = 2⁻¹ := by simp [halfHalf]
  rw [bwdRecMatrix_zero, h0, h1, e1, e2, div_one, ENNReal.div_self (by simp) (by simp)]
  intro h
  rw [ENNReal.inv_eq_one] at h
  norm_num at h

/-! ### Random walks -/

/-- The random walk on `ℤ` (3.11), MT p. 55: `P(x, y) = Γ(y − x)`. -/
def rwMatrix (Γ : ℤ → ℝ≥0∞) (x y : ℤ) : ℝ≥0∞ := Γ (y - x)

/-- The random walk matrix is a transition matrix when `Γ` is a probability on `ℤ`. -/
theorem isTransitionMatrix_rwMatrix {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' k, Γ k = 1) :
    IsTransitionMatrix (rwMatrix Γ) := fun x => by
  rw [← hΓ]
  exact (Equiv.subRight x).tsum_eq Γ

/-- Translation invariance of the random walk (MT p. 55). -/
theorem rwMatrix_translate (Γ : ℤ → ℝ≥0∞) (x y c : ℤ) :
    rwMatrix Γ (x + c) (y + c) = rwMatrix Γ x y := by
  simp [rwMatrix]

/-- (3.11): if `W ∼ ν`, then `P(x + W = y) = ν{y − x}`. -/
theorem rw_step_law (ν : Measure ℤ) (x y : ℤ) :
    (ν.map fun w => x + w) {y} = ν {y - x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y)]
  congr 1
  ext w
  simp only [mem_preimage, mem_singleton_iff]
  omega

/-- The random walk on the half line `ℤ₊` (3.12)–(3.14), MT pp. 55–56:
`P(x, y) = Γ(y − x)` for `y > 0` and `P(x, 0) = Γ(−∞, −x]`. -/
noncomputable def rwhlMatrix (Γ : ℤ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if y = 0 then ∑' k : ℤ, (if k ≤ -(x : ℤ) then Γ k else 0) else Γ ((y : ℤ) - x)

/-- The half-line random walk matrix is a transition matrix when `Γ` is a probability on `ℤ`. -/
theorem isTransitionMatrix_rwhlMatrix {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' k, Γ k = 1) :
    IsTransitionMatrix (rwhlMatrix Γ) := fun x => by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [rwhlMatrix, ite_true, Nat.add_one_ne_zero, ite_false]
  have hg : Function.Injective fun y : ℕ => ((y + 1 : ℕ) : ℤ) - x := fun a b h => by
    simp only at h; omega
  have hsupp : Function.support (fun k : ℤ => if -(x : ℤ) < k then Γ k else 0) ⊆
      Set.range fun y : ℕ => ((y + 1 : ℕ) : ℤ) - x := by
    intro k hk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hk
    obtain ⟨hk, -⟩ := hk
    exact ⟨(k + x - 1).toNat, by simp only; omega⟩
  have h2 := hg.tsum_eq hsupp
  simp only [show ∀ y : ℕ, -(x : ℤ) < ((y + 1 : ℕ) : ℤ) - x by intro y; omega, ite_true] at h2
  rw [h2, ← ENNReal.tsum_add, ← hΓ]
  refine tsum_congr fun k => ?_
  by_cases hk : k ≤ -(x : ℤ)
  · simp [hk, not_lt.2 hk]
  · simp [hk, lt_of_not_ge hk]

/-! ### The simple storage model -/

/-- The increment `S − J` of the storage model, for independent input `S ∼ H` and release
`J ∼ G` (MT p. 56): `P(S − J = x) = Σᵢ H(i) G(i − x)`. -/
theorem storage_increment_singleton (H G : Measure ℤ) [SFinite H] [SFinite G] (x : ℤ) :
    (H.prod G).map (fun p : ℤ × ℤ => p.1 - p.2) {x} = ∑' i, H {i} * G {i - x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have hset : (fun p : ℤ × ℤ => p.1 - p.2) ⁻¹' {x} = ⋃ i : ℤ, ({i} : Set ℤ) ×ˢ {i - x} := by
    ext ⟨a, b⟩
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_prod]
    constructor
    · intro h; exact ⟨a, rfl, by omega⟩
    · rintro ⟨i, rfl, rfl⟩; omega
  rw [hset, measure_iUnion (fun i j hij => by
      refine Set.disjoint_left.2 fun p hi hj => hij ?_
      simp only [mem_prod, mem_singleton_iff] at hi hj
      rw [← hi.1, ← hj.1]) (fun i => (measurableSet_singleton i).prod (measurableSet_singleton _))]
  exact tsum_congr fun i => Measure.prod_prod _ _

/-- **Correction** (MT p. 56): the book's `Γ(x) = Σᵢ H(i) G(x + i)` is not the increment law.
With `S = 0` and `J = 1` surely, `P(S − J = 1) = 0`, but the book's sum at `x = 1` is `1`. -/
theorem storage_increment_counterexample :
    ((Measure.dirac (0 : ℤ)).prod (Measure.dirac (1 : ℤ))).map (fun p : ℤ × ℤ => p.1 - p.2) {1} ≠
      ∑' i : ℕ, Measure.dirac (0 : ℤ) {(i : ℤ)} * Measure.dirac (1 : ℤ) {1 + (i : ℤ)} := by
  rw [storage_increment_singleton, tsum_eq_single 0 fun i hi => by
      simp [Measure.dirac_apply', show (i : ℤ) ≠ 0 by omega]]
  rw [tsum_eq_single 0 fun i hi => by
      simp only [Measure.dirac_apply' _ (measurableSet_singleton _), mem_singleton_iff,
        indicator_apply]
      simp [hi]]
  simp

/-! ### Embedded queueing models -/

/-- The mixed Poisson weights `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)` of (3.14)–(3.15) and (3.19): the
probability of `j` events of a rate-`μ` Poisson process in a time `T ∼ G`. -/
noncomputable def poissonWeight (G : Measure ℝ≥0) (μ : ℝ≥0) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ t, poissonMeasure (μ * t) {j} ∂G

/-- (3.14)–(3.15): `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)`. -/
theorem poissonWeight_eq (G : Measure ℝ≥0) (μ : ℝ≥0) (j : ℕ) :
    poissonWeight G μ j =
      ∫⁻ t, ENNReal.ofReal (exp (-((μ * t : ℝ≥0) : ℝ)) * ((μ * t : ℝ≥0) : ℝ) ^ j / j.factorial)
        ∂G := by
  simp_rw [poissonWeight, poissonMeasure_singleton]

/-- `Σⱼ pⱼ = 1`: the mixed Poisson weights form a probability on `ℤ₊`. -/
theorem tsum_poissonWeight (G : Measure ℝ≥0) [IsProbabilityMeasure G] (μ : ℝ≥0) :
    ∑' j, poissonWeight G μ j = 1 := by
  have hm : ∀ j, Measurable fun t : ℝ≥0 => poissonMeasure (μ * t) {j} := fun j => by
    simp_rw [poissonMeasure_singleton]
    fun_prop
  unfold poissonWeight
  rw [← lintegral_tsum fun j => (hm j).aemeasurable]
  have : ∀ t : ℝ≥0, ∑' j, poissonMeasure (μ * t) {j} = 1 := fun t => by
    have h := Measure.tsum_indicator_apply_singleton (poissonMeasure (μ * t)) univ
      MeasurableSet.univ
    simp only [indicator_univ] at h
    rw [h, measure_univ]
  simp [this]

/-- The GI/M/1 matrix of Proposition 3.3.1 (MT p. 56): `P(x, y) = p_{x+1−y}` for
`0 < y ≤ x + 1` and `P(x, 0) = q_x = Σ_{i ≥ x+1} pᵢ`. -/
noncomputable def giM1Matrix (p : ℕ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if y = 0 then ∑' i, p (i + x + 1) else if y ≤ x + 1 then p (x + 1 - y) else 0

/-- The increment law `Γ(k) = p_{1−k}` (`k ≤ 1`) of the GI/M/1 queue as a random walk. -/
noncomputable def giM1Increment (p : ℕ → ℝ≥0∞) (k : ℤ) : ℝ≥0∞ :=
  if k ≤ 1 then p (1 - k).toNat else 0

/-- The GI/M/1 matrix is the half-line random walk with increments `Γ(k) = p_{1−k}`
(MT p. 57, "hence `N` is a random walk on a half line"). -/
theorem giM1Matrix_eq_rwhl (p : ℕ → ℝ≥0∞) : giM1Matrix p = rwhlMatrix (giM1Increment p) := by
  funext x y
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp only [giM1Matrix, rwhlMatrix, ite_true]
    have hg : Function.Injective fun i : ℕ => -(x : ℤ) - i := fun a b h => by
      simp only at h; omega
    have hsupp : Function.support (fun k : ℤ =>
        if k ≤ -(x : ℤ) then giM1Increment p k else 0) ⊆ Set.range fun i : ℕ => -(x : ℤ) - i := by
      intro k hk
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hk
      obtain ⟨hk, -⟩ := hk
      exact ⟨(-(x : ℤ) - k).toNat, by simp only; omega⟩
    rw [← hg.tsum_eq hsupp]
    refine tsum_congr fun i => ?_
    simp only [show -(x : ℤ) - i ≤ -(x : ℤ) by omega, ite_true, giM1Increment,
      show -(x : ℤ) - i ≤ 1 by omega]
    congr 1
    omega
  · simp only [giM1Matrix, rwhlMatrix, Nat.pos_iff_ne_zero.1 hy, ite_false, giM1Increment]
    by_cases h : y ≤ x + 1
    · simp only [h, show ((y : ℤ) - x ≤ 1) by omega, ite_true]
      congr 1
      omega
    · simp only [h, show ¬((y : ℤ) - x ≤ 1) by omega, ite_false]

/-- The GI/M/1 increments sum to one when the `p_j` do. -/
theorem tsum_giM1Increment {p : ℕ → ℝ≥0∞} (hp : ∑' j, p j = 1) :
    ∑' k, giM1Increment p k = 1 := by
  have hg : Function.Injective fun j : ℕ => (1 : ℤ) - j := fun a b h => by
    simp only at h; omega
  have hsupp : Function.support (giM1Increment p) ⊆ Set.range fun j : ℕ => (1 : ℤ) - j := by
    intro k hk
    simp only [Function.mem_support, giM1Increment, ne_eq, ite_eq_right_iff, not_forall] at hk
    obtain ⟨hk, -⟩ := hk
    exact ⟨(1 - k).toNat, by simp only; omega⟩
  rw [← hg.tsum_eq hsupp, ← hp]
  refine tsum_congr fun j => ?_
  simp only [giM1Increment, show (1 : ℤ) - j ≤ 1 by omega, ite_true]
  congr 1
  omega

/-- **Proposition 3.3.1** (MT p. 56). For the GI/M/1 queue with service rate `μ` and
inter-arrival law `G`, the matrix with `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)` and
`q_j = Σ_{i ≥ j+1} pᵢ` is a transition matrix on `ℤ₊` (so Theorem 3.2.1 builds the chain `N`),
and it is the random walk on a half line with increments `Γ(k) = p_{1−k}`. -/
theorem proposition_3_3_1 (G : Measure ℝ≥0) [IsProbabilityMeasure G] (μ : ℝ≥0) :
    IsTransitionMatrix (giM1Matrix (poissonWeight G μ)) ∧
      giM1Matrix (poissonWeight G μ) = rwhlMatrix (giM1Increment (poissonWeight G μ)) := by
  refine ⟨?_, giM1Matrix_eq_rwhl _⟩
  rw [giM1Matrix_eq_rwhl]
  exact isTransitionMatrix_rwhlMatrix (tsum_giM1Increment (tsum_poissonWeight G μ))

/-- The M/G/1 matrix of Proposition 3.3.2 (MT p. 57): row `0` is `(q₀, q₁, …)` and row `x ≥ 1`
is `P(x, y) = q_{y+1−x}` for `y ≥ x − 1`. -/
noncomputable def mG1Matrix (q : ℕ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if x = 0 then q y else if x ≤ y + 1 then q (y + 1 - x) else 0

/-- The M/G/1 matrix is a transition matrix when the `q_j` sum to one. -/
theorem isTransitionMatrix_mG1Matrix {q : ℕ → ℝ≥0∞} (hq : ∑' j, q j = 1) :
    IsTransitionMatrix (mG1Matrix q) := fun x => by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa [mG1Matrix] using hq
  · simp only [mG1Matrix, Nat.pos_iff_ne_zero.1 hx, ite_false]
    have hg : Function.Injective fun j : ℕ => j + x - 1 := fun a b h => by
      simp only at h; omega
    have hsupp : Function.support (fun y : ℕ => if x ≤ y + 1 then q (y + 1 - x) else 0) ⊆
        Set.range fun j : ℕ => j + x - 1 := by
      intro y hy
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hy
      obtain ⟨hy, -⟩ := hy
      exact ⟨y + 1 - x, by simp only; omega⟩
    rw [← hg.tsum_eq hsupp, ← hq]
    refine tsum_congr fun j => ?_
    simp only [show x ≤ j + x - 1 + 1 by omega, ite_true]
    congr 1
    omega

/-- **Proposition 3.3.2** (MT p. 57). For the M/G/1 queue with arrival rate `r` and service law
`H`, the matrix with `q_j = ∫ e^{−rt}(rt)ʲ/j! H(dt)` (3.19) is a transition matrix on `ℤ₊`, so
Theorem 3.2.1 builds the chain `N*`. -/
theorem proposition_3_3_2 (H : Measure ℝ≥0) [IsProbabilityMeasure H] (r : ℝ≥0) :
    IsTransitionMatrix (mG1Matrix (poissonWeight H r)) :=
  isTransitionMatrix_mG1Matrix (tsum_poissonWeight H r)

/-! ### Linear models on the rationals -/

/-- The AR(1) model on `ℚ` (MT p. 58): `P(r, q) = Γ(q − αr)`. -/
def arMatrix (α : ℚ) (Γ : ℚ → ℝ≥0∞) (r q : ℚ) : ℝ≥0∞ := Γ (q - α * r)

/-- **Proposition 3.3.3** (MT p. 58). For `α ∈ ℚ` and a noise law `ν` on `ℚ` with
`Γ(q) = ν{q}`, one step of `Xₙ₊₁ = αXₙ + Wₙ₊₁` from `r` lands on `q` with probability
`Γ(q − αr)`, and `P(r, q) = Γ(q − αr)` is a transition matrix on `ℚ` (so Theorem 3.2.1 builds the
chain). -/
theorem proposition_3_3_3 (α : ℚ) (ν : Measure ℚ) [IsProbabilityMeasure ν] :
    (∀ r q, (ν.map fun w => α * r + w) {q} = arMatrix α (fun q => ν {q}) r q) ∧
      IsTransitionMatrix (arMatrix α fun q => ν {q}) := by
  refine ⟨fun r q => ?_, fun r => ?_⟩
  · rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton q), arMatrix]
    congr 1
    ext w
    simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  · simp only [arMatrix]
    have h := Measure.tsum_indicator_apply_singleton ν univ MeasurableSet.univ
    simp only [indicator_univ] at h
    have he := (Equiv.subRight (α * r)).tsum_eq fun q => ν {q}
    simp only [Equiv.subRight_apply] at he
    rw [he, h, measure_univ]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Communication for countable models (MT §4.1.1, §4.1.3)

Meyn and Tweedie, §4.1.1, pp. 76–77, and §4.1.3, pp. 80–81. The chains are built from the
transition matrices of §3.3 (`SpecificMatrices`) by `matKernel`.

**Matrix chains.** `leads_of_pos`: a positive entry `P(x, y) > 0` gives `x → y`;
`isAbsorbing_matKernel_iff`: `A` is absorbing iff `P(x, y) = 0` for `x ∈ A`, `y ∉ A`.

**Random walk on a half line** (4.2)–(4.4), p. 76–77, `rwhlMatrix Γ` on `ℤ₊`.
* `rwhl_pow_zero_ge`: if `Γ(w) = δ` for some `w < 0`, then `Pⁿ(x, 0) ≥ δⁿ` once `n|w| ≥ x`;
  `rwhl_hitProb_zero_pos`: hence `L(x, 0) > 0` for every `x`.
* `rwhl_hitProb_zero_eq_zero`: if `Γ(−∞, 0) = 0`, then `{0}` is not reached from any `x ≠ 0`.
* `rwhl_even_increments`: increments concentrated on the even integers, with `Γ(2y) > 0` for all
  `y`: the even states form an absorbing set, so no odd state is reached from an even one, while
  from an odd state every state is reached.

**Irreducible models** (§4.1.3).
* Forward recurrence time chain (4.6)–(4.7), p. 80: `fwdRec_isAbsorbing` (the states
  `{1, …, r}` are absorbing), `fwdRec_communicates` (they communicate) and `fwdRec_pow_down`
  (`P^{x−y}(x, y) = 1`).
* GI/M/1 queue, p. 80: `giM1_isIrreducibleChain` (if `p₀ > 0` and `P(x, 0) > 0` for all `x`),
  `giM1_poisson_isIrreducibleChain` (for the Poisson weights of Proposition 3.3.1 with `μ > 0`
  and `G` not concentrated at `0`).
* M/G/1 queue, p. 80: `mG1_isIrreducibleChain`, `mG1_poisson_isIrreducibleChain`.
* Random walk on `ℤ`, p. 81: with `H` the subgroup generated by the support of `Γ` (`H = dℤ`, `d`
  the g.c.d. of the support, `rw_closure_eq_zmultiples`), the cosets `x + H` are absorbing
  (`rw_coset_isAbsorbing`); if `Γ` charges both half lines they are exactly the communicating
  classes (`rw_commClass_eq`), and there are finitely many of them (`rw_commClass_finite`).
* Random walk on `ℚ` with integer increments, p. 81: the classes `q + ℤ` are absorbing and
  irreducible (`ratWalk_commClass_eq`, `ratWalk_isAbsorbing`), and there are infinitely many
  (`ratWalk_commClass_infinite`).

**Corrections.**
* p. 77: "`L(x, 0) > 0` for all states `x` or for none" is false at `x = 0`: with `Γ = δ₀`,
  `L(0, 0) = 1` but `L(1, 0) = 0` (`rwhl_dichotomy_counterexample`). The dichotomy holds for the
  states `x ≠ 0`.
* p. 80: the GI/M/1 chain is not irreducible "no matter what the distribution of the
  inter-arrival times": if `G = δ₀` then `p₀ = 1`, the chain only moves up, and `1` does not lead
  to `0` (`giM1_dirac_counterexample`). It is irreducible when `μ > 0` and `G` is not concentrated
  at `0` (`giM1_poisson_isIrreducibleChain`).
* p. 80: likewise the M/G/1 chain is not "always irreducible": if `H = δ₀` then `q₀ = 1`, the
  chain is absorbed at `0`, and `0` does not lead to `1` (`mG1_dirac_counterexample`). It is
  irreducible when `r > 0` and `H` is not concentrated at `0`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-! ### Matrix chains -/

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- `P¹(x, y) = P(x, y)`. -/
theorem matKernel_pow_one_singleton (p : X → X → ℝ≥0∞) (x y : X) :
    (matKernel p ^ 1) x {y} = p x y := by
  rw [pow_one, matKernel_singleton]

/-- A positive entry `P(x, y) > 0` gives `x → y`. -/
theorem leads_of_pos {p : X → X → ℝ≥0∞} [IsMarkovKernel (matKernel p)] {x y : X}
    (h : p x y ≠ 0) : Leads (matKernel p) x y :=
  (leads_iff_exists_pow _ x y).2 ⟨1, by rw [matKernel_pow_one_singleton]; exact pos_iff_ne_zero.2 h⟩

/-- A set is absorbing for a transition matrix iff no positive entry leads out of it. -/
theorem isAbsorbing_matKernel_iff {p : X → X → ℝ≥0∞} [IsMarkovKernel (matKernel p)]
    (A : Set X) : IsAbsorbing (matKernel p) A ↔ ∀ x ∈ A, ∀ y ∉ A, p x y = 0 := by
  have hA := measurableSet_of_countable A
  refine forall₂_congr fun x _ => ?_
  rw [← prob_compl_eq_zero_iff hA, matKernel_apply, ENNReal.tsum_eq_zero]
  refine forall_congr' fun y => ?_
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy]

/-- A state reached from a point of an absorbing set lies in the set. -/
theorem IsAbsorbing.mem_of_leads {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) {x y : X} (hx : x ∈ A) (hxy : Leads P x y) : y ∈ A := by
  by_contra hy
  obtain ⟨n, hn⟩ := (leads_iff_exists_pow P x y).1 hxy
  have h0 := hAbs.pow_compl (measurableSet_of_countable A) n hx
  have : (P ^ n) x {y} ≤ (P ^ n) x Aᶜ := measure_mono (singleton_subset_iff.2 hy)
  rw [h0] at this
  exact lt_irrefl _ (hn.trans_le this)

/-- `x → y` and a positive entry `P(y, z)` give `x → z`. -/
theorem Leads.step {p : X → X → ℝ≥0∞} [IsMarkovKernel (matKernel p)] {x y z : X}
    (hxy : Leads (matKernel p) x y) (h : p y z ≠ 0) : Leads (matKernel p) x z :=
  hxy.trans (leads_of_pos h)

/-! ### Random walk on a half line (§4.1.1) -/

/-- `P(x, 0) ≥ Γ(w)` for `w ≤ −x`. -/
theorem rwhl_zero_ge (Γ : ℤ → ℝ≥0∞) {x : ℕ} {w : ℤ} (hw : w ≤ -(x : ℤ)) :
    Γ w ≤ rwhlMatrix Γ x 0 := by
  simp only [rwhlMatrix, ite_true]
  have := ENNReal.le_tsum (f := fun k : ℤ => if k ≤ -(x : ℤ) then Γ k else 0) w
  simpa [hw] using this

/-- MT p. 77: if `Γ(w) = δ` for some `w < 0`, then `Pⁿ(x, 0) ≥ δⁿ` whenever `x ≤ n|w|`. -/
theorem rwhl_pow_zero_ge (Γ : ℤ → ℝ≥0∞) {w : ℤ} (hw : w < 0) (n : ℕ) (x : ℕ)
    (hx : (x : ℤ) ≤ n * (-w)) : Γ w ^ n ≤ (matKernel (rwhlMatrix Γ) ^ n) x {0} := by
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0
    rw [pow_zero, pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton 0)]
  | succ n ih =>
    rw [pow_succ_apply _ n x (measurableSet_singleton 0), lintegral_matKernel, pow_succ']
    set y : ℕ := ((x : ℤ) + w).toNat
    refine le_trans ?_ (ENNReal.le_tsum y)
    by_cases hxw : (x : ℤ) + w ≤ 0
    · have hy : y = 0 := Int.toNat_of_nonpos hxw
      rw [hy]
      exact mul_le_mul' (rwhl_zero_ge Γ (by omega)) (ih 0 (by push_cast; nlinarith))
    · have hy : (y : ℤ) = x + w := Int.toNat_of_nonneg (by omega)
      have hy0 : y ≠ 0 := by omega
      have hp : rwhlMatrix Γ x y = Γ w := by
        simp only [rwhlMatrix, hy0, ite_false, hy]
        congr 1
        ring
      rw [hp]
      exact mul_le_mul' le_rfl (ih y (by rw [hy]; push_cast at hx ⊢; linarith))

/-- MT p. 77: if (4.4) holds, `Γ(w) > 0` for some `w < 0`, then `{0}` is reached with positive
probability from every state, `L(x, 0) > 0`. -/
theorem rwhl_hitProb_zero_pos {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwhlMatrix Γ))]
    {w : ℤ} (hw : w < 0) (hΓw : Γ w ≠ 0) (x : ℕ) :
    0 < hitProb (matKernel (rwhlMatrix Γ)) {0} x := by
  refine (hitProb_pos_iff _ (measurableSet_singleton 0) x).2 ⟨x, ?_⟩
  refine (ENNReal.pow_pos (pos_iff_ne_zero.2 hΓw) _).trans_le (rwhl_pow_zero_ge Γ hw _ x ?_)
  push_cast
  nlinarith

/-- MT p. 77: if `P(W < 0) = 0`, then `{0}` cannot be reached from any state `x ≠ 0`. -/
theorem rwhl_hitProb_zero_eq_zero {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwhlMatrix Γ))]
    (hΓ : ∀ k < 0, Γ k = 0) {x : ℕ} (hx : x ≠ 0) :
    hitProb (matKernel (rwhlMatrix Γ)) {0} x = 0 := by
  have hAbs : IsAbsorbing (matKernel (rwhlMatrix Γ)) {y | x ≤ y} := by
    rw [isAbsorbing_matKernel_iff]
    intro y hy z hz
    simp only [mem_ofPred_eq, not_le] at hy hz
    by_cases hz0 : z = 0
    · subst hz0
      simp only [rwhlMatrix, ite_true]
      refine ENNReal.tsum_eq_zero.2 fun k => ?_
      split_ifs with hk
      · exact hΓ k (by omega)
      · rfl
    · simp only [rwhlMatrix, hz0, ite_false]
      exact hΓ _ (by omega)
  exact hAbs.hitProb_eq_zero (measurableSet_of_countable _)
    (Set.disjoint_left.2 fun y hy h0 => by
      rw [mem_singleton_iff.1 h0] at hy
      exact hx (Nat.le_zero.1 hy)) (mem_ofPred_eq ▸ le_rfl)

/-- The increment law `Γ = δ₀` on `ℤ`. -/
noncomputable def diracZeroInt (k : ℤ) : ℝ≥0∞ := if k = 0 then 1 else 0

/-- **Correction (MT p. 77).** "`L(x, 0) > 0` for all states `x` or for none" fails at `x = 0`:
for `Γ = δ₀` the walk returns to `0` from `0` but never reaches `0` from `1`. -/
theorem rwhl_dichotomy_counterexample :
    ∃ _ : IsMarkovKernel (matKernel (rwhlMatrix diracZeroInt)),
      0 < hitProb (matKernel (rwhlMatrix diracZeroInt)) {0} 0 ∧
      hitProb (matKernel (rwhlMatrix diracZeroInt)) {0} 1 = 0 := by
  have hsum : ∑' k, diracZeroInt k = 1 := by
    rw [tsum_eq_single 0 fun k hk => by simp [diracZeroInt, hk]]
    simp [diracZeroInt]
  have hM := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hsum)
  refine ⟨hM, ?_, rwhl_hitProb_zero_eq_zero (fun k hk => by simp [diracZeroInt, hk.ne])
    one_ne_zero⟩
  refine (hitProb_pos_iff _ (measurableSet_singleton 0) 0).2 ⟨0, ?_⟩
  rw [zero_add, matKernel_pow_one_singleton]
  refine lt_of_lt_of_le ?_ (rwhl_zero_ge diracZeroInt (x := 0) (w := 0) le_rfl)
  simp [diracZeroInt]

/-- MT p. 77: increments concentrated on the even integers, with `Γ(2y) > 0` for all `y`. The
even states `ℤ₊⁰` form an absorbing set, so no odd state is reached from an even state; from an
odd state every state is reached (through `0`). -/
theorem rwhl_even_increments {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwhlMatrix Γ))]
    (hodd : ∀ y, Γ (2 * y + 1) = 0) (heven : ∀ y, Γ (2 * y) ≠ 0) :
    IsAbsorbing (matKernel (rwhlMatrix Γ)) {x | Even x} ∧
      (∀ x y : ℕ, Even x → Odd y → hitProb (matKernel (rwhlMatrix Γ)) {y} x = 0) ∧
      ∀ w y : ℕ, Odd w → Leads (matKernel (rwhlMatrix Γ)) w y := by
  have hAbs : IsAbsorbing (matKernel (rwhlMatrix Γ)) {x | Even x} := by
    rw [isAbsorbing_matKernel_iff]
    intro x hx z hz
    simp only [mem_ofPred_eq, Nat.not_even_iff_odd] at hx hz
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    have hz0 : z ≠ 0 := by omega
    simp only [rwhlMatrix, hz0, ite_false]
    have : (z : ℤ) - x = 2 * ((b : ℤ) - a) + 1 := by push_cast [ha, hb]; ring
    rw [this]
    exact hodd _
  refine ⟨hAbs, fun x y hx hy => hAbs.hitProb_eq_zero (measurableSet_of_countable _)
    (Set.disjoint_left.2 fun z hz hzy => ?_) hx, fun w y hw => ?_⟩
  · rw [mem_singleton_iff.1 hzy] at hz
    exact (Nat.not_even_iff_odd.2 hy) hz
  · obtain ⟨m, hm⟩ := hw
    have hw0 : Leads (matKernel (rwhlMatrix Γ)) w 0 := by
      refine leads_of_pos fun h => heven (-(m : ℤ) - 1) ?_
      exact nonpos_iff_eq_zero.1 (h ▸ rwhl_zero_ge Γ (by push_cast [hm]; omega))
    rcases Nat.even_or_odd y with ⟨k, hk⟩ | ⟨k, hk⟩
    · by_cases hy0 : y = 0
      · exact hy0 ▸ hw0
      · refine hw0.step ?_
        simp only [rwhlMatrix, hy0, ite_false]
        have : ((y : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast [hk]; ring
        rw [this]
        exact heven _
    · refine leads_of_pos ?_
      have hy0 : y ≠ 0 := by omega
      simp only [rwhlMatrix, hy0, ite_false]
      have : (y : ℤ) - w = 2 * ((k : ℤ) - m) := by push_cast [hk, hm]; ring
      rw [this]
      exact heven _

/-! ### The forward recurrence time chain (§4.1.3) -/

/-- MT p. 80: with `r = sup{n : p(n) > 0}` finite, the states `V⁺ ∈ {1, …, r}`, i.e.
`{k : k < r}` (state `k` stands for `V⁺ = k + 1`), form an absorbing set. -/
theorem fwdRec_isAbsorbing {p : ℕ → ℝ≥0∞} [IsMarkovKernel (matKernel (fwdRecMatrix p))]
    {r : ℕ} (hrmax : ∀ n, r < n → p n = 0) :
    IsAbsorbing (matKernel (fwdRecMatrix p)) {k | k < r} := by
  rw [isAbsorbing_matKernel_iff]
  intro k hk j hj
  simp only [mem_ofPred_eq, not_lt] at hk hj
  simp only [fwdRecMatrix]
  split_ifs with h0 h1
  · exact hrmax _ (by omega)
  · exact absurd h1 (by omega)
  · rfl

/-- The forward recurrence time chain moves down deterministically: `k → j` for `j ≤ k`. -/
theorem fwdRec_leads_down {p : ℕ → ℝ≥0∞} [IsMarkovKernel (matKernel (fwdRecMatrix p))]
    {k j : ℕ} (h : j ≤ k) : Leads (matKernel (fwdRecMatrix p)) k j := by
  induction k with
  | zero => rw [Nat.le_zero.1 h]; exact Leads.refl _ 0
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · refine (leads_of_pos ?_).trans (ih (by omega))
      simp [fwdRecMatrix]
    · rw [le_antisymm h hj]
      exact Leads.refl _ _

/-- (4.7), MT p. 80: `P^{x−y}(x, y) = 1`, written `Pᵏ(y + k, y) = 1`. -/
theorem fwdRec_pow_down (p : ℕ → ℝ≥0∞) (y k : ℕ) :
    (matKernel (fwdRecMatrix p) ^ k) (y + k) {y} = 1 := by
  induction k with
  | zero => rw [add_zero, pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton y)]
  | succ k ih =>
    rw [← add_assoc, pow_succ_apply _ k _ (measurableSet_singleton y), lintegral_matKernel,
      tsum_eq_single (y + k) fun z hz => by simp [fwdRecMatrix]; omega]
    simp [fwdRecMatrix, ih]

/-- MT p. 80: the forward recurrence time chain restricted to `{1, …, r}` is irreducible: all
of these states communicate. -/
theorem fwdRec_communicates {p : ℕ → ℝ≥0∞} [IsMarkovKernel (matKernel (fwdRecMatrix p))]
    {r : ℕ} (hr : p r ≠ 0) (hr1 : 1 ≤ r) {x y : ℕ} (hx : x < r) (hy : y < r) :
    Communicates (matKernel (fwdRecMatrix p)) x y := by
  have hlead : ∀ a b : ℕ, b < r → Leads (matKernel (fwdRecMatrix p)) a b := fun a b hb => by
    have h0 : Leads (matKernel (fwdRecMatrix p)) a 0 := fwdRec_leads_down (Nat.zero_le a)
    have h1 : Leads (matKernel (fwdRecMatrix p)) a (r - 1) := h0.step (by
      simp only [fwdRecMatrix, ite_true]
      rwa [Nat.sub_add_cancel hr1])
    exact h1.trans (fwdRec_leads_down (by omega))
  exact ⟨hlead x y hy, hlead y x hx⟩

/-! ### Queueing models (§4.1.3) -/

/-- MT p. 80: the GI/M/1 chain is irreducible when `P(x, x + 1) = p₀ > 0` and `P(x, 0) > 0` for
every `x`. -/
theorem giM1_isIrreducibleChain {p : ℕ → ℝ≥0∞} [IsMarkovKernel (matKernel (giM1Matrix p))]
    (hp0 : p 0 ≠ 0) (hq : ∀ x, ∑' i, p (i + x + 1) ≠ 0) :
    IsIrreducibleChain (matKernel (giM1Matrix p)) := by
  rw [isIrreducibleChain_iff]
  have h0y : ∀ y, Leads (matKernel (giM1Matrix p)) 0 y := fun y => by
    induction y with
    | zero => exact Leads.refl _ 0
    | succ y ih => exact ih.step (by simpa [giM1Matrix] using hp0)
  have hx0 : ∀ x, Leads (matKernel (giM1Matrix p)) x 0 := fun x =>
    leads_of_pos (by simpa [giM1Matrix] using hq x)
  exact fun x y => ⟨(hx0 x).trans (h0y y), (hx0 y).trans (h0y x)⟩

/-- The mixed Poisson weights are positive when the rate is positive and the mixing law is not
concentrated at `0`. -/
theorem poissonWeight_ne_zero {G : Measure ℝ≥0} {μ : ℝ≥0} (hμ : μ ≠ 0) (hG : G {0}ᶜ ≠ 0)
    (j : ℕ) : poissonWeight G μ j ≠ 0 := by
  have hm : Measurable fun t : ℝ≥0 => poissonMeasure (μ * t) {j} := by
    simp_rw [poissonMeasure_singleton]
    fun_prop
  rw [poissonWeight, ← pos_iff_ne_zero, lintegral_pos_iff_support hm]
  refine (pos_iff_ne_zero.2 hG).trans_le (measure_mono fun t ht => ?_)
  rw [Function.mem_support, poissonMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have ht' : (0 : ℝ) < ((μ * t : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.2 (mul_pos (pos_iff_ne_zero.2 hμ) (pos_iff_ne_zero.2 ht))
  exact div_pos (mul_pos (Real.exp_pos _) (pow_pos ht' j)) (Nat.cast_pos.2 (Nat.factorial_pos j))

/-- MT p. 80: the GI/M/1 chain of Proposition 3.3.1 is irreducible when the service rate is
positive and the inter-arrival law is not concentrated at `0`. -/
theorem giM1_poisson_isIrreducibleChain (G : Measure ℝ≥0) [IsProbabilityMeasure G] {μ : ℝ≥0}
    (hμ : μ ≠ 0) (hG : G {0}ᶜ ≠ 0) :
    ∃ _ : IsMarkovKernel (matKernel (giM1Matrix (poissonWeight G μ))),
      IsIrreducibleChain (matKernel (giM1Matrix (poissonWeight G μ))) := by
  have hM := isMarkovKernel_matKernel (proposition_3_3_1 G μ).1
  refine ⟨hM, giM1_isIrreducibleChain (poissonWeight_ne_zero hμ hG 0) fun x h => ?_⟩
  exact poissonWeight_ne_zero hμ hG (0 + x + 1)
    (nonpos_iff_eq_zero.1 (h ▸ ENNReal.le_tsum (f := fun i => poissonWeight G μ (i + x + 1)) 0))

/-- With `G = δ₀`, the mixed Poisson weights are `δ₀`. -/
theorem poissonWeight_dirac_zero (μ : ℝ≥0) (j : ℕ) :
    poissonWeight (Measure.dirac 0) μ j = if j = 0 then 1 else 0 := by
  rw [poissonWeight, lintegral_dirac, mul_zero, poissonMeasure_singleton]
  rcases j with _ | j <;> simp

/-- **Correction (MT p. 80).** The GI/M/1 chain is not irreducible for every inter-arrival
distribution: with `G = δ₀` the chain only moves up, so `1` does not lead to `0`. -/
theorem giM1_dirac_counterexample (μ : ℝ≥0) :
    ∃ _ : IsMarkovKernel (matKernel (giM1Matrix (poissonWeight (Measure.dirac 0) μ))),
      ¬ IsIrreducibleChain (matKernel (giM1Matrix (poissonWeight (Measure.dirac 0) μ))) := by
  have hM := isMarkovKernel_matKernel (proposition_3_3_1 (Measure.dirac 0) μ).1
  refine ⟨hM, fun h => ?_⟩
  have hAbs : IsAbsorbing (matKernel (giM1Matrix (poissonWeight (Measure.dirac 0) μ)))
      {y | 1 ≤ y} := by
    rw [isAbsorbing_matKernel_iff]
    intro x hx z hz
    simp only [mem_ofPred_eq, not_le, Nat.lt_one_iff] at hx hz
    subst hz
    simp only [giM1Matrix, ite_true, poissonWeight_dirac_zero]
    exact ENNReal.tsum_eq_zero.2 fun i => by simp
  have h10 := ((isIrreducibleChain_iff _).1 h 1 0).1
  exact absurd (hAbs.mem_of_leads (by simp : (1 : ℕ) ∈ {y : ℕ | 1 ≤ y}) h10)
    (by simp)

/-- MT p. 80: the M/G/1 chain is irreducible when all the `q_j` are positive. -/
theorem mG1_isIrreducibleChain {q : ℕ → ℝ≥0∞} [IsMarkovKernel (matKernel (mG1Matrix q))]
    (hq : ∀ j, q j ≠ 0) : IsIrreducibleChain (matKernel (mG1Matrix q)) := by
  rw [isIrreducibleChain_iff]
  have hx0 : ∀ x, Leads (matKernel (mG1Matrix q)) x 0 := fun x => by
    induction x with
    | zero => exact Leads.refl _ 0
    | succ x ih => exact (leads_of_pos (by simpa [mG1Matrix] using hq 0)).trans ih
  have h0y : ∀ y, Leads (matKernel (mG1Matrix q)) 0 y := fun y =>
    leads_of_pos (by simpa [mG1Matrix] using hq y)
  exact fun x y => ⟨(hx0 x).trans (h0y y), (hx0 y).trans (h0y x)⟩

/-- MT p. 80: the M/G/1 chain of Proposition 3.3.2 is irreducible when the arrival rate is
positive and the service law is not concentrated at `0`. -/
theorem mG1_poisson_isIrreducibleChain (H : Measure ℝ≥0) [IsProbabilityMeasure H] {r : ℝ≥0}
    (hr : r ≠ 0) (hH : H {0}ᶜ ≠ 0) :
    ∃ _ : IsMarkovKernel (matKernel (mG1Matrix (poissonWeight H r))),
      IsIrreducibleChain (matKernel (mG1Matrix (poissonWeight H r))) := by
  have hM := isMarkovKernel_matKernel (proposition_3_3_2 H r)
  exact ⟨hM, mG1_isIrreducibleChain (poissonWeight_ne_zero hr hH)⟩

/-- **Correction (MT p. 80).** The M/G/1 chain is not always irreducible: with `H = δ₀` the
chain is absorbed at `0`, so `0` does not lead to `1`. -/
theorem mG1_dirac_counterexample (r : ℝ≥0) :
    ∃ _ : IsMarkovKernel (matKernel (mG1Matrix (poissonWeight (Measure.dirac 0) r))),
      ¬ IsIrreducibleChain (matKernel (mG1Matrix (poissonWeight (Measure.dirac 0) r))) := by
  have hM := isMarkovKernel_matKernel (proposition_3_3_2 (Measure.dirac 0) r)
  refine ⟨hM, fun h => ?_⟩
  have hAbs : IsAbsorbing (matKernel (mG1Matrix (poissonWeight (Measure.dirac 0) r))) {0} := by
    rw [isAbsorbing_matKernel_iff]
    intro x hx z hz
    rw [mem_singleton_iff] at hx hz
    subst hx
    simp [mG1Matrix, poissonWeight_dirac_zero, hz]
  have h01 := ((isIrreducibleChain_iff _).1 h 0 1).1
  exact absurd (hAbs.mem_of_leads (mem_singleton 0) h01) (by simp)

/-! ### Unrestricted random walk on `ℤ` (§4.1.3) -/

/-- The subgroup `H` of `ℤ` generated by the support of the increment law `Γ`. -/
def rwSupportGroup (Γ : ℤ → ℝ≥0∞) : AddSubgroup ℤ := AddSubgroup.closure {k | Γ k ≠ 0}

/-- `H = dℤ` for some `d ≥ 0` (`d` is the g.c.d. of the support of `Γ`, MT p. 81). -/
theorem rw_closure_eq_zmultiples (Γ : ℤ → ℝ≥0∞) :
    ∃ d : ℕ, rwSupportGroup Γ = AddSubgroup.zmultiples (d : ℤ) := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic (rwSupportGroup Γ)
  exact ⟨a.natAbs, by rw [ha, Int.zmultiples_natAbs, AddSubgroup.zmultiples_eq_closure]⟩

/-- MT p. 81: each coset `x + H` (for `H = dℤ`, the set `D_r = {md + r}`) is absorbing. -/
theorem rw_coset_isAbsorbing {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwMatrix Γ))] (x : ℤ) :
    IsAbsorbing (matKernel (rwMatrix Γ)) {y | y - x ∈ rwSupportGroup Γ} := by
  rw [isAbsorbing_matKernel_iff]
  intro y hy z hz
  by_contra h
  have hzy : z - y ∈ rwSupportGroup Γ := AddSubgroup.subset_closure h
  exact hz (by simpa using add_mem hzy hy)

/-- From `x` the walk reaches `x + s` for every `s` in the additive monoid generated by the
support of `Γ`. -/
theorem rw_leads_add {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwMatrix Γ))] {s : ℤ}
    (hs : s ∈ AddSubmonoid.closure {k | Γ k ≠ 0}) (x : ℤ) :
    Leads (matKernel (rwMatrix Γ)) x (x + s) := by
  induction hs using AddSubmonoid.closure_induction generalizing x with
  | mem s hs => exact leads_of_pos (by simpa [rwMatrix] using hs)
  | zero => rw [add_zero]; exact Leads.refl _ x
  | add s t _ _ hs ht => rw [← add_assoc]; exact (hs x).trans (ht (x + s))

/-- If `Γ` charges both `(0, ∞)` and `(−∞, 0)`, the additive monoid generated by its support is
the group `H` it generates. -/
theorem rw_monoid_eq_group {Γ : ℤ → ℝ≥0∞} {a b : ℤ} (ha : 0 < a) (hΓa : Γ a ≠ 0) (hb : b < 0)
    (hΓb : Γ b ≠ 0) {h : ℤ} (hh : h ∈ rwSupportGroup Γ) :
    h ∈ AddSubmonoid.closure {k | Γ k ≠ 0} := by
  set M := AddSubmonoid.closure {k : ℤ | Γ k ≠ 0}
  have hmul : ∀ (n : ℕ) {g : ℤ}, g ∈ M → (n : ℤ) * g ∈ M := fun n g hg => by
    rw [← nsmul_eq_mul]
    exact AddSubmonoid.nsmul_mem _ hg n
  have haM : a ∈ M := AddSubmonoid.subset_closure hΓa
  have hbM : b ∈ M := AddSubmonoid.subset_closure hΓb
  have hnegA : -a ∈ M := by
    have : -a = ((-b - 1).toNat : ℤ) * a + (a.toNat : ℤ) * b := by
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg ha.le]
      ring
    rw [this]
    exact add_mem (hmul _ haM) (hmul _ hbM)
  have hzmul : ∀ k : ℤ, k * a ∈ M := fun k => by
    rcases le_or_gt 0 k with hk | hk
    · rw [← Int.toNat_of_nonneg hk]
      exact hmul _ haM
    · have : k * a = ((-k).toNat : ℤ) * (-a) := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [this]
      exact hmul _ hnegA
  have hneg : ∀ g ∈ M, -g ∈ M := fun g hg => by
    induction hg using AddSubmonoid.closure_induction with
    | mem g _ =>
      have : -g = ((a - 1).toNat : ℤ) * g + (-g) * a := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [this]
      exact add_mem (hmul _ (AddSubmonoid.subset_closure (by assumption))) (hzmul _)
    | zero => simp
    | add x y _ _ hx hy => rw [neg_add]; exact add_mem hx hy
  induction hh using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubmonoid.subset_closure hx
  | zero => exact M.zero_mem
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact hneg x hx

/-- MT p. 81: if `Γ(−∞, 0) > 0` and `Γ(0, ∞) > 0`, the communicating class of `x` is the coset
`x + H`: the chain is irreducible on each `D_r`. -/
theorem rw_commClass_eq {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwMatrix Γ))] {a b : ℤ}
    (ha : 0 < a) (hΓa : Γ a ≠ 0) (hb : b < 0) (hΓb : Γ b ≠ 0) (x : ℤ) :
    commClass (matKernel (rwMatrix Γ)) x = {y | y - x ∈ rwSupportGroup Γ} := by
  ext y
  constructor
  · intro h
    exact (rw_coset_isAbsorbing x).mem_of_leads (by simp) h.1
  · intro h
    have h1 := rw_leads_add (rw_monoid_eq_group ha hΓa hb hΓb h) x
    have h2 := rw_leads_add (rw_monoid_eq_group ha hΓa hb hΓb (neg_mem h)) y
    rw [add_sub_cancel] at h1
    rw [neg_sub, add_sub_cancel] at h2
    exact ⟨h1, h2⟩

/-- MT p. 81: if `Γ(−∞, 0) > 0` and `Γ(0, ∞) > 0`, the walk on `ℤ` has finitely many
communicating classes: with `H = dℤ`, `d ≥ 1`, each class is the class of some `r < d`. -/
theorem rw_commClass_finite {Γ : ℤ → ℝ≥0∞} [IsMarkovKernel (matKernel (rwMatrix Γ))] {a b : ℤ}
    (ha : 0 < a) (hΓa : Γ a ≠ 0) (hb : b < 0) (hΓb : Γ b ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ ∀ x : ℤ, ∃ r : ℕ, r < d ∧
      commClass (matKernel (rwMatrix Γ)) x = commClass (matKernel (rwMatrix Γ)) r := by
  obtain ⟨d, hd⟩ := rw_closure_eq_zmultiples Γ
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · have : a ∈ rwSupportGroup Γ := AddSubgroup.subset_closure hΓa
      rw [hd, h, Nat.cast_zero, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] at this
      omega
    · exact h
  refine ⟨d, hd0, fun x => ⟨(x % d).toNat, ?_, ?_⟩⟩
  · have := Int.emod_lt_of_pos x (Int.natCast_pos.2 hd0)
    omega
  · rw [commClass_eq_iff, rw_commClass_eq ha hΓa hb hΓb, mem_ofPred_eq, hd,
      Int.toNat_of_nonneg (Int.emod_nonneg x (by omega)), AddSubgroup.mem_zmultiples_iff]
    refine ⟨-(x / d), ?_⟩
    rw [smul_eq_mul, Int.emod_def]
    ring

/-! ### Random walk on `ℚ` with integer increments (§4.1.3) -/

/-- The class `q + ℤ` of a rational `q`. -/
def ratClass (q : ℚ) : Set ℚ := {r | ∃ n : ℤ, r = q + n}

/-- MT p. 81: for the walk on `ℚ` with increments in `ℤ`, `q + ℤ` is absorbing. -/
theorem ratWalk_isAbsorbing {Γ : ℚ → ℝ≥0∞} [IsMarkovKernel (matKernel (arMatrix 1 Γ))]
    (hΓ : ∀ q, Γ q ≠ 0 ↔ ∃ n : ℤ, q = n) (q : ℚ) :
    IsAbsorbing (matKernel (arMatrix 1 Γ)) (ratClass q) := by
  rw [isAbsorbing_matKernel_iff]
  rintro r ⟨m, rfl⟩ s hs
  by_contra h
  obtain ⟨n, hn⟩ := (hΓ _).1 h
  exact hs ⟨m + n, by push_cast; rw [arMatrix, one_mul] at *; linarith⟩

/-- MT p. 81: if `Γ(n) > 0` for every integer `n`, the communicating class of `q` is `q + ℤ`,
which is absorbing and irreducible. -/
theorem ratWalk_commClass_eq {Γ : ℚ → ℝ≥0∞} [IsMarkovKernel (matKernel (arMatrix 1 Γ))]
    (hΓ : ∀ q, Γ q ≠ 0 ↔ ∃ n : ℤ, q = n) (q : ℚ) :
    commClass (matKernel (arMatrix 1 Γ)) q = ratClass q := by
  ext r
  constructor
  · intro h
    exact (ratWalk_isAbsorbing hΓ q).mem_of_leads ⟨0, by simp⟩ h.1
  · rintro ⟨n, rfl⟩
    refine ⟨leads_of_pos ((hΓ _).2 ⟨n, by simp⟩),
      leads_of_pos ((hΓ _).2 ⟨-n, by simp⟩)⟩

/-- MT p. 81: the walk on `ℚ` with integer increments has infinitely many (countably many)
absorbing irreducible classes. -/
theorem ratWalk_commClass_infinite {Γ : ℚ → ℝ≥0∞} [IsMarkovKernel (matKernel (arMatrix 1 Γ))]
    (hΓ : ∀ q, Γ q ≠ 0 ↔ ∃ n : ℤ, q = n) :
    (range (commClass (matKernel (arMatrix 1 Γ)))).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => commClass (matKernel (arMatrix 1 Γ)) (1 / ((k : ℚ) + 2)))
    (fun k j hkj => ?_) fun k => mem_range_self _
  simp only at hkj
  have hmem := hkj ▸ mem_commClass_self (matKernel (arMatrix 1 Γ)) (1 / ((j : ℚ) + 2))
  rw [ratWalk_commClass_eq hΓ] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hk1 : 0 < 1 / ((k : ℚ) + 2) := by positivity
  have hj1 : 0 < 1 / ((j : ℚ) + 2) := by positivity
  have hk2 : 1 / ((k : ℚ) + 2) ≤ 1 / 2 := by
    gcongr
    linarith [(Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
  have hj2 : 1 / ((j : ℚ) + 2) ≤ 1 / 2 := by
    gcongr
    linarith [(Nat.cast_nonneg j : (0 : ℚ) ≤ j)]
  have hn1 : (n : ℚ) < 1 := by linarith
  have hn2 : (-1 : ℚ) < n := by linarith
  have hn0 : n = 0 := by
    have h1 : n < 1 := by exact_mod_cast hn1
    have h2 : -1 < n := by exact_mod_cast hn2
    omega
  rw [hn0, Int.cast_zero, add_zero] at hn
  have : (j : ℚ) + 2 = k + 2 := by
    have h := hn
    field_simp at h
    linarith
  exact_mod_cast (by linarith : (k : ℚ) = j)

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minorization and the Nummelin splitting (MT §5.1.1)

Meyn and Tweedie, §5.1.1, pp. 98–100, and (5.10), p. 101. The split space is `X̌ = X × Bool`:
`X₀ = X × {false}` is the "top" copy of `X` and `X₁ = X × {true}` the "bottom" copy.

* `Minorization P` (5.2): a measurable set `C`, a constant `0 < δ < 1` and a probability
  measure `ν` with `P(x, ·) ≥ δ ν` for `x ∈ C`. `Minorization.IsConcentrated`: the book's extra
  requirement `ν(Cᶜ) = 0`; `Minorization.ofLe`: any bound `P(x, ·) ≥ ν'` on `C` with
  `0 < ν'(C) < ∞` gives a concentrated minorization.
* `splitK`: the kernel `x ↦ (1 − r(x)) δ_{(x,0)} + r(x) δ_{(x,1)}`, `r = δ 1_C`, which tosses the
  `δ`-coin; `split μ = μ*` (5.3) is `splitK ∘ₘ μ`. `split_apply_false`, `split_apply_true` are
  (5.3); `split_fst_preimage`, `split_map_fst` are the marginal identity (5.4); `split_add`,
  `split_smul`, `split_sub` express that `μ ↦ μ*` is linear.
* `resid`: the residual kernel `R(x, ·) = (1 − δ)⁻¹ (P(x, ·) − δν)` on `C` and `P(x, ·)` off `C`;
  it is a transition kernel (`isMarkovKernel_resid`): this is where (5.2) is used (p. 100).
* `baseK`: the kernel `Q(x₀, ·) = R(x, ·)`, `Q(x₁, ·) = ν`, and the split kernel
  `splitKernel = P̌ = splitK ∘ₖ baseK`: first move by `Q`, then toss the coin. This is (5.5)–(5.7)
  (`splitKernel_apply_false_of_notMem`, `splitKernel_apply_false_of_mem`,
  `splitKernel_apply_true`).
* `baseK_comp_splitK`: the factorisation `Q ∘ₖ splitK = P`, the heart of the construction.
* (5.10) `split_comp_splitKernel`: `μ* P̌ = (μP)*`, and `split_comp_splitKernel_pow`:
  `μ* P̌ⁿ = (μPⁿ)*`; `splitKernel_pow_succ`: `P̌ⁿ⁺¹ = splitK ∘ₖ Pⁿ ∘ₖ Q`.
* **Theorem 5.1.3 (i)** in the form (5.9) (`theorem_5_1_3_i`, p. 100):
  `∫ λ(dx) Pᵏ(x, A) = ∫ λ*(dy) P̌ᵏ(y, A₀ ∪ A₁)`.
* The atoms (p. 100): `isAtom_bottom` (`X₁` is an atom with `P̌(x₁, ·) = ν*`),
  `isAtom_checkAlpha` (`α̌ = C₁`, (5.8)), `splitKernel_pow_bottom_compl` (`P̌ⁿ(xᵢ, X₁ \ C₁) = 0`
  for `n ≥ 1`) and `split_bottom` (`φ*(X₁) = δ φ(C)`).

**Corrections.** The book allows `δ = 1` in (5.2), when (5.6) divides by `0`; the structure here
requires `δ < 1`, which costs nothing (`Minorization.ofLe` uses `δ ≤ 1/2`). The book requires
`ν(Cᶜ) = 0`; the construction and Theorem 5.1.3 do not need it, and it is kept as the separate
hypothesis `IsConcentrated` where it matters.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

variable (P : Kernel X X) in
/-- The **minorization condition** (5.2), MT p. 98: a measurable set `C`, a constant
`0 < δ < 1` and a probability measure `ν` with `P(x, A) ≥ δ ν(A)` for every `x ∈ C`. -/
structure Minorization where
  /-- The set `C` on which the chain is split. -/
  C : Set X
  /-- The constant `δ`. -/
  δ : ℝ≥0∞
  /-- The minorizing probability measure `ν`. -/
  ν : Measure X
  /-- `C` is measurable. -/
  measurableSet_C : MeasurableSet C
  /-- `δ > 0`. -/
  δ_pos : 0 < δ
  /-- `δ < 1`. -/
  δ_lt_one : δ < 1
  /-- `ν` is a probability measure. -/
  isProbabilityMeasure_ν : IsProbabilityMeasure ν
  /-- `P(x, ·) ≥ δ ν` for `x ∈ C`. -/
  le : ∀ x ∈ C, δ • ν ≤ P x

namespace Minorization

variable {P : Kernel X X}

/-- The book's normalisation in (5.2): `ν(Cᶜ) = 0`. -/
def IsConcentrated (M : Minorization P) : Prop := M.ν M.Cᶜ = 0

/-- `δ ≠ ∞`. -/
theorem δ_ne_top (M : Minorization P) : M.δ ≠ ∞ := (M.δ_lt_one.trans ENNReal.one_lt_top).ne

/-- `1 − δ ≠ 0`. -/
theorem one_sub_δ_ne_zero (M : Minorization P) : 1 - M.δ ≠ 0 :=
  (tsub_pos_of_lt M.δ_lt_one).ne'

/-- `δ ν` is a finite measure. -/
theorem isFiniteMeasure_smul_ν (M : Minorization P) : IsFiniteMeasure (M.δ • M.ν) := by
  have := M.isProbabilityMeasure_ν
  exact ⟨by simp [M.δ_ne_top.lt_top]⟩

/-- (5.2) on sets: `P(x, A) ≥ δ ν(A)` for `x ∈ C`. -/
theorem le_apply (M : Minorization P) {x : X} (hx : x ∈ M.C) (A : Set X) :
    M.δ * M.ν A ≤ P x A := by
  have := M.le x hx A
  rwa [Measure.smul_apply, smul_eq_mul] at this

/-- A minorization from any bound `P(x, ·) ≥ ν'` on `C` with `0 < ν'(C) < ∞`: take
`δ = min(ν'(C), 1/2)` and `ν = ν'(· ∩ C)/ν'(C)`. -/
noncomputable def ofLe {C : Set X} (hC : MeasurableSet C) {ν' : Measure X}
    (hle : ∀ x ∈ C, ν' ≤ P x) (hpos : 0 < ν' C) (hfin : ν' C ≠ ∞) : Minorization P where
  C := C
  δ := min (ν' C) 2⁻¹
  ν := (ν' C)⁻¹ • ν'.restrict C
  measurableSet_C := hC
  δ_pos := lt_min hpos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
  δ_lt_one := (min_le_right _ _).trans_lt (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  isProbabilityMeasure_ν := ⟨by
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
      ENNReal.inv_mul_cancel hpos.ne' hfin]⟩
  le x hx := by
    refine Measure.le_intro fun A hA _ => ?_
    rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    calc min (ν' C) 2⁻¹ * (ν' C)⁻¹ * ν' (A ∩ C) ≤ 1 * ν' (A ∩ C) := by
          gcongr
          calc min (ν' C) 2⁻¹ * (ν' C)⁻¹ ≤ ν' C * (ν' C)⁻¹ := by gcongr; exact min_le_left _ _
            _ = 1 := ENNReal.mul_inv_cancel hpos.ne' hfin
      _ ≤ P x A := by rw [one_mul]; exact (measure_mono inter_subset_left).trans (hle x hx A)

/-- The minorization `ofLe` lives on the given set. -/
theorem ofLe_C {C : Set X} (hC : MeasurableSet C) {ν' : Measure X} (hle : ∀ x ∈ C, ν' ≤ P x)
    (hpos : 0 < ν' C) (hfin : ν' C ≠ ∞) : (ofLe hC hle hpos hfin).C = C := rfl

/-- The minorization `ofLe` satisfies the book's normalisation `ν(Cᶜ) = 0`. -/
theorem ofLe_isConcentrated {C : Set X} (hC : MeasurableSet C) {ν' : Measure X}
    (hle : ∀ x ∈ C, ν' ≤ P x) (hpos : 0 < ν' C) (hfin : ν' C ≠ ∞) :
    (ofLe hC hle hpos hfin).IsConcentrated := by
  change ((ν' C)⁻¹ • ν'.restrict C) Cᶜ = 0
  rw [Measure.smul_apply, Measure.restrict_apply hC.compl, compl_inter_self, measure_empty,
    smul_zero]

/-! ### The coin and the split of a measure -/

/-- The coin probability `r(x) = δ 1_C(x)`: the probability that the split chain drops to the
bottom level on arriving at `x`. -/
noncomputable def splitProb (M : Minorization P) (x : X) : ℝ≥0∞ := M.C.indicator (fun _ => M.δ) x

/-- `r` is measurable. -/
theorem measurable_splitProb (M : Minorization P) : Measurable M.splitProb :=
  measurable_const.indicator M.measurableSet_C

/-- `r(x) ≤ δ`. -/
theorem splitProb_le (M : Minorization P) (x : X) : M.splitProb x ≤ M.δ := by
  unfold splitProb
  by_cases hx : x ∈ M.C <;> simp [hx]

/-- `r(x) ≤ 1`. -/
theorem splitProb_le_one (M : Minorization P) (x : X) : M.splitProb x ≤ 1 :=
  (M.splitProb_le x).trans M.δ_lt_one.le

/-- `r(x) = δ` on `C`. -/
theorem splitProb_of_mem (M : Minorization P) {x : X} (hx : x ∈ M.C) : M.splitProb x = M.δ := by
  simp [splitProb, hx]

/-- `r(x) = 0` off `C`. -/
theorem splitProb_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) : M.splitProb x = 0 := by
  simp [splitProb, hx]

/-- The coin measure `(1 − r(x)) δ_{(x,0)} + r(x) δ_{(x,1)}` on `X × Bool`. -/
noncomputable def splitMeas (M : Minorization P) (x : X) : Measure (X × Bool) :=
  (1 - M.splitProb x) • Measure.dirac (x, false) + M.splitProb x • Measure.dirac (x, true)

/-- The coin measure of a measurable set. -/
theorem splitMeas_apply (M : Minorization P) (x : X) {s : Set (X × Bool)} (hs : MeasurableSet s) :
    M.splitMeas x s = (1 - M.splitProb x) * s.indicator 1 (x, false) +
      M.splitProb x * s.indicator 1 (x, true) := by
  simp [splitMeas, Measure.dirac_apply' _ hs]

/-- The coin kernel `splitK : X → X × Bool`. -/
noncomputable def splitK (M : Minorization P) : Kernel X (X × Bool) where
  toFun := M.splitMeas
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [M.splitMeas_apply _ hs]
    have h0 : Measurable fun x : X => s.indicator (1 : X × Bool → ℝ≥0∞) (x, false) :=
      (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
    have h1 : Measurable fun x : X => s.indicator (1 : X × Bool → ℝ≥0∞) (x, true) :=
      (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
    exact ((measurable_const.sub M.measurable_splitProb).mul h0).add
      (M.measurable_splitProb.mul h1)

/-- `splitK x = (1 − r(x)) δ_{(x,0)} + r(x) δ_{(x,1)}`. -/
theorem splitK_apply (M : Minorization P) (x : X) : M.splitK x = M.splitMeas x := rfl

/-- The coin kernel is Markov. -/
theorem isMarkovKernel_splitK (M : Minorization P) : IsMarkovKernel M.splitK := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [splitK_apply, M.splitMeas_apply x MeasurableSet.univ]
  simp [tsub_add_cancel_of_le (M.splitProb_le_one x)]

/-- `∫ f d(splitK x) = (1 − r(x)) f(x, 0) + r(x) f(x, 1)`. -/
theorem lintegral_splitK (M : Minorization P) (x : X) {f : X × Bool → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂M.splitK x = (1 - M.splitProb x) * f (x, false) + M.splitProb x * f (x, true) := by
  rw [splitK_apply, splitMeas, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac' _ hf, lintegral_dirac' _ hf, smul_eq_mul,
    smul_eq_mul]

/-- The **split measure** `μ*` of (5.3), MT p. 99: `μ* = splitK ∘ₘ μ`. -/
noncomputable def split (M : Minorization P) (μ : Measure X) : Measure (X × Bool) := M.splitK ∘ₘ μ

/-- `μ*(s) = ∫ μ(dx) [(1 − r(x)) 1_s(x, 0) + r(x) 1_s(x, 1)]`. -/
theorem split_apply (M : Minorization P) (μ : Measure X) {s : Set (X × Bool)}
    (hs : MeasurableSet s) :
    M.split μ s = ∫⁻ x, (1 - M.splitProb x) * s.indicator 1 (x, false) +
      M.splitProb x * s.indicator 1 (x, true) ∂μ := by
  rw [split, Measure.bind_apply hs M.splitK.aemeasurable]
  exact lintegral_congr fun x => M.splitMeas_apply x hs

/-- `∫ f dμ* = ∫ μ(dx) [(1 − r(x)) f(x, 0) + r(x) f(x, 1)]`. -/
theorem lintegral_split (M : Minorization P) (μ : Measure X) {f : X × Bool → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂M.split μ =
      ∫⁻ x, (1 - M.splitProb x) * f (x, false) + M.splitProb x * f (x, true) ∂μ := by
  rw [split, Measure.lintegral_bind M.splitK.aemeasurable hf.aemeasurable]
  exact lintegral_congr fun x => M.lintegral_splitK x hf

/-- **(5.3), top level**: `μ*(A₀) = (1 − δ) μ(A ∩ C) + μ(A ∩ Cᶜ)`. -/
theorem split_apply_false (M : Minorization P) (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    M.split μ (A ×ˢ {false}) = (1 - M.δ) * μ (A ∩ M.C) + μ (A ∩ M.Cᶜ) := by
  rw [M.split_apply μ (hA.prod (measurableSet_singleton false))]
  have hfun : (fun x => (1 - M.splitProb x) * (A ×ˢ {false}).indicator (1 : X × Bool → ℝ≥0∞)
      (x, false) + M.splitProb x * (A ×ˢ {false}).indicator 1 (x, true)) =
      fun x => (A ∩ M.C).indicator (fun _ => 1 - M.δ) x + (A ∩ M.Cᶜ).indicator 1 x := by
    ext x
    by_cases hx : x ∈ A <;> by_cases hc : x ∈ M.C <;>
      simp [hx, hc, M.splitProb_of_mem, M.splitProb_of_notMem, indicator]
  rw [hfun, lintegral_add_left (measurable_const.indicator (hA.inter M.measurableSet_C)),
    lintegral_indicator_const (hA.inter M.measurableSet_C),
    lintegral_indicator_one (hA.inter M.measurableSet_C.compl)]

/-- **(5.3), bottom level**: `μ*(A₁) = δ μ(A ∩ C)`. -/
theorem split_apply_true (M : Minorization P) (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    M.split μ (A ×ˢ {true}) = M.δ * μ (A ∩ M.C) := by
  rw [M.split_apply μ (hA.prod (measurableSet_singleton true))]
  have hfun : (fun x => (1 - M.splitProb x) * (A ×ˢ {true}).indicator (1 : X × Bool → ℝ≥0∞)
      (x, false) + M.splitProb x * (A ×ˢ {true}).indicator 1 (x, true)) =
      (A ∩ M.C).indicator (fun _ => M.δ) := by
    ext x
    by_cases hx : x ∈ A <;> by_cases hc : x ∈ M.C <;>
      simp [hx, hc, M.splitProb_of_mem, M.splitProb_of_notMem, indicator]
  rw [hfun, lintegral_indicator_const (hA.inter M.measurableSet_C)]

/-- The bottom level: `φ*(X₁) = δ φ(C)` (MT p. 100). -/
theorem split_bottom (M : Minorization P) (μ : Measure X) :
    M.split μ (univ ×ˢ {true}) = M.δ * μ M.C := by
  rw [M.split_apply_true μ MeasurableSet.univ, univ_inter]

/-- **(5.4)**: `μ*(A₀ ∪ A₁) = μ(A)`, where `A₀ ∪ A₁ = A × Bool`. -/
theorem split_fst_preimage (M : Minorization P) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : M.split μ (Prod.fst ⁻¹' A) = μ A := by
  rw [M.split_apply μ (measurable_fst hA)]
  have hfun : (fun x => (1 - M.splitProb x) * (Prod.fst ⁻¹' A).indicator
      (1 : X × Bool → ℝ≥0∞) (x, false) + M.splitProb x * (Prod.fst ⁻¹' A).indicator 1 (x, true))
      = A.indicator 1 := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx, tsub_add_cancel_of_le (M.splitProb_le_one x)]
  rw [hfun, lintegral_indicator_one hA]

/-- (5.4) as an identity of measures: the marginal of `μ*` on `X` is `μ`. -/
theorem split_map_fst (M : Minorization P) (μ : Measure X) : (M.split μ).map Prod.fst = μ := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, M.split_fst_preimage μ hA]

/-- `μ*(X̌) = μ(X)`. -/
theorem split_univ (M : Minorization P) (μ : Measure X) : M.split μ univ = μ univ := by
  rw [← preimage_univ (f := (Prod.fst : X × Bool → X)), M.split_fst_preimage μ MeasurableSet.univ]

/-- `μ*` is a probability measure when `μ` is. -/
theorem isProbabilityMeasure_split (M : Minorization P) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (M.split μ) :=
  ⟨by rw [M.split_univ, measure_univ]⟩

/-- Splitting is additive: `(μ + ρ)* = μ* + ρ*`. -/
theorem split_add (M : Minorization P) (μ ρ : Measure X) :
    M.split (μ + ρ) = M.split μ + M.split ρ :=
  Measure.comp_add

/-- Splitting is homogeneous: `(c μ)* = c μ*`. -/
theorem split_smul (M : Minorization P) (c : ℝ≥0∞) (μ : Measure X) :
    M.split (c • μ) = c • M.split μ :=
  Measure.comp_smul c

/-- Splitting commutes with subtraction: `(μ − ρ)*(s) = μ*(s) − ρ*(s)` for `ρ ≤ μ`, `ρ` finite. -/
theorem split_sub (M : Minorization P) {μ ρ : Measure X} [IsFiniteMeasure ρ] (h : ρ ≤ μ)
    (s : Set (X × Bool)) : M.split (μ - ρ) s = M.split μ s - M.split ρ s := by
  have hfin : M.split ρ s ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ s))
    rw [M.split_univ]
    exact measure_ne_top ρ univ
  have hadd : M.split (μ - ρ) + M.split ρ = M.split μ := by
    rw [← M.split_add, Measure.sub_add_cancel_of_le h]
  rw [← hadd, Measure.add_apply, ENNReal.add_sub_cancel_right hfin]

/-- Splitting commutes with restriction to a cylinder: `μ*` restricted to `A × Bool` is
`(μ restricted to A)*`. -/
theorem split_restrict_fst (M : Minorization P) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) :
    (M.split μ).restrict (Prod.fst ⁻¹' A) = M.split (μ.restrict A) := by
  ext s hs
  rw [Measure.restrict_apply hs, M.split_apply _ (hs.inter (measurable_fst hA)),
    M.split_apply _ hs, ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · have h1 : ∀ b : Bool, (s ∩ Prod.fst ⁻¹' A).indicator (1 : X × Bool → ℝ≥0∞) (x, b) =
        s.indicator 1 (x, b) := fun b => by
      by_cases hb : (x, b) ∈ s <;> simp [hb, hx]
    simp [hx, h1]
  · have h1 : ∀ b : Bool, (s ∩ Prod.fst ⁻¹' A).indicator (1 : X × Bool → ℝ≥0∞) (x, b) = 0 :=
      fun b => by simp [hx]
    simp [hx]

/-! ### The residual kernel and the split kernel -/

/-- The residual measure `R(x, ·)`: `(1 − δ)⁻¹ (P(x, ·) − δ ν)` on `C` (5.6) and `P(x, ·)` off
`C` (5.5). -/
noncomputable def residMeas (M : Minorization P) (x : X) : Measure X := by
  classical
  exact if x ∈ M.C then (1 - M.δ)⁻¹ • (P x - M.δ • M.ν) else P x

/-- `R(x, A) = (1 − δ)⁻¹ (P(x, A) − δ ν(A))` on `C`. -/
theorem residMeas_apply_of_mem (M : Minorization P) {x : X} (hx : x ∈ M.C) {A : Set X}
    (hA : MeasurableSet A) :
    M.residMeas x A = (1 - M.δ)⁻¹ * (P x A - M.δ * M.ν A) := by
  have := M.isFiniteMeasure_smul_ν
  simp [residMeas, hx, Measure.sub_apply hA (M.le x hx)]

/-- `R(x, ·) = P(x, ·)` off `C`. -/
theorem residMeas_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) :
    M.residMeas x = P x := by
  simp [residMeas, hx]

/-- The residual kernel `R`. -/
noncomputable def resid (M : Minorization P) : Kernel X X where
  toFun := M.residMeas
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    classical
    have hfun : (fun x => M.residMeas x A) = fun x =>
        if x ∈ M.C then (1 - M.δ)⁻¹ * (P x A - M.δ * M.ν A) else P x A := by
      ext x
      by_cases hx : x ∈ M.C
      · simp only [hx, ite_true]
        exact M.residMeas_apply_of_mem hx hA
      · simp only [hx, ite_false]
        rw [M.residMeas_of_notMem hx]
    rw [hfun]
    exact Measurable.ite M.measurableSet_C
      (measurable_const.mul ((Kernel.measurable_coe P hA).sub measurable_const))
      (Kernel.measurable_coe P hA)

/-- `R(x, ·) = residMeas x`. -/
theorem resid_apply (M : Minorization P) (x : X) : M.resid x = M.residMeas x := rfl

/-- The residual kernel is a transition kernel (MT p. 100: "(5.6) is always non-negative"). -/
theorem isMarkovKernel_resid (M : Minorization P) [IsMarkovKernel P] :
    IsMarkovKernel M.resid := by
  have := M.isProbabilityMeasure_ν
  refine ⟨fun x => ⟨?_⟩⟩
  rw [resid_apply]
  by_cases hx : x ∈ M.C
  · rw [M.residMeas_apply_of_mem hx MeasurableSet.univ, measure_univ, measure_univ, mul_one,
      ENNReal.inv_mul_cancel M.one_sub_δ_ne_zero (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  · rw [M.residMeas_of_notMem hx, measure_univ]

/-- The measure `Q(z, ·)`: `ν` on the bottom level and `R(x, ·)` on the top level. -/
noncomputable def baseMeas (M : Minorization P) (z : X × Bool) : Measure X :=
  if z.2 then M.ν else M.resid z.1

/-- The kernel `Q : X̌ → X`. -/
noncomputable def baseK (M : Minorization P) : Kernel (X × Bool) X where
  toFun := M.baseMeas
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have hfun : (fun z => M.baseMeas z A) = fun z : X × Bool =>
        if z.2 = true then M.ν A else M.resid z.1 A := by
      ext z
      cases h : z.2 <;> simp [baseMeas, h]
    rw [hfun]
    exact Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
      ((Kernel.measurable_coe _ hA).comp measurable_fst)

/-- `Q(x₀, ·) = R(x, ·)`. -/
theorem baseK_apply_false (M : Minorization P) (x : X) : M.baseK (x, false) = M.resid x := by
  change M.baseMeas (x, false) = _
  simp [baseMeas]

/-- `Q(x₁, ·) = ν`. -/
theorem baseK_apply_true (M : Minorization P) (x : X) : M.baseK (x, true) = M.ν := by
  change M.baseMeas (x, true) = _
  simp [baseMeas]

/-- `Q` is a transition kernel. -/
theorem isMarkovKernel_baseK (M : Minorization P) [IsMarkovKernel P] : IsMarkovKernel M.baseK := by
  have := M.isProbabilityMeasure_ν
  have := M.isMarkovKernel_resid
  refine ⟨fun z => ?_⟩
  obtain ⟨x, b⟩ := z
  cases b
  · rw [baseK_apply_false]; infer_instance
  · rw [baseK_apply_true]; infer_instance

/-- **The factorisation** `Q ∘ₖ splitK = P`: tossing the coin at `x` and then moving by `Q`
is the same as moving by `P`. On `C`, `(1 − δ) R(x, ·) + δ ν = P(x, ·)`. -/
theorem baseK_comp_splitK (M : Minorization P) : M.baseK ∘ₖ M.splitK = P := by
  have := M.isFiniteMeasure_smul_ν
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA, M.lintegral_splitK x (Kernel.measurable_coe _ hA),
    baseK_apply_false, baseK_apply_true,
    resid_apply]
  by_cases hx : x ∈ M.C
  · rw [M.residMeas_apply_of_mem hx hA, M.splitProb_of_mem hx, ← mul_assoc,
      ENNReal.mul_inv_cancel M.one_sub_δ_ne_zero (ENNReal.sub_ne_top ENNReal.one_ne_top), one_mul,
      tsub_add_cancel_of_le (M.le_apply hx A)]
  · rw [M.residMeas_of_notMem hx, M.splitProb_of_notMem hx]
    simp

/-- The **split kernel** `P̌ = splitK ∘ₖ Q` (5.5)–(5.7), MT p. 99: from `xᵢ`, move to `y` by
`Q(xᵢ, ·)` and then toss the `δ`-coin at `y`. -/
noncomputable def splitKernel (M : Minorization P) : Kernel (X × Bool) (X × Bool) :=
  M.splitK ∘ₖ M.baseK

/-- `P̌(z, ·) = Q(z, ·)*`. -/
theorem splitKernel_apply (M : Minorization P) (z : X × Bool) :
    M.splitKernel z = M.split (M.baseK z) := by
  rw [splitKernel, Kernel.comp_apply]
  rfl

/-- The split kernel is a transition kernel. -/
theorem isMarkovKernel_splitKernel (M : Minorization P) [IsMarkovKernel P] :
    IsMarkovKernel M.splitKernel := by
  have := M.isMarkovKernel_baseK
  have := M.isMarkovKernel_splitK
  unfold splitKernel
  infer_instance

/-- **(5.5)**: `P̌(x₀, ·) = P(x, ·)*` for `x ∉ C`. -/
theorem splitKernel_apply_false_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) :
    M.splitKernel (x, false) = M.split (P x) := by
  rw [splitKernel_apply, baseK_apply_false, resid_apply, M.residMeas_of_notMem hx]

/-- **(5.6)**: `P̌(x₀, ·) = (1 − δ)⁻¹ [P(x, ·)* − δ ν*]` for `x ∈ C`. -/
theorem splitKernel_apply_false_of_mem (M : Minorization P) {x : X} (hx : x ∈ M.C)
    (s : Set (X × Bool)) :
    M.splitKernel (x, false) s = (1 - M.δ)⁻¹ * (M.split (P x) s - M.δ * M.split M.ν s) := by
  have := M.isFiniteMeasure_smul_ν
  rw [splitKernel_apply, baseK_apply_false, resid_apply]
  simp only [residMeas, hx, ite_true]
  rw [M.split_smul, Measure.smul_apply, smul_eq_mul, M.split_sub (M.le x hx), M.split_smul,
    Measure.smul_apply, smul_eq_mul]

/-- **(5.7)**: `P̌(x₁, ·) = ν*`. -/
theorem splitKernel_apply_true (M : Minorization P) (x : X) :
    M.splitKernel (x, true) = M.split M.ν := by
  rw [splitKernel_apply, baseK_apply_true]

/-- **(5.10)**, MT p. 101: `μ* P̌ = (μP)*`. -/
theorem split_comp_splitKernel (M : Minorization P) (μ : Measure X) :
    M.splitKernel ∘ₘ M.split μ = M.split (P ∘ₘ μ) := by
  rw [splitKernel, split, Measure.comp_assoc, Kernel.comp_assoc, baseK_comp_splitK,
    ← Measure.comp_assoc]
  rfl

/-- (5.10) iterated: `μ* P̌ⁿ = (μPⁿ)*`. -/
theorem split_comp_splitKernel_pow (M : Minorization P) (n : ℕ) (μ : Measure X) :
    (M.splitKernel ^ n : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split μ =
      M.split ((P ^ n : Kernel X X) ∘ₘ μ) := by
  induction n generalizing μ with
  | zero =>
    rw [pow_zero, pow_zero]
    change Kernel.id ∘ₘ _ = M.split (Kernel.id ∘ₘ μ)
    rw [Measure.id_comp, Measure.id_comp]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change ((M.splitKernel ^ n) ∘ₖ M.splitKernel) ∘ₘ _ = M.split (((P ^ n) ∘ₖ P) ∘ₘ μ)
    rw [← Measure.comp_assoc, split_comp_splitKernel, ih, Measure.comp_assoc]

/-- `P̌ⁿ⁺¹ = splitK ∘ₖ Pⁿ ∘ₖ Q`. -/
theorem splitKernel_pow_succ (M : Minorization P) (n : ℕ) :
    M.splitKernel ^ (n + 1) = M.splitK ∘ₖ ((P ^ n) ∘ₖ M.baseK) := by
  induction n with
  | zero =>
    rw [zero_add, pow_one, pow_zero]
    change _ = M.splitK ∘ₖ (Kernel.id ∘ₖ M.baseK)
    rw [Kernel.id_comp]
    rfl
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    change (M.splitK ∘ₖ ((P ^ n) ∘ₖ M.baseK)) ∘ₖ (M.splitK ∘ₖ M.baseK) =
      M.splitK ∘ₖ (((P ^ n) ∘ₖ P) ∘ₖ M.baseK)
    rw [show M.splitK ∘ₖ ((P ^ n) ∘ₖ M.baseK) ∘ₖ (M.splitK ∘ₖ M.baseK) =
      M.splitK ∘ₖ ((P ^ n) ∘ₖ (M.baseK ∘ₖ M.splitK) ∘ₖ M.baseK) by simp only [Kernel.comp_assoc],
      baseK_comp_splitK]

/-- `P̌ⁿ⁺¹(z, ·) = (Q(z, ·) Pⁿ)*`. -/
theorem splitKernel_pow_succ_apply (M : Minorization P) (n : ℕ) (z : X × Bool) :
    (M.splitKernel ^ (n + 1)) z = M.split ((P ^ n : Kernel X X) ∘ₘ M.baseK z) := by
  rw [splitKernel_pow_succ, Kernel.comp_apply, Kernel.comp_apply]
  rfl

/-- **Theorem 5.1.3 (i)** in the form (5.9), MT p. 100: for every measure `λ` and measurable `A`,
`∫ λ(dx) Pᵏ(x, A) = ∫ λ*(dy) P̌ᵏ(y, A₀ ∪ A₁)`. -/
theorem theorem_5_1_3_i (M : Minorization P) (k : ℕ) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) :
    ∫⁻ x, (P ^ k) x A ∂μ = ∫⁻ z, (M.splitKernel ^ k) z (Prod.fst ⁻¹' A) ∂M.split μ := by
  rw [← measure_kernel_apply μ _ hA, ← Measure.bind_apply (measurable_fst hA)
    (Kernel.aemeasurable _)]
  rw [split_comp_splitKernel_pow, M.split_fst_preimage _ hA]

/-! ### The atoms of the split chain -/

/-- The bottom level `X₁` is an atom for the split chain, with `P̌(x₁, ·) = ν*` (MT p. 100). -/
theorem isAtom_bottom (M : Minorization P) : IsAtom M.splitKernel (univ ×ˢ {true}) :=
  ⟨MeasurableSet.univ.prod (measurableSet_singleton true), M.split M.ν, fun z hz => by
    obtain ⟨x, b⟩ := z
    simp only [mem_prod, mem_univ, mem_singleton_iff, true_and] at hz
    rw [hz, splitKernel_apply_true]⟩

/-- The atom `α̌ = C₁` of (5.8), MT p. 100. -/
def checkAlpha (M : Minorization P) : Set (X × Bool) := M.C ×ˢ {true}

/-- `α̌ = C₁` is measurable. -/
theorem measurableSet_checkAlpha (M : Minorization P) : MeasurableSet M.checkAlpha :=
  M.measurableSet_C.prod (measurableSet_singleton true)

/-- `α̌ = C₁` is an atom (5.8). -/
theorem isAtom_checkAlpha (M : Minorization P) : IsAtom M.splitKernel M.checkAlpha :=
  ⟨M.measurableSet_checkAlpha, M.split M.ν, fun z hz => by
    obtain ⟨x, b⟩ := z
    simp only [checkAlpha, mem_prod, mem_singleton_iff] at hz
    rw [hz.2, splitKernel_apply_true]⟩

/-- `μ*(X₁ \ C₁) = 0`: the split measures put no mass on the bottom level outside `C`. -/
theorem split_bottom_compl (M : Minorization P) (μ : Measure X) :
    M.split μ (M.Cᶜ ×ˢ {true}) = 0 := by
  rw [M.split_apply_true μ M.measurableSet_C.compl, compl_inter_self, measure_empty, mul_zero]

/-- MT p. 100: `P̌ⁿ(xᵢ, X₁ \ C₁) = 0` for every `n ≥ 1` and every `xᵢ`, so that `α̌ = C₁` is the
only part of the bottom level reached with positive probability. -/
theorem splitKernel_pow_bottom_compl (M : Minorization P) (n : ℕ) (z : X × Bool) :
    (M.splitKernel ^ (n + 1)) z (M.Cᶜ ×ˢ {true}) = 0 := by
  rw [splitKernel_pow_succ_apply, split_bottom_compl]

end Minorization

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Connecting the split and original chains (MT §5.1.2)

Meyn and Tweedie, §5.1.2, pp. 100–101. `M : Minorization P` is a minorization (5.2) and
`P̌ = M.splitKernel` the split kernel on `X̌ = X × Bool`.

* `lintegral_cylFn_split`: the finite-dimensional distributions of the first coordinate of the
  split chain started from `μ*` are those of the original chain started from `μ`, for every
  measure `μ`; the proof is an induction on the length of the cylinder, using (5.10) and the
  fact that splitting commutes with restriction to sets `A × Bool`.
* **Theorem 5.1.3 (i)**, path form (`theorem_5_1_3_i_path`, p. 100): the law of `(Φ̌ₙ.1)ₙ`
  under `P̌_{μ*}` is `P_μ`; `isMarkovChain_split_fst`: the first coordinate of the split chain is
  a Markov chain with kernel `P` and initial law `μ`; `lintegral_split_fst`: hence
  `E_μ[F(Φ)] = Ě_{μ*}[F(Φ̌.1)]` for every measurable `F ≥ 0` on path space, and in particular
  `E_λ[f(Φ_k)] = Ě_{λ*}[f(Φ̌_k)]` (`lintegral_split_coord`, p. 101).
* **Theorem 5.1.3 (ii)** (`theorem_5_1_3_ii`, p. 100): if `Φ̌` is `φ*`-irreducible then `Φ` is
  `φ`-irreducible (`isPhiIrreducible_of_split`); if `Φ` is `φ`-irreducible with `φ(C) > 0` then
  `Φ̌` is `ν*`-irreducible, every state reaches `α̌ = C₁`, and `α̌` is an accessible atom.
* `isPhiIrreducible_split` and `isPhiIrreducible_split_iff`: `Φ` is `φ`-irreducible iff `Φ̌` is
  `φ*`-irreducible, with no condition on `φ(C)`; `isMaximalIrreducibility_split`: if `ψ` is a
  maximal irreducibility measure for `Φ` then `ψ*` is one for `Φ̌`.

**Corrections.** None. Theorem 5.1.3 (ii) is stated by the book for the sets `C₁ ⊆ X₁`; the first
half holds for every minorization, the second needs `φ(C) > 0` as stated.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace Minorization

variable {P : Kernel X X}

/-! ### The finite-dimensional distributions of the marginal chain -/

/-- The cylinder functions of the split chain on the sets `Aᵢ × Bool` integrate against `μ*` to
the cylinder functions of the original chain against `μ`. -/
theorem lintegral_cylFn_split (M : Minorization P) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (μ : Measure X) :
    ∫⁻ z, cylFn M.splitKernel n (fun i => Prod.fst ⁻¹' A i) z ∂M.split μ =
      ∫⁻ x, cylFn P n A x ∂μ := by
  induction n generalizing A μ with
  | zero =>
    simp only [cylFn]
    rw [lintegral_indicator_one (measurable_fst (hA 0)), lintegral_indicator_one (hA 0),
      M.split_fst_preimage μ (hA 0)]
  | succ n ih =>
    simp only [cylFn]
    have hA' : ∀ i, MeasurableSet (A (i + 1)) := fun i => hA (i + 1)
    have hg := measurable_cylFn M.splitKernel n (A := fun i => Prod.fst ⁻¹' A (i + 1))
      fun i => measurable_fst (hA (i + 1))
    rw [lintegral_indicator (measurable_fst (hA 0)), lintegral_indicator (hA 0),
      M.split_restrict_fst μ (hA 0),
      ← Measure.lintegral_bind M.splitKernel.aemeasurable hg.aemeasurable]
    change ∫⁻ w, _ ∂(M.splitKernel ∘ₘ M.split (μ.restrict (A 0))) = _
    rw [split_comp_splitKernel, ih hA',
      Measure.lintegral_bind P.aemeasurable (measurable_cylFn P n hA').aemeasurable]

/-- **Theorem 5.1.3 (i)**, path form (MT p. 100): `Φ` is the marginal chain of `Φ̌`. The law of
the first coordinates `(Φ̌ₙ.1)ₙ` of the split chain started from `μ*` is the law `P_μ` of the
original chain. -/
theorem theorem_5_1_3_i_path (M : Minorization P) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := M.isMarkovKernel_splitKernel
    (pathMeasure M.splitKernel (M.split μ)).map (fun ω n => (ω n).1) = pathMeasure P μ := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split μ
  have := isProbabilityMeasure_pathMeasure M.splitKernel (M.split μ)
  have hπ : Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  have : IsProbabilityMeasure ((pathMeasure M.splitKernel (M.split μ)).map
      fun ω n => (ω n).1) := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  refine theorem_3_4_1_unique P μ _ fun n A hA => ?_
  rw [Measure.map_apply hπ (measurableSet_boxSet n hA)]
  have hpre : (fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1) ⁻¹' boxSet n A =
      boxSet n (fun i => Prod.fst ⁻¹' A i) := by
    ext ω; simp [boxSet]
  rw [hpre, pathMeasure_boxSet _ _ n fun i => measurable_fst (hA i),
    M.lintegral_cylFn_split n hA μ]

/-- The first coordinate of the split chain is a Markov chain with transition kernel `P` and
initial distribution `μ` (MT p. 96, (i)). -/
theorem isMarkovChain_split_fst (M : Minorization P) [IsMarkovKernel P] (μ : Measure X) :
    haveI := M.isMarkovKernel_splitKernel
    IsMarkovChain P μ (pathMeasure M.splitKernel (M.split μ)) (fun n ω => (ω n).1) := by
  have := M.isMarkovKernel_splitKernel
  refine ⟨fun n => measurable_fst.comp (measurable_pi_apply n), fun n A hA => ?_⟩
  have hpre : {ω : ℕ → X × Bool | ∀ i ≤ n, (ω i).1 ∈ A i} =
      boxSet n (fun i => Prod.fst ⁻¹' A i) := by
    ext ω; simp [boxSet]
  rw [hpre, pathMeasure_boxSet _ _ n fun i => measurable_fst (hA i),
    M.lintegral_cylFn_split n hA μ]

/-- `E_μ[F(Φ)] = Ě_{μ*}[F(Φ̌.1)]` for every measurable `F ≥ 0` on path space. -/
theorem lintegral_split_fst (M : Minorization P) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : (ℕ → X) → ℝ≥0∞} (hF : Measurable F) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ ω, F (fun n => (ω n).1) ∂pathMeasure M.splitKernel (M.split μ) =
      ∫⁻ ω, F ω ∂pathMeasure P μ := by
  have := M.isMarkovKernel_splitKernel
  have hπ : Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  rw [← M.theorem_5_1_3_i_path μ, lintegral_map hF hπ]

/-- MT p. 101: `E_λ[f(Φ_k)] = Ě_{λ*}[f(Φ̌_k)]` for `f` identical on the two copies of `X`. -/
theorem lintegral_split_coord (M : Minorization P) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (k : ℕ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ ω, f (ω k).1 ∂pathMeasure M.splitKernel (M.split μ) = ∫⁻ ω, f (ω k) ∂pathMeasure P μ :=
  M.lintegral_split_fst μ (F := fun ω => f (ω k)) (hf.comp (measurable_pi_apply k))

/-! ### Irreducibility of the split chain -/

/-- `μ*(A₀) ≥ (1 − δ) μ(A)`. -/
theorem one_sub_mul_le_split_false (M : Minorization P) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : (1 - M.δ) * μ A ≤ M.split μ (A ×ˢ {false}) := by
  rw [M.split_apply_false μ hA, ← measure_inter_add_sdiff A M.measurableSet_C, mul_add,
    sdiff_eq]
  gcongr
  exact mul_le_of_le_one_left' tsub_le_self

omit [MeasurableSpace X] in
/-- A set `s ⊆ X̌` is covered by `s₀ × {0} ∪ s₁ × {1}`, its two sections. -/
theorem subset_sections (s : Set (X × Bool)) :
    s ⊆ ((fun x => (x, false)) ⁻¹' s) ×ˢ {false} ∪ ((fun x => (x, true)) ⁻¹' s) ×ˢ {true} := by
  rintro ⟨x, b⟩ h
  cases b
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- If `μ*(s) > 0` then `μ(s₀) > 0` or `μ(s₁ ∩ C) > 0`. -/
theorem split_pos_cases (M : Minorization P) (μ : Measure X) {s : Set (X × Bool)}
    (hs : MeasurableSet s) (h : 0 < M.split μ s) :
    0 < μ ((fun x => (x, false)) ⁻¹' s) ∨ 0 < μ ((fun x => (x, true)) ⁻¹' s ∩ M.C) := by
  have h0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have h1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  by_contra hc
  push Not at hc
  have hle : M.split μ s ≤ 0 := by
    calc M.split μ s ≤ M.split μ (((fun x => (x, false)) ⁻¹' s) ×ˢ {false} ∪
          ((fun x => (x, true)) ⁻¹' s) ×ˢ {true}) := measure_mono (subset_sections s)
      _ ≤ M.split μ (((fun x => (x, false)) ⁻¹' s) ×ˢ {false}) +
          M.split μ (((fun x => (x, true)) ⁻¹' s) ×ˢ {true}) := measure_union_le _ _
      _ = 0 := by
        rw [M.split_apply_false μ h0, M.split_apply_true μ h1,
          measure_mono_null inter_subset_left (nonpos_iff_eq_zero.1 hc.1),
          measure_mono_null inter_subset_left (nonpos_iff_eq_zero.1 hc.1),
          nonpos_iff_eq_zero.1 hc.2]
        simp
  exact absurd h (not_lt.2 hle)

/-- **Theorem 5.1.3 (ii)**, first part (MT p. 100): if the split chain is `φ*`-irreducible, the
original chain is `φ`-irreducible. -/
theorem isPhiIrreducible_of_split (M : Minorization P) [IsMarkovKernel P] {φ : Measure X}
    (h : haveI := M.isMarkovKernel_splitKernel; IsPhiIrreducible M.splitKernel (M.split φ)) :
    IsPhiIrreducible P φ := by
  have := M.isMarkovKernel_splitKernel
  intro A hA hpos x
  have hA' : MeasurableSet (Prod.fst ⁻¹' A : Set (X × Bool)) := measurable_fst hA
  have h1 := h _ hA' (by rwa [M.split_fst_preimage φ hA]) (x, false)
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA' _).1 h1
  refine (hitProb_pos_iff P hA x).2 ⟨n, ?_⟩
  have h2 := M.theorem_5_1_3_i (n + 1) (Measure.dirac x) hA
  rw [lintegral_dirac' _ (Kernel.measurable_coe _ hA),
    M.lintegral_split _ (Kernel.measurable_coe _ hA'), lintegral_dirac'] at h2
  · rw [h2]
    refine lt_of_lt_of_le ?_ le_self_add
    refine ENNReal.mul_pos ?_ hn.ne'
    exact (tsub_pos_of_lt ((M.splitProb_le x).trans_lt M.δ_lt_one)).ne'
  · exact ((measurable_const.sub M.measurable_splitProb).mul
      ((Kernel.measurable_coe _ hA').comp (measurable_id.prodMk measurable_const))).add
      (M.measurable_splitProb.mul
        ((Kernel.measurable_coe _ hA').comp (measurable_id.prodMk measurable_const)))

/-- If the original chain is `φ`-irreducible, the split chain is `φ*`-irreducible. -/
theorem isPhiIrreducible_split (M : Minorization P) [IsMarkovKernel P] {φ : Measure X}
    (h : IsPhiIrreducible P φ) :
    haveI := M.isMarkovKernel_splitKernel; IsPhiIrreducible M.splitKernel (M.split φ) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_baseK
  intro s hs hpos z
  have hQ : M.baseK z ≠ 0 := IsProbabilityMeasure.ne_zero _
  have h0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have h1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  rw [hitProb_pos_iff _ hs]
  rcases M.split_pos_cases φ hs hpos with hc | hc
  · obtain ⟨m, hm⟩ := exists_pow_comp_pos h hQ h0 hc
    refine ⟨m + 1, ?_⟩
    rw [M.splitKernel_pow_succ_apply]
    refine lt_of_lt_of_le ?_ (measure_mono (show ((fun x => (x, false)) ⁻¹' s) ×ˢ
      ({false} : Set Bool) ⊆ s from prod_subset_iff.2 fun x hx b hb => by
        rw [mem_singleton_iff.1 hb]; exact hx))
    exact (ENNReal.mul_pos M.one_sub_δ_ne_zero hm.ne').trans_le
      (M.one_sub_mul_le_split_false _ h0)
  · obtain ⟨m, hm⟩ := exists_pow_comp_pos h hQ (h1.inter M.measurableSet_C) hc
    refine ⟨m + 1, ?_⟩
    rw [M.splitKernel_pow_succ_apply]
    refine lt_of_lt_of_le ?_ (measure_mono (show ((fun x => (x, true)) ⁻¹' s) ×ˢ
      ({true} : Set Bool) ⊆ s from prod_subset_iff.2 fun x hx b hb => by
        rw [mem_singleton_iff.1 hb]; exact hx))
    rw [M.split_apply_true _ h1]
    exact ENNReal.mul_pos M.δ_pos.ne' hm.ne'

/-- `Φ` is `φ`-irreducible iff `Φ̌` is `φ*`-irreducible. -/
theorem isPhiIrreducible_split_iff (M : Minorization P) [IsMarkovKernel P] (φ : Measure X) :
    IsPhiIrreducible P φ ↔
      haveI := M.isMarkovKernel_splitKernel; IsPhiIrreducible M.splitKernel (M.split φ) :=
  ⟨M.isPhiIrreducible_split, M.isPhiIrreducible_of_split⟩

/-- **Theorem 5.1.3 (ii)** (MT p. 100). (a) If `Φ̌` is `φ*`-irreducible then `Φ` is
`φ`-irreducible. (b) If `Φ` is `φ`-irreducible with `φ(C) > 0`, then `Φ̌` is `ν*`-irreducible,
every state of `X̌` reaches `α̌ = C₁`, and `α̌` is an accessible atom of `Φ̌` for every maximal
irreducibility measure of `Φ̌`. -/
theorem theorem_5_1_3_ii (M : Minorization P) [IsMarkovKernel P] (φ : Measure X) :
    haveI := M.isMarkovKernel_splitKernel
    (IsPhiIrreducible M.splitKernel (M.split φ) → IsPhiIrreducible P φ) ∧
      (IsPhiIrreducible P φ → 0 < φ M.C →
        IsPhiIrreducible M.splitKernel (M.split M.ν) ∧
        (∀ z, 0 < hitProb M.splitKernel M.checkAlpha z) ∧
        ∀ ψ : Measure (X × Bool), IsMaximalIrreducibility M.splitKernel ψ →
          IsAccessibleAtom M.splitKernel ψ M.checkAlpha) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_baseK
  refine ⟨M.isPhiIrreducible_of_split, fun h hC => ?_⟩
  have hreach : ∀ z, ∃ n, 0 < (M.splitKernel ^ n) z M.checkAlpha := fun z => by
    obtain ⟨m, hm⟩ := exists_pow_comp_pos h (IsProbabilityMeasure.ne_zero (M.baseK z))
      M.measurableSet_C hC
    refine ⟨m + 1 + 1, ?_⟩
    rw [M.splitKernel_pow_succ_apply, checkAlpha, M.split_apply_true _ M.measurableSet_C,
      inter_self]
    exact ENNReal.mul_pos M.δ_pos.ne' hm.ne'
  have hν : ∀ y ∈ M.checkAlpha, M.splitKernel y = M.split M.ν := fun y hy => by
    obtain ⟨x, b⟩ := y
    simp only [checkAlpha, mem_prod, mem_singleton_iff] at hy
    rw [hy.2, splitKernel_apply_true]
  exact proposition_5_1_1 M.splitKernel M.measurableSet_checkAlpha hν hreach

/-- If `ψ` is a maximal irreducibility measure for `Φ`, then `ψ*` is a maximal irreducibility
measure for the split chain. -/
theorem isMaximalIrreducibility_split (M : Minorization P) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    haveI := M.isMarkovKernel_splitKernel; IsMaximalIrreducibility M.splitKernel (M.split ψ) := by
  have := M.isMarkovKernel_splitKernel
  refine ⟨fun h0 => hψ.1 ?_, M.isPhiIrreducible_split hψ.2.1, fun φc hφc => ?_⟩
  · rw [← Measure.measure_univ_eq_zero, ← M.split_univ, h0]
    rfl
  -- the marginal of `φc` is an irreducibility measure for `Φ`
  have hmarg : IsPhiIrreducible P (φc.map Prod.fst) := by
    intro A hA hpos x
    have hA' : MeasurableSet (Prod.fst ⁻¹' A : Set (X × Bool)) := measurable_fst hA
    rw [Measure.map_apply measurable_fst hA] at hpos
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA' _).1 (hφc _ hA' hpos (x, false))
    refine (hitProb_pos_iff P hA x).2 ⟨n, ?_⟩
    have h2 := M.theorem_5_1_3_i (n + 1) (Measure.dirac x) hA
    have hm : Measurable fun z : X × Bool => (M.splitKernel ^ (n + 1)) z (Prod.fst ⁻¹' A) :=
      Kernel.measurable_coe _ hA'
    rw [lintegral_dirac' _ (Kernel.measurable_coe _ hA), M.lintegral_split _ hm,
      lintegral_dirac'] at h2
    · rw [h2]
      refine lt_of_lt_of_le ?_ le_self_add
      exact ENNReal.mul_pos (tsub_pos_of_lt ((M.splitProb_le x).trans_lt M.δ_lt_one)).ne' hn.ne'
    · exact ((measurable_const.sub M.measurable_splitProb).mul
        (hm.comp (measurable_id.prodMk measurable_const))).add
        (M.measurable_splitProb.mul (hm.comp (measurable_id.prodMk measurable_const)))
  have hac := hψ.2.2 _ hmarg
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  have hs0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have hs1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  -- `ψ` does not charge the two sections
  have hψ0 : ψ ((fun x => (x, false)) ⁻¹' s) = 0 := by
    have := (M.one_sub_mul_le_split_false ψ hs0).trans
      (measure_mono (μ := M.split ψ) (show ((fun x => (x, false)) ⁻¹' s) ×ˢ
        ({false} : Set Bool) ⊆ s from prod_subset_iff.2 fun x hx b hb => by
          rw [mem_singleton_iff.1 hb]; exact hx))
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left M.one_sub_δ_ne_zero
  have hψ1 : ψ ((fun x => (x, true)) ⁻¹' s ∩ M.C) = 0 := by
    have := measure_mono (μ := M.split ψ) (show ((fun x => (x, true)) ⁻¹' s) ×ˢ {true} ⊆ s from
      prod_subset_iff.2 fun x hx b hb => by rw [mem_singleton_iff.1 hb]; exact hx)
    rw [h0, M.split_apply_true ψ hs1, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left M.δ_pos.ne'
  -- the bottom level outside `C` is never reached
  have hbot : φc (M.Cᶜ ×ˢ {true}) = 0 := by
    by_contra hne
    have hm : MeasurableSet (M.Cᶜ ×ˢ ({true} : Set Bool)) :=
      M.measurableSet_C.compl.prod (measurableSet_singleton true)
    obtain ⟨z, -⟩ := nonempty_of_measure_ne_zero hne
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hm z).1 (hφc _ hm (pos_iff_ne_zero.2 hne) z)
    rw [M.splitKernel_pow_bottom_compl] at hn
    exact lt_irrefl _ hn
  refine measure_mono_null (subset_sections s) (measure_union_null ?_ ?_)
  · refine measure_mono_null (show ((fun x => (x, false)) ⁻¹' s) ×ˢ ({false} : Set Bool) ⊆
      Prod.fst ⁻¹' ((fun x => (x, false)) ⁻¹' s) from fun z hz => hz.1) ?_
    have := hac hψ0
    rwa [Measure.map_apply measurable_fst hs0] at this
  · have hsub : ((fun x => (x, true)) ⁻¹' s) ×ˢ ({true} : Set Bool) ⊆
        Prod.fst ⁻¹' ((fun x => (x, true)) ⁻¹' s ∩ M.C) ∪ M.Cᶜ ×ˢ {true} := by
      rintro ⟨x, b⟩ ⟨hx, hb⟩
      by_cases hc : x ∈ M.C
      · exact Or.inl ⟨hx, hc⟩
      · exact Or.inr ⟨hc, hb⟩
    refine measure_mono_null hsub (measure_union_null ?_ hbot)
    have := hac hψ1
    rwa [Measure.map_apply measurable_fst (hs1.inter M.measurableSet_C)] at this

end Minorization

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Small sets (MT §5.2)

Meyn and Tweedie, §5.2, pp. 102–106: the definition and the elementary results. The existence
of small sets (Theorems 5.2.1–5.2.3, Proposition 5.2.4 (ii)) is in `SmallSetExistence`.

* `IsSmallSet P m ν C` (5.14), p. 102: `C` is `νₘ`-small, `m ≥ 1`, `ν ≠ 0` and `Pᵐ(x, ·) ≥ ν` for
  every `x ∈ C`; `IsSmall P C`: `C` is small for some `m` and `ν`.
* `IsSmallSet.mono`, `IsSmallSet.smul`, `IsSmallSet.le_apply`: elementary properties;
  `IsSmallSet.measure_univ_le`: `ν(X) ≤ 1` when `C` is non-empty.
* `isSmallSet_of_atom` (p. 102): an atom with `P(x, ·) = ν` is `ν`-small with `m = 1`.
* `pow_add_ge_of_le`: the Chapman–Kolmogorov bound `Pᵐ⁺ⁿ(x, B) ≥ Pᵐ(x, C) ν(B)` when
  `Pⁿ(y, ·) ≥ ν` on `C`; `comp_le_comp`: `μ ≤ μ'` implies `μK ≤ μ'K`.
* **Proposition 5.2.4 (i)** (`proposition_5_2_4_i`, p. 105): if `C` is `νₙ`-small and
  `Pᵐ(x, C) ≥ δ > 0` on `D`, then `D` is `δνₙ`-small with index `m + n`.
* **Proposition 5.2.4 (iii)** (`proposition_5_2_4_iii`, p. 106): for a `φ`-irreducible chain
  and a small `C` with `φ(C) > 0`, `C` is `ν_M`-small for some `M` with `ν_M(C) > 0`, namely
  `ν_M = νPᵐ⁺¹`.
* `IsSmallSet.minorization`: a `ν`-small set with `ν(C) > 0` gives the minorization condition
  (5.2) for `Pᵐ`, with the book's normalisation `ν(Cᶜ) = 0`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- `C` is a **`νₘ`-small set** (5.14), MT p. 102: `C` is measurable, `m ≥ 1`, `ν` is a nonzero
measure and `Pᵐ(x, B) ≥ ν(B)` for every `x ∈ C` and every measurable `B`. -/
def IsSmallSet (P : Kernel X X) (m : ℕ) (ν : Measure X) (C : Set X) : Prop :=
  MeasurableSet C ∧ 0 < m ∧ ν ≠ 0 ∧ ∀ x ∈ C, ν ≤ (P ^ m) x

/-- `C` is a **small set** (MT p. 102): it is `νₘ`-small for some `m ≥ 1` and nonzero `ν`. -/
def IsSmall (P : Kernel X X) (C : Set X) : Prop := ∃ m ν, IsSmallSet P m ν C

/-- The bound `Pᵐ(x, B) ≥ ν(B)` of a small set. -/
theorem IsSmallSet.le_apply {P : Kernel X X} {m : ℕ} {ν : Measure X} {C : Set X}
    (h : IsSmallSet P m ν C) {x : X} (hx : x ∈ C) (B : Set X) : ν B ≤ (P ^ m) x B :=
  h.2.2.2 x hx B

/-- A measurable subset of a small set is small. -/
theorem IsSmallSet.mono {P : Kernel X X} {m : ℕ} {ν : Measure X} {C D : Set X}
    (h : IsSmallSet P m ν C) (hD : MeasurableSet D) (hDC : D ⊆ C) : IsSmallSet P m ν D :=
  ⟨hD, h.2.1, h.2.2.1, fun x hx => h.2.2.2 x (hDC hx)⟩

/-- A nonzero multiple of a nonzero measure is nonzero. -/
theorem smul_measure_ne_zero {ν : Measure X} (hν : ν ≠ 0) {c : ℝ≥0∞} (hc : c ≠ 0) :
    c • ν ≠ 0 := fun h => by
  have h1 := congrArg (fun μ : Measure X => μ univ) h
  simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
    Measure.measure_univ_eq_zero] at h1
  exact h1.elim hc hν

/-- A nonzero multiple `cν` with `c ≤ 1` of a minorizing measure is minorizing. -/
theorem IsSmallSet.smul {P : Kernel X X} {m : ℕ} {ν : Measure X} {C : Set X}
    (h : IsSmallSet P m ν C) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc1 : c ≤ 1) : IsSmallSet P m (c • ν) C :=
  ⟨h.1, h.2.1, smul_measure_ne_zero h.2.2.1 hc0, fun x hx => by
    refine Measure.le_intro fun B _ _ => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact (mul_le_of_le_one_left' hc1).trans (h.le_apply hx B)⟩

/-- The minorizing measure of a non-empty small set has mass at most one. -/
theorem IsSmallSet.measure_univ_le {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} {ν : Measure X}
    {C : Set X} (h : IsSmallSet P m ν C) (hne : C.Nonempty) : ν univ ≤ 1 := by
  obtain ⟨x, hx⟩ := hne
  have := isMarkovKernel_pow P m
  exact (h.le_apply hx univ).trans prob_le_one

/-- An atom is small (MT p. 102): if `P(x, ·) = ν` on `α`, with `ν ≠ 0`, then `α` is `ν`-small
with `m = 1`. -/
theorem isSmallSet_of_atom (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) {ν : Measure X}
    (hν : ∀ x ∈ α, P x = ν) (h0 : ν ≠ 0) : IsSmallSet P 1 ν α :=
  ⟨hα, one_pos, h0, fun x hx => by rw [pow_one, hν x hx]⟩

/-- **Chapman–Kolmogorov through `C`**: if `Pⁿ(y, ·) ≥ ν` for every `y ∈ C`, then
`Pᵐ⁺ⁿ(x, B) ≥ ∫_C Pᵐ(x, dy) Pⁿ(y, B) ≥ Pᵐ(x, C) ν(B)` (5.26). -/
theorem pow_add_ge_of_le (P : Kernel X X) {m n : ℕ} {C : Set X}
    {ν : Measure X} (hν : ∀ y ∈ C, ν ≤ (P ^ n) y) (x : X) {B : Set X} (hB : MeasurableSet B) :
    (P ^ m) x C * ν B ≤ (P ^ (m + n)) x B := by
  rw [Kernel.pow_add_apply_eq_lintegral P m n x hB]
  calc (P ^ m) x C * ν B = ∫⁻ _ in C, ν B ∂(P ^ m) x := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in C, (P ^ n) y B ∂(P ^ m) x := setLIntegral_mono (Kernel.measurable_coe _ hB)
        fun y hy => hν y hy B
    _ ≤ ∫⁻ y, (P ^ n) y B ∂(P ^ m) x := setLIntegral_le_lintegral _ _

/-- The bound `Pᵐ⁺ⁿ(x, ·) ≥ Pᵐ(x, C) ν` as an inequality of measures. -/
theorem smul_le_pow_add_of_le (P : Kernel X X) {m n : ℕ} {C : Set X}
    {ν : Measure X} (hν : ∀ y ∈ C, ν ≤ (P ^ n) y) (x : X) :
    (P ^ m) x C • ν ≤ (P ^ (m + n)) x :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact pow_add_ge_of_le P hν x hB

/-- Composition with a kernel is monotone in the measure: `μ ≤ μ'` implies `μK ≤ μ'K`. -/
theorem comp_le_comp {Y : Type*} [MeasurableSpace Y] (K : Kernel X Y) {μ μ' : Measure X}
    (h : μ ≤ μ') : K ∘ₘ μ ≤ K ∘ₘ μ' :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.bind_apply hB K.aemeasurable, Measure.bind_apply hB K.aemeasurable]
    exact lintegral_mono' h le_rfl

/-- **Proposition 5.2.4 (i)** (MT p. 105). If `C` is `νₙ`-small and `Pᵐ(x, C) ≥ δ > 0` for every
`x ∈ D`, then `D` is `δνₙ`-small with index `m + n`. -/
theorem proposition_5_2_4_i (P : Kernel X X) {n m : ℕ} {ν : Measure X} {C D : Set X}
    (hC : IsSmallSet P n ν C) (hD : MeasurableSet D) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (h : ∀ x ∈ D, δ ≤ (P ^ m) x C) : IsSmallSet P (m + n) (δ • ν) D :=
  ⟨hD, Nat.add_pos_right m hC.2.1, smul_measure_ne_zero hC.2.2.1 hδ.ne', fun x hx =>
    Measure.le_intro fun B hB _ => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact (mul_le_mul_left (h x hx) _).trans (pow_add_ge_of_le P hC.2.2.2 x hB)⟩

/-- **Proposition 5.2.4 (iii)** (MT p. 106). For a `φ`-irreducible chain and a `νₙ`-small set `C`
with `φ(C) > 0`, there are `m` and `ν_M = νPᵐ⁺¹` such that `C` is `ν_M`-small with index
`M = n + m + 1` and `ν_M(C) > 0`. -/
theorem proposition_5_2_4_iii (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {n : ℕ} {ν : Measure X} {C : Set X} (hC : IsSmallSet P n ν C)
    (hCφ : 0 < φ C) :
    ∃ m, IsSmallSet P (n + (m + 1)) ((P ^ (m + 1) : Kernel X X) ∘ₘ ν) C ∧
      0 < ((P ^ (m + 1) : Kernel X X) ∘ₘ ν) C := by
  obtain ⟨m, hm⟩ := exists_pow_comp_pos hφ hC.2.2.1 hC.1 hCφ
  refine ⟨m, ⟨hC.1, by omega, fun h0 => by rw [h0] at hm; exact lt_irrefl _ hm, fun x hx => ?_⟩,
    hm⟩
  rw [show n + (m + 1) = (m + 1) + n by omega, Kernel.pow_add P (m + 1) n, Kernel.comp_apply]
  exact comp_le_comp _ (hC.2.2.2 x hx)

/-- A `ν`-small set `C` with `ν(C) > 0` gives the minorization condition (5.2) for `Pᵐ` on `C`,
with `ν(Cᶜ) = 0`. -/
noncomputable def IsSmallSet.minorization {P : Kernel X X} [IsMarkovKernel P] {m : ℕ}
    {ν : Measure X} {C : Set X} (h : IsSmallSet P m ν C) (hpos : 0 < ν C) : Minorization (P ^ m) :=
  Minorization.ofLe h.1 h.2.2.2 hpos (ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono (subset_univ C)).trans (h.measure_univ_le (nonempty_of_measure_ne_zero
      hpos.ne'))))

/-- The minorization of a small set lives on that set. -/
theorem IsSmallSet.minorization_C {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} {ν : Measure X}
    {C : Set X} (h : IsSmallSet P m ν C) (hpos : 0 < ν C) : (h.minorization hpos).C = C := rfl

/-- The minorization of a small set satisfies the book's normalisation `ν(Cᶜ) = 0`. -/
theorem IsSmallSet.minorization_isConcentrated {P : Kernel X X} [IsMarkovKernel P] {m : ℕ}
    {ν : Measure X} {C : Set X} (h : IsSmallSet P m ν C) (hpos : 0 < ν C) :
    (h.minorization hpos).IsConcentrated :=
  Minorization.ofLe_isConcentrated _ _ _ _

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The existence of small sets (MT §5.2, Theorems 5.2.1–5.2.3)

Meyn and Tweedie, §5.2, pp. 103–106. Throughout, `B(X)` is **countably generated**
(`MeasurableSpace.CountablyGenerated X`), the standing assumption of MT p. 50 (a "general state
space"); this is the hypothesis the proof needs, both for jointly measurable densities and for a
countable family of sets approximating every measurable set.

* `transDensity P φ n x y = pⁿ(x, y)` (5.15): the density of the absolutely continuous part of
  `Pⁿ(x, ·)` with respect to `φ`, taken to be Mathlib's kernel Radon–Nikodym derivative, which is
  jointly measurable (`measurable_transDensity`). `theorem_5_2_1_density` is (5.15):
  `Pⁿ(x, B) = ∫_B pⁿ(x, y) φ(dy) + P⊥(x, B)` with `P⊥(x, ·) ⟂ φ`. This is part (i) of the proof
  of Theorem 5.2.1.
* `ae_exists_transDensity_pos`: under the hypothesis of Theorem 5.2.1,
  `Σₙ pⁿ(x, y) > 0` for `x ∈ A` and `φ`-a.e. `y ∈ A` (MT p. 104).
* `exists_rect_of_not_ae_zero`: the replacement for the density-point argument (5.19)–(5.23).
  If `F(x, z) = φ(Uₓ ∩ Vᶻ)` does not vanish for a.e. `x, z ∈ A`, there are `E, D ⊆ A` of positive
  measure with `F ≥ ε > 0` on `E × D`. The proof approximates the sections `Uₓ`, `Vᶻ` by the sets
  of a countable measure-dense family; no differentiation of measures is needed.
* **Theorem 5.2.1** (`theorem_5_2_1`, p. 103): for finite `φ` and `A` with `φ(A) > 0` such that
  every `B ⊆ A` with `φ(B) > 0` is reached from every `x ∈ A`, there are `C ⊆ A` with
  `φ(C) > 0`, `m ≥ 1` and `δ > 0` with `Pᵐ(x, B) ≥ δ φ(B ∩ C)` for all `x ∈ C`: this is the
  integrated form of (5.16), `pᵐ(x, y) ≥ δ` on `C × C`, which is how (5.16) is used.
* `theorem_5_2_1_density_ge`: the density form of (5.16), `pᵐ(x, y) ≥ δ` for `x ∈ C` and
  `φ`-a.e. `y ∈ C`, for the jointly measurable version of the densities.
* **Theorem 5.2.2** (`theorem_5_2_2`, p. 105): for a `ψ`-irreducible chain, every `A ∈ B⁺(X)`
  contains a `νₘ`-small set `C ∈ B⁺(X)` with `νₘ(C) > 0`.
* **Theorem 5.2.3** (`theorem_5_2_3`, `theorem_5_2_3_resolvent`, p. 105): the minorization
  condition (5.2) holds for some `m`-skeleton, and for every resolvent `K_{a_ε}`, `0 < ε < 1`.
* **Proposition 5.2.4 (ii)** (`proposition_5_2_4_ii`, p. 106): `X` is a countable union of small
  sets, `C̄(n, m) = {y : Pⁿ(y, C) ≥ m⁻¹}` (5.27).

**Corrections and hypotheses.** The theorems need `B(X)` countably generated (the book's standing
assumption). The book takes `φ` σ-finite in Theorem 5.2.1; the statement here takes `φ` finite,
which is all Theorem 5.2.2 needs (a maximal irreducibility measure has an equivalent probability
measure). The specific version of the densities built in the book's proof (with the
Chapman–Kolmogorov inequality (5.17)) is not needed: the Chapman–Kolmogorov equations for the
kernels themselves suffice.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal symmDiff

variable {X : Type*} [MeasurableSpace X]

variable [MeasurableSpace.CountablyGenerated X]

/-! ### Jointly measurable densities -/

/-- The density `pⁿ(x, y)` of (5.15): the Radon–Nikodym derivative of the absolutely continuous
part of `Pⁿ(x, ·)` with respect to `φ`. -/
noncomputable def transDensity (P : Kernel X X) (φ : Measure X) (n : ℕ) (x y : X) : ℝ≥0∞ :=
  Kernel.rnDeriv (P ^ n) (Kernel.const X φ) x y

/-- The densities are jointly measurable (part (i) of the proof of Theorem 5.2.1, MT p. 103). -/
theorem measurable_transDensity (P : Kernel X X) (φ : Measure X) (n : ℕ) :
    Measurable fun p : X × X => transDensity P φ n p.1 p.2 :=
  Kernel.measurable_rnDeriv _ _

/-- `∫_B pⁿ(x, y) φ(dy) ≤ Pⁿ(x, B)`. -/
theorem setLIntegral_transDensity_le (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    ∫⁻ y in B, transDensity P φ n x y ∂φ ≤ (P ^ n) x B := by
  have := isMarkovKernel_pow P n
  have h := Kernel.setLIntegral_rnDeriv_le (κ := P ^ n) (η := Kernel.const X φ) (a := x) hB
  rwa [Kernel.const_apply] at h

/-- `∫ pⁿ(x, y) g(y) φ(dy) ≤ ∫ g dPⁿ(x, ·)` for measurable `g ≥ 0`. -/
theorem lintegral_transDensity_mul_le (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] (n : ℕ) (x : X) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, transDensity P φ n x y * g y ∂φ ≤ ∫⁻ y, g y ∂(P ^ n) x := by
  have := isMarkovKernel_pow P n
  have h := Kernel.withDensity_rnDeriv_le (P ^ n) (Kernel.const X φ) x
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _), Kernel.const_apply] at h
  calc ∫⁻ y, transDensity P φ n x y * g y ∂φ
      = ∫⁻ y, g y ∂φ.withDensity (Kernel.rnDeriv (P ^ n) (Kernel.const X φ) x) :=
        (lintegral_withDensity_eq_lintegral_mul _
          (Kernel.measurable_rnDeriv_right _ _ x) hg).symm
    _ ≤ ∫⁻ y, g y ∂(P ^ n) x := lintegral_mono' h le_rfl

/-- **(5.15)** (MT p. 103): the Lebesgue decomposition
`Pⁿ(x, B) = ∫_B pⁿ(x, y) φ(dy) + P⊥(x, B)`, with `P⊥(x, ·)` singular with respect to `φ`, and
with jointly measurable densities. -/
theorem theorem_5_2_1_density (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] (n : ℕ) :
    Measurable (fun p : X × X => transDensity P φ n p.1 p.2) ∧
      ∀ x, ∃ Q : Measure X, Q ⟂ₘ φ ∧ ∀ B, MeasurableSet B →
        (P ^ n) x B = ∫⁻ y in B, transDensity P φ n x y ∂φ + Q B := by
  have := isMarkovKernel_pow P n
  refine ⟨measurable_transDensity P φ n, fun x => ⟨Kernel.singularPart (P ^ n)
    (Kernel.const X φ) x, ?_, fun B hB => ?_⟩⟩
  · have h := Kernel.mutuallySingular_singularPart (P ^ n) (Kernel.const X φ) x
    rwa [Kernel.const_apply] at h
  · have h := congrArg (fun κ : Kernel X X => κ x B)
      (Kernel.rnDeriv_add_singularPart (P ^ n) (Kernel.const X φ))
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add] at h
    rw [← h, Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _), Kernel.const_apply,
      withDensity_apply _ hB]
    rfl

/-- Under the hypothesis of Theorem 5.2.1, for `x ∈ A`, `Σₙ pⁿ⁺¹(x, y) > 0` for `φ`-a.e.
`y ∈ A` (MT p. 104). -/
theorem ae_exists_transDensity_pos (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] {A : Set X} (hA : MeasurableSet A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 < φ B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B)
    {x : X} (hx : x ∈ A) :
    ∀ᵐ y ∂φ.restrict A, ∃ n, 0 < transDensity P φ (n + 1) x y := by
  set N : Set X := A ∩ ⋂ n, {y | transDensity P φ (n + 1) x y = 0} with hNdef
  have hmeas : ∀ n, Measurable fun y => transDensity P φ n x y := fun n =>
    Kernel.measurable_rnDeriv_right _ _ x
  have hNm : MeasurableSet N :=
    hA.inter (MeasurableSet.iInter fun n => hmeas (n + 1) (measurableSet_singleton 0))
  have hN : φ N = 0 := by
    by_contra hpos
    -- the singular parts live on null sets
    have hdec : ∀ n, ∃ Q : Measure X, Q ⟂ₘ φ ∧ ∀ B, MeasurableSet B →
        (P ^ (n + 1)) x B = ∫⁻ y in B, transDensity P φ (n + 1) x y ∂φ + Q B :=
      fun n => (theorem_5_2_1_density P φ (n + 1)).2 x
    choose Q hQ hQB using hdec
    have hsing : ∀ n, ∃ s, MeasurableSet s ∧ Q n s = 0 ∧ φ sᶜ = 0 := fun n => by
      obtain ⟨s, hs, h1, h2⟩ := hQ n
      exact ⟨s, hs, h1, h2⟩
    choose s hs hs0 hs1 using hsing
    set B := N ∩ ⋂ n, s n
    have hBm : MeasurableSet B := hNm.inter (MeasurableSet.iInter hs)
    have hBφ : φ B = φ N := by
      refine measure_congr ?_
      refine (inter_ae_eq_left_of_ae_eq_univ ?_)
      refine ae_eq_univ.2 ?_
      rw [compl_iInter]
      exact measure_iUnion_null hs1
    obtain ⟨k, hk⟩ := h B hBm (inter_subset_left.trans inter_subset_left)
      (by rw [hBφ]; exact pos_iff_ne_zero.2 hpos) x hx
    have hz1 : ∫⁻ y in B, transDensity P φ (k + 1) x y ∂φ = 0 := by
      rw [setLIntegral_congr_fun hBm (g := fun _ => 0) fun y hy => by
        have : y ∈ ⋂ n, {y | transDensity P φ (n + 1) x y = 0} := hy.1.2
        exact mem_iInter.1 this k]
      simp
    have hz2 : Q k B = 0 :=
      measure_mono_null (inter_subset_right.trans (iInter_subset _ k)) (hs0 k)
    rw [hQB k B hBm, hz1, hz2, add_zero] at hk
    exact lt_irrefl _ hk
  have h1 : ∀ᵐ y ∂φ, y ∉ N := measure_eq_zero_iff_ae_notMem.1 hN
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae h1] with y hyA hyN
  by_contra hc
  push Not at hc
  exact hyN ⟨hyA, mem_iInter.2 fun n => nonpos_iff_eq_zero.1 (hc n)⟩

/-! ### Selecting a rectangle -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- `φ(s ∩ t) ≤ φ(a ∩ b) + φ(a ∆ s) + φ(b ∆ t)`. -/
theorem measure_inter_le_add_symmDiff (φ : Measure X) (a b s t : Set X) :
    φ (s ∩ t) ≤ φ (a ∩ b) + φ (a ∆ s) + φ (b ∆ t) := by
  calc φ (s ∩ t) ≤ φ ((a ∩ b) ∪ (a ∆ s) ∪ (b ∆ t)) := measure_mono fun y ⟨hs, ht⟩ => by
        by_cases ha : y ∈ a <;> by_cases hb : y ∈ b
        · exact Or.inl (Or.inl ⟨ha, hb⟩)
        · exact Or.inr (Or.inr ⟨ht, hb⟩)
        · exact Or.inl (Or.inr (Or.inr ⟨hs, ha⟩))
        · exact Or.inl (Or.inr (Or.inr ⟨hs, ha⟩))
    _ ≤ φ ((a ∩ b) ∪ (a ∆ s)) + φ (b ∆ t) := measure_union_le _ _
    _ ≤ φ (a ∩ b) + φ (a ∆ s) + φ (b ∆ t) := by gcongr; exact measure_union_le _ _

omit [MeasurableSpace.CountablyGenerated X] in
/-- If `a < 5 (j + 1)⁻¹` for every `j`, then `a = 0`. -/
theorem eq_zero_of_forall_lt_five_inv {a : ℝ≥0∞} (h : ∀ j : ℕ, a < 5 * ((j : ℝ≥0∞) + 1)⁻¹) :
    a = 0 := by
  by_contra ha
  have h5 : a / 5 ≠ 0 := by simp [ha]
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h5
  have h1 := (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).1 hj
  have h2 : 5 * ((j : ℝ≥0∞) + 1)⁻¹ ≤ (j : ℝ≥0∞)⁻¹ * 5 := by
    rw [mul_comm]
    gcongr
    exact le_self_add
  exact lt_irrefl _ ((h j).trans_le h2 |>.trans h1)

/-- **Selecting a rectangle** (the replacement for (5.19)–(5.23), MT pp. 104–105). Let
`F(x, z) = φ(Uₓ ∩ Vᶻ)`, where `Uₓ = {y : (x, y) ∈ U}` and `Vᶻ = {y : (y, z) ∈ V}`. If it is not
true that `F(x, z) = 0` for a.e. `x ∈ A` and a.e. `z ∈ A`, then there are `E, D ⊆ A` of positive
measure and `ε > 0` with `F ≥ ε` on `E × D`. The sections are approximated by the sets of a
countable measure-dense family (here `B(X)` countably generated is used). -/
theorem exists_rect_of_not_ae_zero (φ : Measure X) [IsFiniteMeasure φ] {A : Set X}
    (hA : MeasurableSet A) {U V : Set (X × X)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : ¬ ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A,
      φ (Prod.mk x ⁻¹' U ∩ (fun y => (y, z)) ⁻¹' V) = 0) :
    ∃ E D : Set X, E ⊆ A ∧ D ⊆ A ∧ MeasurableSet E ∧ MeasurableSet D ∧ 0 < φ E ∧ 0 < φ D ∧
      ∃ ε : ℝ≥0∞, 0 < ε ∧
        ∀ x ∈ E, ∀ z ∈ D, ε ≤ φ (Prod.mk x ⁻¹' U ∩ (fun y => (y, z)) ⁻¹' V) := by
  set F : X → X → ℝ≥0∞ := fun x z => φ (Prod.mk x ⁻¹' U ∩ (fun y => (y, z)) ⁻¹' V) with hFdef
  -- a positive threshold
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ¬ ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A,
      F x z < 5 * ((j : ℝ≥0∞) + 1)⁻¹ := by
    by_contra hc
    push Not at hc
    refine h ?_
    have h1 : ∀ᵐ x ∂φ.restrict A, ∀ j : ℕ, ∀ᵐ z ∂φ.restrict A,
        F x z < 5 * ((j : ℝ≥0∞) + 1)⁻¹ := ae_all_iff.2 hc
    filter_upwards [h1] with x hx
    filter_upwards [ae_all_iff.2 hx] with z hz
    exact eq_zero_of_forall_lt_five_inv hz
  set ε : ℝ≥0∞ := ((j : ℝ≥0∞) + 1)⁻¹ with hεdef
  have hε0 : 0 < ε := ENNReal.inv_pos.2 (by simp)
  have hεt : ε ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
  have hε2 : ε + ε ≠ ∞ := ENNReal.add_ne_top.2 ⟨hεt, hεt⟩
  obtain ⟨𝒜, h𝒜c, h𝒜d⟩ := exists_countable_measureDense φ
  have := h𝒜c.to_subtype
  -- the two families of approximating pieces
  set Es : Set X → Set X := fun S => {x | x ∈ A ∧ φ ((Prod.mk x ⁻¹' U) ∆ S) < ε} with hEs
  set Ds : Set X → Set X := fun T => {z | z ∈ A ∧ φ (((fun y => (y, z)) ⁻¹' V) ∆ T) < ε}
    with hDs
  have hEsm : ∀ S ∈ 𝒜, MeasurableSet (Es S) := fun S hS => by
    have hset : (fun x => φ ((Prod.mk x ⁻¹' U) ∆ S)) =
        fun x => φ (Prod.mk x ⁻¹' (U ∆ (univ ×ˢ S))) := by
      ext x; congr 1; ext y; simp [mem_symmDiff]
    have hmeas : Measurable fun x => φ ((Prod.mk x ⁻¹' U) ∆ S) := by
      rw [hset]
      exact measurable_measure_prodMk_left (hU.symmDiff (MeasurableSet.univ.prod
        (h𝒜d.measurable S hS)))
    exact hA.inter (measurableSet_lt hmeas measurable_const)
  have hDsm : ∀ T ∈ 𝒜, MeasurableSet (Ds T) := fun T hT => by
    have hset : (fun z => φ (((fun y => (y, z)) ⁻¹' V) ∆ T)) =
        fun z => φ ((fun y => (y, z)) ⁻¹' (V ∆ (T ×ˢ univ))) := by
      ext z; congr 1; ext y; simp [mem_symmDiff]
    have hmeas : Measurable fun z => φ (((fun y => (y, z)) ⁻¹' V) ∆ T) := by
      rw [hset]
      exact measurable_measure_prodMk_right (hV.symmDiff ((h𝒜d.measurable T hT).prod
        MeasurableSet.univ))
    exact hA.inter (measurableSet_lt hmeas measurable_const)
  -- every point of `A` lies in one of the pieces
  have hεr : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal hεt
  have hEcov : ∀ x ∈ A, ∃ S ∈ 𝒜, x ∈ Es S := fun x hx => by
    obtain ⟨S, hS, hlt⟩ := h𝒜d.approx (Prod.mk x ⁻¹' U) (measurable_prodMk_left hU)
      (measure_ne_top _ _) ε.toReal (ENNReal.toReal_pos hε0.ne' hεt)
    exact ⟨S, hS, hx, by rwa [hεr] at hlt⟩
  have hDcov : ∀ z ∈ A, ∃ T ∈ 𝒜, z ∈ Ds T := fun z hz => by
    obtain ⟨T, hT, hlt⟩ := h𝒜d.approx ((fun y => (y, z)) ⁻¹' V)
      ((measurable_id.prodMk measurable_const) hV) (measure_ne_top _ _) ε.toReal
      (ENNReal.toReal_pos hε0.ne' hεt)
    exact ⟨T, hT, hz, by rwa [hεr] at hlt⟩
  by_contra hcon
  refine hj ?_
  -- the null pieces
  set N₁ : Set X := ⋃ S : 𝒜, ⋃ (_ : φ (Es S) = 0), Es S
  set N₂ : Set X := ⋃ T : 𝒜, ⋃ (_ : φ (Ds T) = 0), Ds T
  have hN₁ : φ N₁ = 0 := measure_iUnion_null fun S => measure_iUnion_null fun h => h
  have hN₂ : φ N₂ = 0 := measure_iUnion_null fun T => measure_iUnion_null fun h => h
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₁)]
    with x hxA hxN
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₂)]
    with z hzA hzN
  by_contra hge
  push Not at hge
  obtain ⟨S, hS, hxS⟩ := hEcov x hxA
  obtain ⟨T, hT, hzT⟩ := hDcov z hzA
  have hES : φ (Es S) ≠ 0 := fun h0 => hxN (mem_iUnion.2 ⟨⟨S, hS⟩, mem_iUnion.2 ⟨h0, hxS⟩⟩)
  have hDT : φ (Ds T) ≠ 0 := fun h0 => hzN (mem_iUnion.2 ⟨⟨T, hT⟩, mem_iUnion.2 ⟨h0, hzT⟩⟩)
  refine hcon ⟨Es S, Ds T, fun y hy => hy.1, fun y hy => hy.1, hEsm S hS, hDsm T hT,
    pos_iff_ne_zero.2 hES, pos_iff_ne_zero.2 hDT, ε, hε0, fun x' hx' z' hz' => ?_⟩
  -- `φ(S ∩ T) > 3ε`
  have hST : 3 * ε < φ (S ∩ T) := by
    have h1 := measure_inter_le_add_symmDiff φ S T (Prod.mk x ⁻¹' U) ((fun y => (y, z)) ⁻¹' V)
    rw [symmDiff_comm S, symmDiff_comm T] at h1
    have h2 : F x z < φ (S ∩ T) + (ε + ε) := by
      calc F x z ≤ _ := h1
        _ = φ (S ∩ T) + (φ ((Prod.mk x ⁻¹' U) ∆ S) + φ (((fun y => (y, z)) ⁻¹' V) ∆ T)) := by
          rw [add_assoc]
        _ < φ (S ∩ T) + (ε + ε) :=
          ENNReal.add_lt_add_left (measure_ne_top _ _) (ENNReal.add_lt_add hxS.2 hzT.2)
    have h3 : 3 * ε + (ε + ε) < φ (S ∩ T) + (ε + ε) := by
      calc 3 * ε + (ε + ε) = 5 * ε := by ring
        _ ≤ F x z := hge
        _ < _ := h2
    exact (ENNReal.add_lt_add_iff_right hε2).1 h3
  have h1 := measure_inter_le_add_symmDiff φ (Prod.mk x' ⁻¹' U) ((fun y => (y, z')) ⁻¹' V) S T
  have h4 : ε + (ε + ε) < F x' z' + (ε + ε) := by
    calc ε + (ε + ε) = 3 * ε := by ring
      _ < φ (S ∩ T) := hST
      _ ≤ _ := h1
      _ = F x' z' + (φ ((Prod.mk x' ⁻¹' U) ∆ S) + φ (((fun y => (y, z')) ⁻¹' V) ∆ T)) := by
        rw [add_assoc]
      _ < F x' z' + (ε + ε) :=
        ENNReal.add_lt_add_left (measure_ne_top _ _) (ENNReal.add_lt_add hx'.2 hz'.2)
  exact ((ENNReal.add_lt_add_iff_right hε2).1 h4).le

/-! ### Theorem 5.2.1 -/

/-- The level sets `{(x, y) : pⁿ⁺¹(x, y) ≥ (k + 1)⁻¹}` of the densities, the sets `Aₙ(η)` of
MT p. 104. -/
def densLevel (P : Kernel X X) (φ : Measure X) (n k : ℕ) : Set (X × X) :=
  {p | ((k : ℝ≥0∞) + 1)⁻¹ ≤ transDensity P φ (n + 1) p.1 p.2}

/-- The level sets are measurable. -/
theorem measurableSet_densLevel (P : Kernel X X) (φ : Measure X) (n k : ℕ) :
    MeasurableSet (densLevel P φ n k) :=
  measurableSet_le measurable_const (measurable_transDensity P φ (n + 1))

/-- The positivity statement of MT p. 104: under the hypothesis of Theorem 5.2.1 there are
`n, m, η` such that `φ{y : pⁿ(x, y) ≥ η, pᵐ(y, z) ≥ η}` is not zero for a.e. `x, z ∈ A`. -/
theorem exists_densLevel_not_ae_zero (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] {A : Set X} (hA : MeasurableSet A) (hφA : 0 < φ A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 < φ B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B) :
    ∃ n m k : ℕ, ¬ ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A,
      φ (Prod.mk x ⁻¹' densLevel P φ n k ∩ (fun y => (y, z)) ⁻¹' densLevel P φ m k) = 0 := by
  by_contra hc
  push Not at hc
  have hne : φ.restrict A ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hφA.ne'
  have : (ae (φ.restrict A)).NeBot := ae_neBot.2 hne
  -- for a.e. `x, z`, a.e. `y` lies in no pair of level sets
  have h1 : ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A, ∀ᵐ y ∂φ.restrict A,
      ∀ n m k : ℕ, ¬ ((x, y) ∈ densLevel P φ n k ∧ (y, z) ∈ densLevel P φ m k) := by
    have hx : ∀ᵐ x ∂φ.restrict A, ∀ n m k : ℕ, ∀ᵐ z ∂φ.restrict A,
        φ (Prod.mk x ⁻¹' densLevel P φ n k ∩ (fun y => (y, z)) ⁻¹' densLevel P φ m k) = 0 :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun k => hc n m k
    filter_upwards [hx] with x hx
    have hz : ∀ᵐ z ∂φ.restrict A, ∀ n m k : ℕ,
        φ (Prod.mk x ⁻¹' densLevel P φ n k ∩ (fun y => (y, z)) ⁻¹' densLevel P φ m k) = 0 :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun k => hx n m k
    filter_upwards [hz] with z hz
    exact ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun k =>
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hz n m k))
  -- hence for a.e. `x, z`, a.e. `y` does not reach `z`
  have h2 : ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A, ∀ᵐ y ∂φ.restrict A,
      ∀ m, transDensity P φ (m + 1) y z = 0 := by
    filter_upwards [ae_restrict_mem hA, h1] with x hxA hx
    filter_upwards [hx] with z hz
    filter_upwards [hz, ae_exists_transDensity_pos P φ hA h hxA] with y hy hpos
    obtain ⟨n, hn⟩ := hpos
    intro m
    by_contra hm
    obtain ⟨k₁, hk₁⟩ := ENNReal.exists_inv_nat_lt hn.ne'
    obtain ⟨k₂, hk₂⟩ := ENNReal.exists_inv_nat_lt hm
    refine hy n m (max k₁ k₂) ⟨?_, ?_⟩
    · refine le_trans ?_ hk₁.le
      gcongr
      exact (Nat.cast_le.2 (le_max_left k₁ k₂)).trans le_self_add
    · refine le_trans ?_ hk₂.le
      gcongr
      exact (Nat.cast_le.2 (le_max_right k₁ k₂)).trans le_self_add
  obtain ⟨x, hx⟩ := h2.exists
  have hmeas : MeasurableSet {q : X × X | ∀ m, transDensity P φ (m + 1) q.2 q.1 = 0} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun m =>
      ((measurable_transDensity P φ (m + 1)).comp measurable_swap) (measurableSet_singleton 0)
  have h3 := (Measure.ae_ae_comm (μ := φ.restrict A) (ν := φ.restrict A)
    (p := fun z y => ∀ m, transDensity P φ (m + 1) y z = 0) hmeas).1 hx
  obtain ⟨y, hy, hyA⟩ := (h3.and (ae_restrict_mem hA)).exists
  obtain ⟨z, hz1, hz2⟩ := (hy.and (ae_exists_transDensity_pos P φ hA h hyA)).exists
  obtain ⟨m, hm⟩ := hz2
  exact hm.ne' (hz1 m)

/-- **Theorem 5.2.1** (MT p. 103). Let `B(X)` be countably generated, `φ` a finite measure and
`A` a set with `φ(A) > 0` such that every `B ⊆ A` with `φ(B) > 0` is reached from every
`x ∈ A`: `Σ_{k ≥ 1} Pᵏ(x, B) > 0`. Then there are `C ⊆ A` with `φ(C) > 0`, `m ≥ 1` and `δ > 0`
such that `Pᵐ(x, B) ≥ δ φ(B ∩ C)` for every `x ∈ C`: the integrated form of (5.16). -/
theorem theorem_5_2_1 (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) [IsFiniteMeasure φ]
    {A : Set X} (hA : MeasurableSet A) (hφA : 0 < φ A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 < φ B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B) :
    ∃ C ⊆ A, MeasurableSet C ∧ 0 < φ C ∧ ∃ m, 0 < m ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ x ∈ C, δ • φ.restrict C ≤ (P ^ m) x := by
  obtain ⟨n, m, k, hnmk⟩ := exists_densLevel_not_ae_zero P φ hA hφA h
  obtain ⟨E, D, hEA, hDA, hEm, hDm, hEpos, hDpos, ε, hε, hF⟩ :=
    exists_rect_of_not_ae_zero φ hA (measurableSet_densLevel P φ n k)
      (measurableSet_densLevel P φ m k) hnmk
  set η : ℝ≥0∞ := ((k : ℝ≥0∞) + 1)⁻¹ with hη
  have hη0 : 0 < η := ENNReal.inv_pos.2 (by simp)
  -- step 1: `P^{n+m+2}(x, ·) ≥ η² ε φ(· ∩ D)` on `E`, as in (5.24)
  have hstep : ∀ x ∈ E, (η * η * ε) • φ.restrict D ≤ (P ^ ((n + 1) + (m + 1))) x := by
    intro x hx
    refine Measure.le_intro fun B hB _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
      Kernel.pow_add_apply_eq_lintegral P (n + 1) (m + 1) x hB]
    set W : Set (X × X) :=
      {q | (x, q.2) ∈ densLevel P φ n k ∧ (q.2, q.1) ∈ densLevel P φ m k} with hW
    have hWm : MeasurableSet W :=
      ((measurable_const.prodMk measurable_snd) (measurableSet_densLevel P φ n k)).inter
        ((measurable_snd.prodMk measurable_fst) (measurableSet_densLevel P φ m k))
    have hsec : ∀ z, ∫⁻ y, W.indicator (fun _ => η * η) (z, y) ∂φ =
        η * η * φ (Prod.mk x ⁻¹' densLevel P φ n k ∩
          (fun y => (y, z)) ⁻¹' densLevel P φ m k) := fun z => by
      have hfun : (fun y => W.indicator (fun _ => η * η) (z, y)) =
          (Prod.mk z ⁻¹' W).indicator (fun _ => η * η) := by
        ext y
        by_cases hy : (z, y) ∈ W <;> simp [hy]
      rw [hfun, lintegral_indicator_const (measurable_prodMk_left hWm)]
      rfl
    have hpt : ∀ z y, W.indicator (fun _ => η * η) (z, y) ≤
        transDensity P φ (n + 1) x y * transDensity P φ (m + 1) y z := fun z y => by
      by_cases hq : (z, y) ∈ W
      · rw [indicator_of_mem hq]
        exact mul_le_mul' hq.1 hq.2
      · rw [indicator_of_notMem hq]
        exact zero_le
    have hmeasW : Measurable (Function.uncurry fun z y => W.indicator (fun _ => η * η) (z, y)) :=
      measurable_const.indicator hWm
    calc η * η * ε * φ (B ∩ D) = ∫⁻ _ in B ∩ D, η * η * ε ∂φ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in B ∩ D, ∫⁻ y, W.indicator (fun _ => η * η) (z, y) ∂φ ∂φ := by
          refine setLIntegral_mono' (hB.inter hDm) fun z hz => ?_
          rw [hsec z]
          gcongr
          exact hF x hx z hz.2
      _ = ∫⁻ y, ∫⁻ z in B ∩ D, W.indicator (fun _ => η * η) (z, y) ∂φ ∂φ :=
          lintegral_lintegral_swap hmeasW.aemeasurable
      _ ≤ ∫⁻ y, transDensity P φ (n + 1) x y * (P ^ (m + 1)) y B ∂φ := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ z in B ∩ D, W.indicator (fun _ => η * η) (z, y) ∂φ
              ≤ ∫⁻ z in B ∩ D, transDensity P φ (n + 1) x y *
                  transDensity P φ (m + 1) y z ∂φ := lintegral_mono fun z => hpt z y
            _ = transDensity P φ (n + 1) x y *
                  ∫⁻ z in B ∩ D, transDensity P φ (m + 1) y z ∂φ :=
                lintegral_const_mul _ ((measurable_transDensity P φ (m + 1)).comp
                  (measurable_const.prodMk measurable_id))
            _ ≤ transDensity P φ (n + 1) x y * ∫⁻ z in B, transDensity P φ (m + 1) y z ∂φ := by
                gcongr
                exact inter_subset_left
            _ ≤ transDensity P φ (n + 1) x y * (P ^ (m + 1)) y B := by
                gcongr
                exact setLIntegral_transDensity_le P φ (m + 1) y hB
      _ ≤ ∫⁻ y, (P ^ (m + 1)) y B ∂(P ^ (n + 1)) x :=
          lintegral_transDensity_mul_le P φ (n + 1) x (Kernel.measurable_coe _ hB)
  -- step 2: pass from `E` to a subset `C` of `D` from which `E` is reached
  have hreach : ∀ z ∈ D, ∃ k', ∃ j : ℕ, (j : ℝ≥0∞)⁻¹ ≤ (P ^ (k' + 1)) z E := fun z hz => by
    obtain ⟨k', hk'⟩ := h E hEm hEA hEpos z (hDA hz)
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hk'.ne'
    exact ⟨k', j, hj.le⟩
  set Cs : ℕ → ℕ → Set X := fun k' j => D ∩ {z | (j : ℝ≥0∞)⁻¹ ≤ (P ^ (k' + 1)) z E}
  have hcov : D ⊆ ⋃ k', ⋃ j, Cs k' j := fun z hz => by
    obtain ⟨k', j, hj⟩ := hreach z hz
    exact mem_iUnion.2 ⟨k', mem_iUnion.2 ⟨j, hz, hj⟩⟩
  obtain ⟨k', hk'⟩ := exists_measure_pos_of_iUnion (hDpos.trans_le (measure_mono hcov))
  obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion hk'
  have hCm : MeasurableSet (Cs k' j) :=
    hDm.inter (measurableSet_le measurable_const (Kernel.measurable_coe _ hEm))
  refine ⟨Cs k' j, fun z hz => hDA hz.1, hCm, hj, (k' + 1) + ((n + 1) + (m + 1)), by omega,
    (j : ℝ≥0∞)⁻¹ * (η * η * ε), ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (by simp))
      (ENNReal.mul_pos (ENNReal.mul_pos hη0.ne' hη0.ne').ne' hε.ne').ne', fun x hx => ?_⟩
  refine le_trans ?_ (smul_le_pow_add_of_le P hstep x)
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, Measure.restrict_apply hB, Measure.restrict_apply hB, mul_assoc]
  gcongr
  · exact hx.2
  · exact inter_subset_left

/-- **(5.16)**, density form: under the conclusion of Theorem 5.2.1, for every `x ∈ C` the
density of `Pᵐ(x, ·)` with respect to `φ` is at least `δ` at `φ`-almost every `y ∈ C`. -/
theorem theorem_5_2_1_density_ge (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] {C : Set X} (hC : MeasurableSet C) {m : ℕ} {δ : ℝ≥0∞} {x : X}
    (hx : δ • φ.restrict C ≤ (P ^ m) x) : ∀ᵐ y ∂φ.restrict C, δ ≤ transDensity P φ m x y := by
  obtain ⟨-, hdec⟩ := theorem_5_2_1_density P φ m
  obtain ⟨Q, hQ, hQB⟩ := hdec x
  obtain ⟨S, hSm, hQS, hφS⟩ := hQ
  have hmeas : Measurable fun y => transDensity P φ m x y := Kernel.measurable_rnDeriv_right _ _ x
  -- the bad set inside `C ∩ S`, where the singular part vanishes
  set Bad := C ∩ S ∩ {y | transDensity P φ m x y < δ} with hBad
  have hBadm : MeasurableSet Bad :=
    (hC.inter hSm).inter (measurableSet_lt hmeas measurable_const)
  have hBad0 : φ Bad = 0 := by
    by_contra hpos
    have h1 := hx Bad
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hBadm,
      inter_eq_left.2 (fun y hy => hy.1.1), hQB Bad hBadm,
      measure_mono_null (fun y hy => hy.1.2) hQS, add_zero] at h1
    have hfin : ∫⁻ y in Bad, transDensity P φ m x y ∂φ ≠ ∞ := by
      have := isMarkovKernel_pow P m
      exact ne_top_of_le_ne_top (measure_ne_top ((P ^ m) x) Bad)
        (setLIntegral_transDensity_le P φ m x hBadm)
    have h2 : ∫⁻ y in Bad, transDensity P φ m x y ∂φ < ∫⁻ _ in Bad, δ ∂φ :=
      setLIntegral_strict_mono hBadm hpos measurable_const hfin
        (Filter.Eventually.of_forall fun y hy => hy.2)
    rw [setLIntegral_const] at h2
    exact absurd h1 (not_le.2 h2)
  have hS' : ∀ᵐ y ∂φ, y ∈ S := mem_ae_iff.2 hφS
  filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hS',
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hBad0)] with y hyC hyS hyB
  by_contra hlt
  push Not at hlt
  exact hyB ⟨⟨hyC, hyS⟩, hlt⟩

/-! ### Theorems 5.2.2 and 5.2.3 -/

/-- **Theorem 5.2.2** (MT p. 105). Let `B(X)` be countably generated and `ψ` a maximal
irreducibility measure. Every `A ∈ B⁺(X)` contains a `νₘ`-small set `C ∈ B⁺(X)` with
`νₘ(C) > 0`. -/
theorem theorem_5_2_2 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hψA : 0 < ψ A) :
    ∃ C ⊆ A, ∃ m ν, IsSmallSet P m ν C ∧ 0 < ψ C ∧ 0 < ν C := by
  obtain ⟨ψ', hψ', hprob, hψψ', -⟩ := theorem_4_0_1 P hψ.2.1 hψ.1
  obtain ⟨h1, h2⟩ := hψ.equiv hψ'
  have hψ'A : 0 < ψ' A := pos_iff_ne_zero.2 fun h0 => hψA.ne' (h1 h0)
  have hyp : ∀ B, MeasurableSet B → B ⊆ A → 0 < ψ' B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B :=
    fun B hB _ hpos x _ => (hitProb_pos_iff P hB x).1 (hψ'.2.1 B hB hpos x)
  obtain ⟨C, hCA, hCm, hψ'C, m, hm, δ, hδ, hC⟩ := theorem_5_2_1 P ψ' hA hψ'A hyp
  have hνC : 0 < (δ • ψ'.restrict C) C := by
    rw [Measure.smul_apply, Measure.restrict_apply hCm, inter_self, smul_eq_mul]
    exact ENNReal.mul_pos hδ.ne' hψ'C.ne'
  refine ⟨C, hCA, m, δ • ψ'.restrict C, ⟨hCm, hm, fun h0 => ?_, hC⟩,
    pos_iff_ne_zero.2 fun h0 => hψ'C.ne' (h2 h0), hνC⟩
  rw [h0] at hνC
  exact lt_irrefl _ hνC

/-- **Theorem 5.2.3** (MT p. 105), skeleton form. For a `ψ`-irreducible chain on a countably
generated space, the minorization condition (5.2) holds for some `m`-skeleton `Pᵐ`, on a set
`C ∈ B⁺(X)` and with `ν(Cᶜ) = 0`. -/
theorem theorem_5_2_3 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ m, 0 < m ∧ ∃ M : Minorization (P ^ m), M.IsConcentrated ∧ 0 < ψ M.C := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  exact ⟨m, hC.2.1, hC.minorization hνC, hC.minorization_isConcentrated hνC, hψC⟩

omit [MeasurableSpace.CountablyGenerated X] in
/-- The resolvent dominates its terms: `K_{a_ε}(x, ·) ≥ (1 − ε) εᵐ Pᵐ(x, ·)`. -/
theorem smul_pow_le_resolvent (P : Kernel X X) (ε : ℝ≥0∞) (m : ℕ) (x : X) :
    ((1 - ε) * ε ^ m) • (P ^ m) x ≤ resolvent P ε x :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul, resolvent_apply P ε x hB, mul_assoc]
    gcongr
    exact ENNReal.le_tsum (f := fun i => ε ^ i * (P ^ i) x B) m

/-- **Theorem 5.2.3** (MT p. 105), resolvent form: for `0 < ε < 1` the minorization condition
(5.2) holds for the `K_{a_ε}`-chain, on a set `C ∈ B⁺(X)` and with `ν(Cᶜ) = 0`. -/
theorem theorem_5_2_3_resolvent (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1) :
    haveI := isMarkovKernel_resolvent P hε1
    ∃ M : Minorization (resolvent P ε), M.IsConcentrated ∧ 0 < ψ M.C := by
  have := isMarkovKernel_resolvent P hε1
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hc : 0 < (1 - ε) * ε ^ m :=
    ENNReal.mul_pos (tsub_pos_of_lt hε1).ne' (pow_ne_zero _ hε0.ne')
  have hle : ∀ x ∈ C, ((1 - ε) * ε ^ m) • ν ≤ resolvent P ε x := fun x hx => by
    refine le_trans ?_ (smul_pow_le_resolvent P ε m x)
    refine Measure.le_intro fun B _ _ => ?_
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
    exact hC.2.2.2 x hx
  have hpos : 0 < (((1 - ε) * ε ^ m) • ν) C := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc.ne' hνC.ne'
  have hfin : (((1 - ε) * ε ^ m) • ν) C ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx C).trans prob_le_one)
  exact ⟨Minorization.ofLe hC.1 hle hpos hfin, Minorization.ofLe_isConcentrated _ _ _ _, hψC⟩

/-- **Proposition 5.2.4 (ii)** (MT p. 106). For a `ψ`-irreducible chain on a countably generated
space, `X` is a countable union of small sets: with `C` the small set of Theorem 5.2.2, the sets
`C̄(n, j) = {y : Pⁿ⁺¹(y, C) ≥ (j + 1)⁻¹}` of (5.27) are small and cover `X`. -/
theorem proposition_5_2_4_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ Cs : ℕ → ℕ → Set X, (∀ n j, IsSmall P (Cs n j)) ∧ ⋃ n, ⋃ j, Cs n j = univ := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  refine ⟨fun n j => {y | ((j : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ (n + 1)) y C}, fun n j => ?_, ?_⟩
  · exact ⟨(n + 1) + m, _, proposition_5_2_4_i P hC
      (measurableSet_le measurable_const (Kernel.measurable_coe _ hC.1))
      (ENNReal.inv_pos.2 (by simp)) fun x hx => hx⟩
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC.1 y).1 (hψ.2.1 C hC.1 hψC y)
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hn.ne'
    refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨j, ?_⟩⟩
    refine le_trans ?_ hj.le
    gcongr
    exact le_self_add

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Periods and cycles on a countable space (MT §5.4.1–5.4.2, Lemma D.7.4)

Meyn and Tweedie, §5.4.1–5.4.2, pp. 110–112, and Lemma D.7.4 of the appendix, which §5.4 uses.

**The g.c.d. of a set of times.**
* `setGcd S`: the greatest common divisor of `S ⊆ ℕ`, the largest common divisor of its
  elements. For an additively closed `S` with a positive element (`IsAddClosed`):
  `setGcd_dvd` (it divides every element), `dvd_setGcd` (every common divisor divides it),
  `setGcd_pos`, and **Lemma D.7.4** (`lemma_D_7_4`): `S` contains all large multiples of
  `setGcd S`. The proof uses the least positive difference of two elements of `S ∪ {0}`, which is
  the g.c.d. (`exists_gcd_witness`); no Bézout identity is needed.

**Countable spaces** (measurable singletons).
* `returnSet P α = {n ≥ 1 : Pⁿ(α, α) > 0}`, `periodAt P α = d(α)` (5.37), p. 111;
  `returnSet_isAddClosed`; `periodAt_dvd`: `Pⁿ(α, α) > 0` with `n ≥ 1` implies `d(α) ∣ n`.
* **Proposition 5.4.1** (`proposition_5_4_1`, p. 111): the period is a class property.
* **Proposition 5.4.2** (`proposition_5_4_2`, p. 111): an irreducible chain with period `d` has
  disjoint cyclic classes `D_i`, `i ∈ ZMod d`, covering `X`, with `P(x, D_{i+1}) = 1` on `D_i`
  (5.39).
* `IsAperiodicCountable`, `IsStronglyAperiodicCountable` (p. 112);
  `IsStronglyAperiodicCountable.isAperiodic`: strong aperiodicity implies aperiodicity.
* **Proposition 5.4.3** (`proposition_5_4_3`, p. 112): for `Pᵈ`, each cyclic class is absorbing
  and irreducible, and every state has period `1` for `Pᵈ`.
* `cycleChain`, `cycleChain_pow_self` (p. 110): the deterministic cycle `x ↦ x + 1` on
  `Fin (d + 1)` has `Pⁿ(x, x) > 0` iff `d + 1 ∣ n`, so every state has period `d + 1`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### The g.c.d. of an additively closed set of times -/

/-- `S ⊆ ℕ` is closed under addition. -/
def IsAddClosed (S : Set ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S

/-- The **greatest common divisor** of `S ⊆ ℕ`: the largest common divisor of its elements
(as used in (5.37) and (5.40)). -/
noncomputable def setGcd (S : Set ℕ) : ℕ := sSup {d | ∀ s ∈ S, d ∣ s}

/-- Multiples `(q + 1) b` of an element of an additively closed set lie in it. -/
theorem IsAddClosed.succ_mul_mem {S : Set ℕ} (hS : IsAddClosed S) {b : ℕ} (hb : b ∈ S) (q : ℕ) :
    (q + 1) * b ∈ S := by
  induction q with
  | zero => simpa using hb
  | succ q ih => rw [add_mul, one_mul]; exact hS _ ih _ hb

/-- Multiples `q b` of an element of `S ∪ {0}` lie in `S ∪ {0}`. -/
theorem IsAddClosed.mul_mem_zero {S : Set ℕ} (hS : IsAddClosed S) {b : ℕ} (hb : b = 0 ∨ b ∈ S)
    (q : ℕ) : q * b = 0 ∨ q * b ∈ S := by
  rcases hb with rfl | hb
  · left; simp
  · rcases q with _ | q
    · left; simp
    · exact Or.inr (hS.succ_mul_mem hb q)

/-- The sum of an element of `S ∪ {0}` and an element of `S` lies in `S`. -/
theorem IsAddClosed.add_mem_of_zero {S : Set ℕ} (hS : IsAddClosed S) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
  rcases ha with rfl | ha
  · simpa using hb
  · exact hS _ ha _ hb

/-- **The g.c.d. as a least difference.** If `S` is additively closed and has a positive element,
the least positive difference `g = b − a` of elements of `S ∪ {0}` (with `b ∈ S`) divides every
element of `S`, and every common divisor of `S` divides it. -/
theorem exists_gcd_witness {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
    (hpos : 0 < s₀) :
    ∃ g a, 0 < g ∧ (a = 0 ∨ a ∈ S) ∧ a + g ∈ S ∧ (∀ s ∈ S, g ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ g := by
  set T : Set ℕ := {g | 0 < g ∧ ∃ a, (a = 0 ∨ a ∈ S) ∧ a + g ∈ S} with hT
  have hTne : T.Nonempty := ⟨s₀, hpos, 0, Or.inl rfl, by simpa using hs₀⟩
  obtain ⟨hgpos, a, ha, hag⟩ := Nat.sInf_mem hTne
  set g := sInf T
  refine ⟨g, a, hgpos, ha, hag, fun s hs => ?_, fun d hd => ?_⟩
  · -- the remainder of `s` modulo `g` is a smaller positive difference unless it is `0`
    by_contra hdvd
    have hr : 0 < s % g := Nat.pos_of_ne_zero fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hrT : s % g ∈ T := by
      refine ⟨hr, s / g * (a + g), hS.mul_mem_zero (Or.inr hag) _, ?_⟩
      have hsplit : s / g * (a + g) + s % g = s / g * a + s := by
        have := Nat.div_add_mod s g
        nlinarith [this]
      rw [hsplit]
      exact hS.add_mem_of_zero (hS.mul_mem_zero ha _) hs
    exact absurd (Nat.sInf_le hrT) (not_le.2 (Nat.mod_lt s hgpos))
  · have h1 : d ∣ a := by
      rcases ha with rfl | ha
      · exact dvd_zero d
      · exact hd a ha
    exact (Nat.dvd_add_right h1).1 (hd _ hag)

/-- For an additively closed `S` with a positive element, `setGcd S` is the least positive
difference of `exists_gcd_witness`. -/
theorem setGcd_spec {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ a, 0 < setGcd S ∧ (a = 0 ∨ a ∈ S) ∧ a + setGcd S ∈ S ∧ (∀ s ∈ S, setGcd S ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ setGcd S := by
  obtain ⟨g, a, hg, ha, hag, hdvd, hmax⟩ := exists_gcd_witness hS hs₀ hpos
  have heq : setGcd S = g := by
    refine IsGreatest.csSup_eq ⟨hdvd, fun d hd => Nat.le_of_dvd hg (hmax d hd)⟩
  rw [heq]
  exact ⟨a, hg, ha, hag, hdvd, hmax⟩

/-- `setGcd S` divides every element of `S`. -/
theorem setGcd_dvd {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {s : ℕ} (hs : s ∈ S) : setGcd S ∣ s := by
  obtain ⟨a, -, -, -, h, -⟩ := setGcd_spec hS hs₀ hpos
  exact h s hs

/-- Every common divisor of `S` divides `setGcd S`. -/
theorem dvd_setGcd {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {d : ℕ} (hd : ∀ s ∈ S, d ∣ s) : d ∣ setGcd S := by
  obtain ⟨a, -, -, -, -, h⟩ := setGcd_spec hS hs₀ hpos
  exact h d hd

/-- `setGcd S > 0`. -/
theorem setGcd_pos {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    0 < setGcd S := by
  obtain ⟨a, h, -⟩ := setGcd_spec hS hs₀ hpos
  exact h

/-- **Lemma D.7.4** (MT p. 549, used in §5.4): an additively closed set of naturals with a positive
element contains every large enough multiple of its g.c.d. -/
theorem lemma_D_7_4 {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ N, ∀ n ≥ N, n * setGcd S ∈ S := by
  obtain ⟨a, hg, ha, hag, hdvd, -⟩ := setGcd_spec hS hs₀ hpos
  set g := setGcd S
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact hS.succ_mul_mem (by simpa using hag) q
  · have haS : a ∈ S := ha.resolve_left ha0
    obtain ⟨k, hk⟩ := hdvd a haS
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => ha0 (by rw [hk, h, mul_zero])
    refine ⟨k * k, fun n hn => ?_⟩
    have hx : k ≤ n / k := (Nat.le_div_iff_mul_le hk0).2 hn
    have hr : n % k < k := Nat.mod_lt n hk0
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt (hr.trans_le hx)
    -- `n g = (t + 1) a + (n % k) (a + g)`
    have hsplit : n * g = (t + 1) * a + n % k * (a + g) := by
      have h1 := Nat.div_add_mod n k
      rw [ht] at h1
      rw [hk]
      nlinarith [h1]
    rw [hsplit]
    rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
    · rw [h0, zero_mul, add_zero]; exact hS.succ_mul_mem haS t
    · obtain ⟨r, hr'⟩ := Nat.exists_eq_add_of_lt h0
      rw [hr', zero_add]
      exact hS _ (hS.succ_mul_mem haS t) _ (hS.succ_mul_mem hag r)

/-! ### The period of a state on a countable space -/

variable {X : Type*} [MeasurableSpace X]

/-- The return times `{n ≥ 1 : Pⁿ(α, α) > 0}` of a state `α`. -/
def returnSet (P : Kernel X X) (α : X) : Set ℕ := {n | 0 < n ∧ 0 < (P ^ n) α {α}}

/-- The **period** `d(α) = g.c.d.{n ≥ 1 : Pⁿ(α, α) > 0}` of a state (5.37), MT p. 111. -/
noncomputable def periodAt (P : Kernel X X) (α : X) : ℕ := setGcd (returnSet P α)

/-- A chain that moves from `D i` into `D (i + 1)` with probability one moves from `D i` into
`D (i + n)` in `n` steps with probability one. -/
theorem pow_apply_eq_one_of_step (P : Kernel X X) [IsMarkovKernel P] {d : ℕ}
    {D : ZMod d → Set X} (hD : ∀ i, MeasurableSet (D i))
    (hstep : ∀ i, ∀ x ∈ D i, P x (D (i + 1)) = 1) (n : ℕ) :
    ∀ i, ∀ x ∈ D i, (P ^ n) x (D (i + n)) = 1 := by
  induction n with
  | zero =>
    intro i x hx
    rw [pow_zero_apply, Nat.cast_zero, add_zero, Measure.dirac_apply' _ (hD i),
      indicator_of_mem hx, Pi.one_apply]
  | succ n ih =>
    intro i x hx
    have := isMarkovKernel_pow P n
    have := isMarkovKernel_pow P (n + 1)
    refine le_antisymm prob_le_one ?_
    rw [pow_succ_apply' P n x (hD _)]
    calc (1 : ℝ≥0∞) = (P ^ n) x (D (i + n)) := (ih i x hx).symm
      _ = ∫⁻ y in D (i + n), 1 ∂(P ^ n) x := by rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ y in D (i + n), P y (D (i + ↑(n + 1))) ∂(P ^ n) x := by
          refine setLIntegral_mono (Kernel.measurable_coe _ (hD _)) fun y hy => ?_
          rw [Nat.cast_succ, ← add_assoc, hstep _ y hy]
      _ ≤ ∫⁻ y, P y (D (i + ↑(n + 1))) ∂(P ^ n) x := setLIntegral_le_lintegral _ _

variable [MeasurableSingletonClass X]

/-- The return times are closed under addition: `P^{m+n}(α, α) ≥ Pᵐ(α, α) Pⁿ(α, α)`. -/
theorem returnSet_isAddClosed (P : Kernel X X) (α : X) : IsAddClosed (returnSet P α) :=
  fun m hm n hn => ⟨Nat.add_pos_left hm.1 n,
    (ENNReal.mul_pos hm.2.ne' hn.2.ne').trans_le (pow_add_singleton_ge P m n α α α)⟩

/-- MT p. 111: `Pⁿ(α, α) = 0` unless `d(α)` divides `n` (for `n ≥ 1`). -/
theorem periodAt_dvd (P : Kernel X X) {α : X} {n : ℕ} (hn : n ∈ returnSet P α) :
    periodAt P α ∣ n :=
  setGcd_dvd (returnSet_isAddClosed P α) hn hn.1 hn

/-- If `α ↔ y` with `α ≠ y`, there are `m, n ≥ 1` with `Pᵐ(α, y) > 0` and `Pⁿ(y, α) > 0`. -/
theorem exists_pow_pos_of_communicates (P : Kernel X X) [IsMarkovKernel P] {α y : X}
    (h : Communicates P α y) (hne : α ≠ y) :
    ∃ m n, 0 < m ∧ 0 < n ∧ 0 < (P ^ m) α {y} ∧ 0 < (P ^ n) y {α} := by
  obtain ⟨m, hm⟩ := (hitProb_pos_iff P (measurableSet_singleton y) α).1 (h.1.resolve_left hne)
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P (measurableSet_singleton α) y).1
    (h.2.resolve_left (Ne.symm hne))
  exact ⟨m + 1, n + 1, by omega, by omega, hm, hn⟩

/-- Every return time of `y` is a return time of `α` minus a fixed return time, when
`α ↔ y`: `d(α)` divides every return time of `y`. -/
theorem periodAt_dvd_of_communicates (P : Kernel X X) [IsMarkovKernel P] {α y : X}
    (h : Communicates P α y) {k : ℕ} (hk : k ∈ returnSet P y) : periodAt P α ∣ k := by
  by_cases hne : α = y
  · subst hne; exact periodAt_dvd P hk
  obtain ⟨m, n, hm0, hn0, hm, hn⟩ := exists_pow_pos_of_communicates P h hne
  have h1 : m + n ∈ returnSet P α :=
    ⟨by omega, (ENNReal.mul_pos hm.ne' hn.ne').trans_le (pow_add_singleton_ge P m n α y α)⟩
  have h2 : m + k + n ∈ returnSet P α := by
    refine ⟨by omega, ?_⟩
    have h3 := (ENNReal.mul_pos hm.ne' hk.2.ne').trans_le (pow_add_singleton_ge P m k α y y)
    exact (ENNReal.mul_pos h3.ne' hn.ne').trans_le (pow_add_singleton_ge P (m + k) n α y α)
  have := periodAt_dvd P h2
  rw [show m + k + n = k + (m + n) by omega] at this
  exact (Nat.dvd_add_left (periodAt_dvd P h1)).1 this

/-- **Proposition 5.4.1** (MT p. 111): if `y ∈ C(α)` then `d(α) = d(y)`. -/
theorem proposition_5_4_1 (P : Kernel X X) [IsMarkovKernel P] {α y : X}
    (h : y ∈ commClass P α) : periodAt P α = periodAt P y := by
  by_cases hne : α = y
  · rw [hne]
  obtain ⟨m, n, hm0, hn0, hm, hn⟩ := exists_pow_pos_of_communicates P h hne
  have hα : m + n ∈ returnSet P α :=
    ⟨by omega, (ENNReal.mul_pos hm.ne' hn.ne').trans_le (pow_add_singleton_ge P m n α y α)⟩
  have hy : n + m ∈ returnSet P y :=
    ⟨by omega, (ENNReal.mul_pos hn.ne' hm.ne').trans_le (pow_add_singleton_ge P n m y α y)⟩
  refine Nat.dvd_antisymm ?_ ?_
  · exact dvd_setGcd (returnSet_isAddClosed P y) hy hy.1
      fun k hk => periodAt_dvd_of_communicates P h hk
  · exact dvd_setGcd (returnSet_isAddClosed P α) hα hα.1
      fun k hk => periodAt_dvd_of_communicates P ((proposition_4_1_1 P).symm h) hk

variable [Countable X]

/-- An irreducible chain on a nonempty space returns to every state: for every `y` there is
`M ≥ 1` with `Pᴹ(y, α) > 0`. -/
theorem exists_return_pow_pos (P : Kernel X X) [IsMarkovKernel P] [Nonempty X]
    (hP : IsIrreducibleChain P) (y α : X) : ∃ M, 0 < M ∧ 0 < (P ^ M) y {α} := by
  have hc : ∀ x, ∃ M, 0 < (P ^ (M + 1)) x {α} := fun x => by
    rcases ((isIrreducibleChain_iff P).1 hP x α).1 with h | h
    · subst h
      -- the chain leaves `α` to some state, which leads back to `α`
      have h1 : 0 < P x univ := by simp
      have hsum : ∃ z, 0 < (P ^ 1) x {z} := by
        rw [pow_one]
        by_contra hz
        push Not at hz
        have : P x univ = 0 := by
          rw [← iUnion_of_singleton (α := X)]
          exact measure_iUnion_null_iff.2 fun z => nonpos_iff_eq_zero.1 (hz z)
        exact h1.ne' this
      obtain ⟨z, hz⟩ := hsum
      obtain ⟨n, hn⟩ := (leads_iff_exists_pow P z x).1 ((isIrreducibleChain_iff P).1 hP z x).1
      exact ⟨n, by
        have := (ENNReal.mul_pos hz.ne' hn.ne').trans_le (pow_add_singleton_ge P 1 n x z x)
        rwa [add_comm] at this⟩
    · exact (hitProb_pos_iff P (measurableSet_singleton α) x).1 h
  obtain ⟨M, hM⟩ := hc y
  exact ⟨M + 1, by omega, hM⟩

omit [MeasurableSingletonClass X] [Countable X] in
/-- The cyclic class of `y` relative to a base state `α`: the class mod `d` of the times `k` with
`Pᵏ(α, y) > 0`. -/
def cyclicClass (P : Kernel X X) (α : X) (d : ℕ) (i : ZMod d) : Set X :=
  {y | ∃ k : ℕ, (k : ZMod d) = i ∧ 0 < (P ^ k) α {y}}

/-- **Proposition 5.4.2** (MT p. 111). Let `Φ` be an irreducible chain on a countable space and
`d = d(α)` the common period. The cyclic classes `D_i`, `i ∈ ZMod d`, are disjoint, cover `X`,
and `P(x, D_{i+1}) = 1` for `x ∈ D_i` (5.39). -/
theorem proposition_5_4_2 (P : Kernel X X) [IsMarkovKernel P] [Nonempty X]
    (hP : IsIrreducibleChain P) (α : X) :
    (∀ i j : ZMod (periodAt P α), i ≠ j →
        Disjoint (cyclicClass P α (periodAt P α) i) (cyclicClass P α (periodAt P α) j)) ∧
      (⋃ i, cyclicClass P α (periodAt P α) i) = univ ∧
      ∀ i, ∀ x ∈ cyclicClass P α (periodAt P α) i,
        P x (cyclicClass P α (periodAt P α) (i + 1)) = 1 := by
  set d := periodAt P α
  refine ⟨fun i j hij => Set.disjoint_left.2 fun y hi hj => hij ?_, ?_, fun i x hx => ?_⟩
  · obtain ⟨k, rfl, hk⟩ := hi
    obtain ⟨k', rfl, hk'⟩ := hj
    obtain ⟨M, hM0, hM⟩ := exists_return_pow_pos P hP y α
    have h1 : k + M ∈ returnSet P α :=
      ⟨by omega, (ENNReal.mul_pos hk.ne' hM.ne').trans_le (pow_add_singleton_ge P k M α y α)⟩
    have h2 : k' + M ∈ returnSet P α :=
      ⟨by omega, (ENNReal.mul_pos hk'.ne' hM.ne').trans_le (pow_add_singleton_ge P k' M α y α)⟩
    have e1 := (ZMod.natCast_eq_zero_iff _ _).2 (periodAt_dvd P h1)
    have e2 := (ZMod.natCast_eq_zero_iff _ _).2 (periodAt_dvd P h2)
    push_cast at e1 e2
    exact add_right_cancel (e1.trans e2.symm)
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := (leads_iff_exists_pow P α y).1 ((isIrreducibleChain_iff P).1 hP α y).1
    exact ⟨k, k, rfl, hk⟩
  · obtain ⟨k, rfl, hk⟩ := hx
    have hzero : P x (cyclicClass P α d ((k : ZMod d) + 1))ᶜ = 0 := by
      by_contra hne
      obtain ⟨y, hy, hpos⟩ := exists_singleton_pos_of_pos (P x) (pos_iff_ne_zero.2 hne)
      refine hy ⟨k + 1, by push_cast; rfl, ?_⟩
      have := (ENNReal.mul_pos hk.ne' (by rw [pow_one]; exact hpos.ne')).trans_le
        (pow_add_singleton_ge P k 1 α x y)
      exact this
    rw [prob_compl_eq_zero_iff (measurableSet_of_countable _)] at hzero
    exact hzero

/-- An irreducible chain on a countable space is **aperiodic** if `d(x) = 1` for every `x`
(MT p. 112). -/
def IsAperiodicCountable (P : Kernel X X) : Prop := ∀ x, periodAt P x = 1

/-- An irreducible chain on a countable space is **strongly aperiodic** if `P(x, x) > 0` for some
`x` (MT p. 112). -/
def IsStronglyAperiodicCountable (P : Kernel X X) : Prop := ∃ x, 0 < P x {x}

omit [Countable X] in
/-- A strongly aperiodic irreducible chain is aperiodic: `1` is a return time, so the common
period is `1`. -/
theorem IsStronglyAperiodicCountable.isAperiodic {P : Kernel X X} [IsMarkovKernel P]
    [Nonempty X] (hP : IsIrreducibleChain P) (h : IsStronglyAperiodicCountable P) :
    IsAperiodicCountable P := by
  obtain ⟨x, hx⟩ := h
  intro y
  have h1 : 1 ∈ returnSet P x := ⟨one_pos, by rwa [pow_one]⟩
  rw [← proposition_5_4_1 P (((isIrreducibleChain_iff P).1 hP) x y)]
  exact Nat.dvd_one.1 (periodAt_dvd P h1)

/-- **Proposition 5.4.3** (MT p. 112). Let `Φ` be irreducible on a countable space, with period
`d` and cyclic classes `D_i`. For the chain `Φ_d` with transition matrix `Pᵈ`: each `D_i` is
absorbing, any two states of `D_i` communicate under `Pᵈ`, and every state has period `1` under
`Pᵈ`. -/
theorem proposition_5_4_3 (P : Kernel X X) [IsMarkovKernel P] [Nonempty X]
    (hP : IsIrreducibleChain P) (α : X) :
    (∀ i, ∀ x ∈ cyclicClass P α (periodAt P α) i,
        (P ^ periodAt P α) x (cyclicClass P α (periodAt P α) i) = 1) ∧
      (∀ i, ∀ x ∈ cyclicClass P α (periodAt P α) i, ∀ y ∈ cyclicClass P α (periodAt P α) i,
        ∃ q, 0 < ((P ^ periodAt P α) ^ q) x {y}) ∧
      ∀ x, periodAt (P ^ periodAt P α) x = 1 := by
  set d := periodAt P α with hd
  obtain ⟨hdisj, -, hstep⟩ := proposition_5_4_2 P hP α
  have hmeas : ∀ i, MeasurableSet (cyclicClass P α d i) := fun i => measurableSet_of_countable _
  have hpow := pow_apply_eq_one_of_step P hmeas hstep
  have hperiod : ∀ x, periodAt P x = d := fun x =>
    (proposition_5_4_1 P (((isIrreducibleChain_iff P).1 hP) α x)).symm
  refine ⟨fun i x hx => ?_, fun i x hx y hy => ?_, fun x => ?_⟩
  · have := hpow d i x hx
    rwa [ZMod.natCast_self, add_zero] at this
  · obtain ⟨k, hk⟩ := (leads_iff_exists_pow P x y).1 (((isIrreducibleChain_iff P).1 hP) x y).1
    -- `y ∈ D_{i+k}`, hence `d ∣ k`
    have hyk : y ∈ cyclicClass P α d (i + k) := by
      have := isMarkovKernel_pow P k
      by_contra hc
      have h1 := hpow k i x hx
      rw [← prob_compl_eq_zero_iff (hmeas _)] at h1
      exact hk.ne' (measure_mono_null (singleton_subset_iff.2 hc) h1)
    have hik : i + k = i := by
      by_contra hne
      exact Set.disjoint_left.1 (hdisj _ _ hne) hyk hy
    have hdk : d ∣ k := (ZMod.natCast_eq_zero_iff k d).1 (by
      have := congrArg (fun z => z - i) hik
      simpa using this)
    obtain ⟨q, rfl⟩ := hdk
    exact ⟨q, by rwa [← pow_mul]⟩
  · have hd0 : 0 < d := by
      obtain ⟨M, hM0, hM⟩ := exists_return_pow_pos P hP α α
      exact setGcd_pos (returnSet_isAddClosed P α) ⟨hM0, hM⟩ hM0
    -- a return time of `x` for `Pᵈ`
    obtain ⟨M, hM0, hM⟩ := exists_return_pow_pos P hP x x
    have hMr : M ∈ returnSet P x := ⟨hM0, hM⟩
    obtain ⟨q₀, hq₀⟩ := hperiod x ▸ periodAt_dvd P hMr
    have hq₀r : q₀ ∈ returnSet (P ^ d) x := by
      refine ⟨Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq₀; omega, ?_⟩
      rw [← pow_mul, ← hq₀]; exact hM
    -- `d · d'(x)` divides every return time of `x`
    have hdvd : d * periodAt (P ^ d) x ∣ periodAt P x := by
      refine dvd_setGcd (returnSet_isAddClosed P x) hMr hM0 fun n hn => ?_
      obtain ⟨q, rfl⟩ := hperiod x ▸ periodAt_dvd P hn
      have hq : q ∈ returnSet (P ^ d) x :=
        ⟨Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hn; exact lt_irrefl _ hn.1,
          by rw [← pow_mul]; exact hn.2⟩
      exact Nat.mul_dvd_mul_left d (periodAt_dvd (P ^ d) hq)
    rw [hperiod x] at hdvd
    have h1 : d * periodAt (P ^ d) x ∣ d * 1 := by rwa [mul_one]
    exact Nat.dvd_one.1 ((Nat.mul_dvd_mul_iff_left hd0).1 h1)

/-! ### The deterministic cycle (MT p. 110) -/

/-- The deterministic cycle `x ↦ x + 1` on `{0, …, d}` (MT p. 110). -/
noncomputable def cycleChain (d : ℕ) : Kernel (Fin (d + 1)) (Fin (d + 1)) :=
  Kernel.deterministic (fun x => x + 1) (measurable_of_countable _)

open Fin.NatCast in
/-- The `n`-step kernel of the cycle is the shift by `n`. -/
theorem cycleChain_pow (d n : ℕ) :
    cycleChain d ^ n = Kernel.deterministic (fun x => x + (n : Fin (d + 1)))
      (measurable_of_countable _) := by
  induction n with
  | zero =>
    ext1 x
    rw [pow_zero]
    change Kernel.id x = _
    simp [Kernel.id, Kernel.deterministic_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    change Kernel.deterministic _ _ ∘ₖ Kernel.deterministic _ _ = _
    rw [Kernel.deterministic_comp_deterministic]
    congr 1
    ext1 x
    simp only [Function.comp, Nat.cast_succ]
    abel

open Fin.NatCast in
/-- MT p. 110: in the deterministic cycle, `Pⁿ(x, x) > 0` iff `n` is a multiple of `d + 1`. -/
theorem cycleChain_pow_self (d n : ℕ) (x : Fin (d + 1)) :
    0 < (cycleChain d ^ n) x {x} ↔ (d + 1) ∣ n := by
  rw [cycleChain_pow, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton x)]
  have : (x + (n : Fin (d + 1)) ∈ ({x} : Set (Fin (d + 1)))) ↔ (d + 1) ∣ n := by
    rw [mem_singleton_iff, add_eq_left, Fin.natCast_eq_zero]
  by_cases h : (d + 1) ∣ n
  · rw [indicator_of_mem (this.2 h)]; simp [h]
  · rw [indicator_of_notMem (fun h' => h (this.1 h'))]; simp [h]

/-- Every state of the deterministic cycle on `d + 1` points has period `d + 1` (MT p. 110). -/
theorem periodAt_cycleChain (d : ℕ) (x : Fin (d + 1)) : periodAt (cycleChain d) x = d + 1 := by
  have hmem : d + 1 ∈ returnSet (cycleChain d) x :=
    ⟨by omega, (cycleChain_pow_self d _ x).2 dvd_rfl⟩
  have hS := returnSet_isAddClosed (cycleChain d) x
  refine Nat.dvd_antisymm (periodAt_dvd _ hmem) (dvd_setGcd hS hmem (by omega) fun n hn => ?_)
  exact (cycleChain_pow_self d n x).1 hn.2

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cycles for a general state space chain (MT §5.4.3)

Meyn and Tweedie, §5.4.3, pp. 112–115. `ψ` is a maximal irreducibility measure.

* `IsCycle P ψ d D` (Theorem 5.4.4, p. 113): a `d`-cycle, disjoint measurable sets `D i`,
  `i ∈ ZMod d`, with `P(x, D_{i+1}) = 1` on `D_i` and `ψ`-null complement of `⋃ D_i`;
  `IsCycle.pow_apply`: `Pⁿ(x, D_{i+n}) = 1` on `D_i`.
* `smallTimes P C ν = E_C` (5.40), p. 112: the times `n ≥ 1` at which `C` is small with a
  multiple of `ν` as minorizing measure; `smallTimes_isAddClosed` (p. 113) and
  `mem_smallTimes_of_isSmallSet`.
* `IsSmallSet.isPhiIrreducible`: the minorizing measure of a small set in `B⁺(X)` is an
  irreducibility measure (used on p. 114, and Proposition 5.5.4 (ii) for small sets).
* `cycleSet P C d i = D*_i` (p. 113), `iUnion_cycleSet`, and the key estimate
  `measure_cycleSet_inter`: `ψ(D*_i ∩ D*_k) = 0` for `i ≠ k`.
* **Theorem 5.4.4** (`theorem_5_4_4`, p. 113): if `C ∈ B⁺(X)` is `ν_M`-small with `ν(C) > 0` and
  `d = g.c.d. E_C`, there is a `d`-cycle, and every `d'`-cycle has `d' ∣ d`;
  `theorem_5_4_4_unique`: the cycle is unique up to `ψ`-null sets and a relabelling
  `i ↦ k + i`, and every cycle class of a `d'`-cycle contains a cycle class of the `d`-cycle
  up to a `ψ`-null set.
* `exists_isSmallSet_mul_gcd` (p. 113, from Lemma D.7.4): `C` is `δₙν`-small at every large
  multiple of `d`; `exists_class_subset_ae` (p. 114): a small set lies, up to a null set, in one
  class of any cycle.
* `IsPeriod P ψ d` (p. 114): `d` is the largest `d` for which a `d`-cycle exists; `isPeriod_gcd`,
  `IsPeriod.eq_gcd`: the period is `g.c.d. E_C` for every such `C`; `exists_isPeriod`: on a
  countably generated space every `ψ`-irreducible chain has a period; `IsAperiodic`,
  `IsStronglyAperiodic`.
* `smallTimes_smul`: `E_C` does not change when `ν` is scaled; `isPhiIrreducible_of_pow_skeleton`:
  irreducibility of a skeleton passes to the chain;
  `exists_forall_mem_smallTimes_of_aperiodic`: for an aperiodic chain `E_C` contains every
  large time.
* **Proposition 5.4.5** (p. 114): (i) `proposition_5_4_5_i`, a strongly aperiodic chain
  satisfies the minorization condition (5.2); (ii) `proposition_5_4_5_ii`, the resolvent is
  strongly aperiodic; (iii) `proposition_5_4_5_iii`, for an aperiodic chain every skeleton is
  `ψ`-irreducible and aperiodic and some skeleton is strongly aperiodic.
* **Proposition 5.4.6** (`proposition_5_4_6`, p. 115): each cycle class is absorbing and
  `ψ`-irreducible for `Pᵈ`; the aperiodicity of `Pᵈ` on each class is
  `proposition_5_4_6_aperiodic` in `CycleAperiodic`.

**Corrections and hypotheses.** Theorem 5.4.4 as stated takes any `ν_M`-small `C ∈ B⁺(X)`; the
proof needs `ν_M(C) > 0` (assumed "without loss of generality" on p. 112, via Proposition 5.2.4
(iii)), and it is a hypothesis here. In the uniqueness statement the book's "`Dᵢ = D'ᵢ` a.e. after
reordering" is the shift `i ↦ k + i`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Cycles -/

variable (P : Kernel X X) (ψ : Measure X) (d : ℕ) in
/-- A **`d`-cycle** (MT Theorem 5.4.4, p. 113): disjoint measurable sets `D i`, `i ∈ ZMod d`,
with `P(x, D_{i+1}) = 1` for `x ∈ D_i`, whose union has `ψ`-null complement. -/
structure IsCycle (D : ZMod d → Set X) : Prop where
  /-- Each class is measurable. -/
  measurableSet : ∀ i, MeasurableSet (D i)
  /-- The classes are disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j)
  /-- The chain moves from `D i` to `D (i + 1)`. -/
  step : ∀ i, ∀ x ∈ D i, P x (D (i + 1)) = 1
  /-- `N = (⋃ D_i)ᶜ` is `ψ`-null. -/
  null_compl : ψ (⋃ i, D i)ᶜ = 0

/-- On a cycle, `Pⁿ(x, D_{i+n}) = 1` for `x ∈ D_i`. -/
theorem IsCycle.pow_apply {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    {D : ZMod d → Set X} (h : IsCycle P ψ d D) (n : ℕ) {i : ZMod d} {x : X} (hx : x ∈ D i) :
    (P ^ n) x (D (i + n)) = 1 :=
  pow_apply_eq_one_of_step P h.measurableSet h.step n i x hx

/-- On a cycle, `Pⁿ(x, D_j) = 0` for `x ∈ D_i` and `j ≠ i + n`. -/
theorem IsCycle.pow_apply_eq_zero {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    {D : ZMod d → Set X} (h : IsCycle P ψ d D) (n : ℕ) {i j : ZMod d} {x : X} (hx : x ∈ D i)
    (hj : j ≠ i + n) : (P ^ n) x (D j) = 0 := by
  have := isMarkovKernel_pow P n
  have h1 := h.pow_apply n hx
  rw [← prob_compl_eq_zero_iff (h.measurableSet _)] at h1
  exact measure_mono_null (Set.disjoint_left.1 (h.disjoint _ _ hj)) h1

/-! ### The set `E_C` of small times -/

/-- `E_C` (5.40), MT p. 112: the times `n ≥ 1` at which `C` is `δₙν`-small for some `δₙ > 0`. -/
def smallTimes (P : Kernel X X) (C : Set X) (ν : Measure X) : Set ℕ :=
  {n | 0 < n ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ C, δ • ν ≤ (P ^ n) x}

/-- Scalar multiplication of measures is monotone in the scalar. -/
theorem smul_measure_le_smul {a b : ℝ≥0∞} (h : a ≤ b) (μ : Measure X) : a • μ ≤ b • μ :=
  Measure.le_intro fun B _ _ => by
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_left h _

/-- `E_C` is closed under addition when `ν(C) > 0` (MT p. 113):
`P^{n+m}(x, B) ≥ ∫_C Pⁿ(x, dy) Pᵐ(y, B) ≥ δₙ ν(C) δₘ ν(B)`. -/
theorem smallTimes_isAddClosed (P : Kernel X X) {C : Set X} {ν : Measure X} (hνC : 0 < ν C) :
    IsAddClosed (smallTimes P C ν) := by
  rintro n ⟨hn, δn, hδn, hn'⟩ m ⟨hm, δm, hδm, hm'⟩
  refine ⟨Nat.add_pos_left hn m, δn * ν C * δm, ENNReal.mul_pos (ENNReal.mul_pos hδn.ne'
    hνC.ne').ne' hδm.ne', fun x hx => ?_⟩
  have h1 : δn * ν C ≤ (P ^ n) x C := by
    have := hn' x hx C
    rwa [Measure.smul_apply, smul_eq_mul] at this
  calc (δn * ν C * δm) • ν = (δn * ν C) • (δm • ν) := by rw [smul_smul]
    _ ≤ ((P ^ n) x C) • (δm • ν) := smul_measure_le_smul h1 _
    _ ≤ (P ^ (n + m)) x := smul_le_pow_add_of_le P hm' x

/-- The index of a `ν_M`-small set lies in `E_C`. -/
theorem mem_smallTimes_of_isSmallSet {P : Kernel X X} {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) : M ∈ smallTimes P C ν :=
  ⟨hC.2.1, 1, one_pos, fun x hx => by rw [one_smul]; exact hC.2.2.2 x hx⟩

/-- An element of `E_C` makes `C` small. -/
theorem isSmallSet_of_mem_smallTimes {P : Kernel X X} {ν : Measure X} {C : Set X}
    (hCm : MeasurableSet C) (hν : ν ≠ 0) {n : ℕ} (hn : n ∈ smallTimes P C ν) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ IsSmallSet P n (δ • ν) C := by
  obtain ⟨hn0, δ, hδ, h⟩ := hn
  exact ⟨δ, hδ, hCm, hn0, smul_measure_ne_zero hν hδ.ne', h⟩

/-- The minorizing measure of a small set `C` with `φ(C) > 0` is an irreducibility measure
(MT p. 114; Proposition 5.5.4 (ii) for small sets). -/
theorem IsSmallSet.isPhiIrreducible {P : Kernel X X} [IsMarkovKernel P] {M : ℕ} {ν : Measure X}
    {C : Set X} (hC : IsSmallSet P M ν C) {φ : Measure X} (hφ : IsPhiIrreducible P φ)
    (hφC : 0 < φ C) : IsPhiIrreducible P ν := by
  intro B hB hνB x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC.1 x).1 (hφ C hC.1 hφC x)
  have h1 := pow_add_ge_of_le P (m := n + 1) hC.2.2.2 x hB
  have h2 := pow_le_hitProb P hB (n + M) x
  rw [show n + M + 1 = n + 1 + M by omega] at h2
  exact (ENNReal.mul_pos hn.ne' hνB.ne').trans_le (h1.trans h2)

/-- `(∫ c dμ) ρ ≤ μK` when `c(y) ρ ≤ K(y, ·)` for every `y`. -/
theorem smul_le_comp_of_le {Y : Type*} [MeasurableSpace Y] (K : Kernel X Y) (μ : Measure X)
    {ρ : Measure Y} {c : X → ℝ≥0∞} (hc : Measurable c) (h : ∀ y, c y • ρ ≤ K y) :
    (∫⁻ y, c y ∂μ) • ρ ≤ K ∘ₘ μ :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hB K.aemeasurable,
      ← lintegral_mul_const _ hc]
    refine lintegral_mono fun y => ?_
    have := h y B
    rwa [Measure.smul_apply, smul_eq_mul] at this

/-- The estimate of MT p. 113: if `Pᵏ(w, C) ≥ η > 0` on `A` and `∫_C ν(dy) Pʳ(y, A) > 0`, then
`2M + k + r ∈ E_C`, via
`P^{M+r+k+M}(x, B) ≥ ∫_C Pᴹ(x, dy) ∫_A Pʳ(y, dw) ∫_C Pᵏ(w, dz) Pᴹ(z, B)`. -/
theorem mem_smallTimes_of_return {P : Kernel X X} {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) {A : Set X} (hA : MeasurableSet A) {k : ℕ} {η : ℝ≥0∞}
    (hη : 0 < η) (hk : ∀ w ∈ A, η ≤ (P ^ k) w C) {r : ℕ}
    (hr : 0 < ((P ^ r : Kernel X X) ∘ₘ ν.restrict C) A) :
    M + (r + (k + M)) ∈ smallTimes P C ν := by
  have ha : ∀ w ∈ A, η • ν ≤ (P ^ (k + M)) w := fun w hw =>
    (smul_measure_le_smul (hk w hw) ν).trans (smul_le_pow_add_of_le P hC.2.2.2 w)
  have hb : ∀ y, ((P ^ r) y A * η) • ν ≤ (P ^ (r + (k + M))) y := fun y => by
    rw [← smul_smul]
    exact smul_le_pow_add_of_le P (C := A) ha y
  have hcm : Measurable fun y => (P ^ r) y A * η := (Kernel.measurable_coe _ hA).mul_const _
  refine ⟨by have := hC.2.1; omega, ((P ^ r : Kernel X X) ∘ₘ ν.restrict C) A * η,
    ENNReal.mul_pos hr.ne' hη.ne', fun x hx => ?_⟩
  have hval : ((P ^ r : Kernel X X) ∘ₘ ν.restrict C) A * η = ∫⁻ y, (P ^ r) y A * η ∂ν.restrict C :=
    by rw [measure_kernel_apply _ _ hA, lintegral_mul_const _ (Kernel.measurable_coe _ hA)]
  rw [hval, show M + (r + (k + M)) = (r + (k + M)) + M by omega, Kernel.pow_add,
    Kernel.comp_apply]
  calc (∫⁻ y, (P ^ r) y A * η ∂ν.restrict C) • ν ≤ (P ^ (r + (k + M))) ∘ₘ ν.restrict C :=
        smul_le_comp_of_le _ _ hcm hb
    _ ≤ (P ^ (r + (k + M))) ∘ₘ ν := comp_le_comp _ Measure.restrict_le_self
    _ ≤ (P ^ (r + (k + M))) ∘ₘ (P ^ M) x := comp_le_comp _ (hC.2.2.2 x hx)
    _ = ((P ^ M) x).bind ⇑(P ^ (r + (k + M))) := rfl

/-! ### The sets `D*_i` -/

/-- `D*_i = {y : Σ_{k ≥ 1, k + i ≡ 0} Pᵏ(y, C) > 0}` (MT p. 113): the states from which `C` is
reached at times `k ≡ −i (mod d)`. -/
def cycleSet (P : Kernel X X) (C : Set X) (d : ℕ) (i : ZMod d) : Set X :=
  {y | ∃ k : ℕ, 0 < k ∧ (k : ZMod d) + i = 0 ∧ 0 < (P ^ k) y C}

/-- `D*_i` as a countable union. -/
theorem cycleSet_eq_iUnion (P : Kernel X X) (C : Set X) (d : ℕ) (i : ZMod d) :
    cycleSet P C d i = ⋃ k : ℕ, {y | 0 < k ∧ (k : ZMod d) + i = 0 ∧ 0 < (P ^ k) y C} := by
  ext y; simp [cycleSet]

/-- `D*_i` is measurable. -/
theorem measurableSet_cycleSet (P : Kernel X X) {C : Set X} (hC : MeasurableSet C) (d : ℕ)
    (i : ZMod d) : MeasurableSet (cycleSet P C d i) := by
  rw [cycleSet_eq_iUnion]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases h : 0 < k ∧ (k : ZMod d) + i = 0
  · simp only [h.1, h.2, true_and]
    exact measurableSet_lt measurable_const (Kernel.measurable_coe _ hC)
  · have : {y : X | 0 < k ∧ (k : ZMod d) + i = 0 ∧ 0 < (P ^ k) y C} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
    rw [this]
    exact MeasurableSet.empty

/-- By irreducibility, `X = ⋃ D*_i` (MT p. 113). -/
theorem iUnion_cycleSet (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {C : Set X} (hC : MeasurableSet C) (hφC : 0 < φ C) (d : ℕ) :
    ⋃ i, cycleSet P C d i = univ := by
  refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC y).1 (hφ C hC hφC y)
  exact ⟨-((n + 1 : ℕ) : ZMod d), n + 1, by omega, by ring, hn⟩

/-- **The key estimate of Theorem 5.4.4** (MT pp. 113–114): `ψ(D*_i ∩ D*_k) = 0` for `i ≠ k`,
where `d = g.c.d. E_C`. -/
theorem measure_cycleSet_inter (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {M : ℕ} {ν : Measure X} {C : Set X} (hC : IsSmallSet P M ν C)
    (hνC : 0 < ν C) {d : ℕ} (hd : d = setGcd (smallTimes P C ν)) {i j : ZMod d} (hij : i ≠ j) :
    ψ (cycleSet P C d i ∩ cycleSet P C d j) = 0 := by
  by_contra hne
  have hpos := pos_iff_ne_zero.2 hne
  set A : ℕ → ℕ → ℕ → Set X := fun k l q => {w | (0 < k ∧ (k : ZMod d) + i = 0) ∧
    (0 < l ∧ (l : ZMod d) + j = 0) ∧ ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ k) w C ∧
      ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ l) w C} with hAdef
  have hsub : cycleSet P C d i ∩ cycleSet P C d j ⊆ ⋃ k, ⋃ l, ⋃ q, A k l q := by
    rintro w ⟨⟨k, hk0, hki, hk⟩, ⟨l, hl0, hlj, hl⟩⟩
    obtain ⟨q₁, hq₁⟩ := ENNReal.exists_inv_nat_lt hk.ne'
    obtain ⟨q₂, hq₂⟩ := ENNReal.exists_inv_nat_lt hl.ne'
    refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨l, mem_iUnion.2 ⟨max q₁ q₂, ⟨hk0, hki⟩, ⟨hl0, hlj⟩,
      le_trans ?_ hq₁.le, le_trans ?_ hq₂.le⟩⟩⟩
    · gcongr
      exact (Nat.cast_le.2 (le_max_left q₁ q₂)).trans le_self_add
    · gcongr
      exact (Nat.cast_le.2 (le_max_right q₁ q₂)).trans le_self_add
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hsub))
  obtain ⟨l, hl⟩ := exists_measure_pos_of_iUnion hk
  obtain ⟨q, hq⟩ := exists_measure_pos_of_iUnion hl
  obtain ⟨w₀, ⟨hk0, hki⟩, ⟨hl0, hlj⟩, -, -⟩ := nonempty_of_measure_ne_zero hq.ne'
  have hAm : MeasurableSet (A k l q) := by
    have : A k l q = {w | ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ k) w C ∧
        ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ l) w C} := by
      ext w; simp [hAdef, hk0, hki, hl0, hlj]
    rw [this]
    exact (measurableSet_le measurable_const (Kernel.measurable_coe _ hC.1)).inter
      (measurableSet_le measurable_const (Kernel.measurable_coe _ hC.1))
  have hη : 0 < ((q : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
  have hρ : ν.restrict C ≠ 0 := by rw [Ne, Measure.restrict_eq_zero]; exact hνC.ne'
  obtain ⟨r, hr⟩ := exists_pow_comp_pos hψ hρ hAm hq
  have h1 := mem_smallTimes_of_return hC hAm (k := k) hη (fun w hw => hw.2.2.1) hr
  have h2 := mem_smallTimes_of_return hC hAm (k := l) hη (fun w hw => hw.2.2.2) hr
  have hS := smallTimes_isAddClosed P hνC
  have hMmem := mem_smallTimes_of_isSmallSet hC
  have e1 := (ZMod.natCast_eq_zero_iff _ d).2 (hd ▸ setGcd_dvd hS hMmem hC.2.1 h1)
  have e2 := (ZMod.natCast_eq_zero_iff _ d).2 (hd ▸ setGcd_dvd hS hMmem hC.2.1 h2)
  push_cast at e1 e2
  exact hij (by linear_combination hki - hlj - e1 + e2)

/-! ### Theorem 5.4.4 -/

/-- **Theorem 5.4.4**, existence (MT p. 113): with `d = g.c.d. E_C`, the sets
`D_i = D ∩ D*_i`, for an absorbing full set `D` avoiding `⋃_{i ≠ k} D*_i ∩ D*_k`, form a
`d`-cycle. -/
theorem exists_isCycle_gcd (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    ∃ D : ZMod (setGcd (smallTimes P C ν)) → Set X,
      IsCycle P ψ (setGcd (smallTimes P C ν)) D ∧
        ∀ i, D i ⊆ cycleSet P C (setGcd (smallTimes P C ν)) i := by
  set d := setGcd (smallTimes P C ν) with hd
  have hd0 : 0 < d := setGcd_pos (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  have : NeZero d := ⟨hd0.ne'⟩
  have hDs := measurableSet_cycleSet P hC.1 d
  set N : Set X := ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), cycleSet P C d i ∩ cycleSet P C d j with hNdef
  have hNm : MeasurableSet N := MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => (hDs i).inter (hDs j)
  have hN : ψ N = 0 := measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => measure_cycleSet_inter P hψ.2.1 hC hνC hd hij
  have hfull : IsFull ψ Nᶜ := by rw [IsFull, compl_compl]; exact hN
  obtain ⟨D, hDsub, -, hDm, hDabs, hDfull⟩ := proposition_4_2_3_ii hψ hNm.compl hfull
  have hcov := iUnion_cycleSet P hψ.2.1 hC.1 hψC d
  have hnotN : ∀ x ∈ D, ∀ i j, x ∈ cycleSet P C d i → x ∈ cycleSet P C d j → i = j :=
    fun x hx i j hi hj => by
      by_contra hij
      exact hDsub hx (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hij, hi, hj⟩⟩⟩)
  refine ⟨fun i => D ∩ cycleSet P C d i, ⟨fun i => hDm.inter (hDs i), fun i j hij =>
    Set.disjoint_left.2 fun x hi hj => hij (hnotN x hi.1 i j hi.2 hj.2), fun i x hx => ?_, ?_⟩,
    fun i => inter_subset_right⟩
  · -- the chain moves from `D_i` to `D_{i+1}`
    have hzero : ∀ j, j ≠ i + 1 → P x (D ∩ cycleSet P C d j) = 0 := fun j hj => by
      by_contra hne
      have hsub : D ∩ cycleSet P C d j ⊆
          ⋃ k : ℕ, {y | 0 < k ∧ (k : ZMod d) + j = 0 ∧ 0 < (P ^ k) y C} :=
        fun y hy => by rw [← cycleSet_eq_iUnion]; exact hy.2
      obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion
        ((pos_iff_ne_zero.2 hne).trans_le (measure_mono hsub))
      obtain ⟨y, hk0, hkj, -⟩ := nonempty_of_measure_ne_zero hk.ne'
      have hreach : 0 < (P ^ (1 + k)) x C := by
        rw [pow_add_pos_iff P 1 k x hC.1, pow_one]
        exact hk.trans_le (measure_mono fun y hy => hy.2.2)
      have hx' : x ∈ cycleSet P C d (j - 1) :=
        ⟨1 + k, by omega, by push_cast; linear_combination hkj, hreach⟩
      exact hj (by linear_combination (hnotN x hx.1 i (j - 1) hx.2 hx').symm)
    have hD1 : P x D = 1 := hDabs x hx.1
    have hcover : D ⊆ (D ∩ cycleSet P C d (i + 1)) ∪
        ⋃ j, ⋃ (_ : j ≠ i + 1), D ∩ cycleSet P C d j := fun y hy => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov ▸ mem_univ y : y ∈ ⋃ i, cycleSet P C d i)
      by_cases hji : j = i + 1
      · exact Or.inl ⟨hy, hji ▸ hj⟩
      · exact Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hji, hy, hj⟩⟩)
    have hnull : P x (⋃ j, ⋃ (_ : j ≠ i + 1), D ∩ cycleSet P C d j) = 0 :=
      measure_iUnion_null fun j => measure_iUnion_null fun hj => hzero j hj
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = P x D := hD1.symm
      _ ≤ P x (D ∩ cycleSet P C d (i + 1)) + P x (⋃ j, ⋃ (_ : j ≠ i + 1),
          D ∩ cycleSet P C d j) := (measure_mono hcover).trans (measure_union_le _ _)
      _ = P x (D ∩ cycleSet P C d (i + 1)) := by rw [hnull, add_zero]
  · -- the complement of the union is `ψ`-null
    refine measure_mono_null (compl_subset_compl.2 fun y hy => ?_) hDfull
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov ▸ mem_univ y : y ∈ ⋃ i, cycleSet P C d i)
    exact mem_iUnion.2 ⟨j, hy, hj⟩

/-- A positive mass on a countable union sits on one of the sets (any countable index). -/
theorem exists_measure_pos_of_iUnion' {ι : Type*} [Countable ι] {μ : Measure X} {s : ι → Set X}
    (h : 0 < μ (⋃ i, s i)) : ∃ i, 0 < μ (s i) := by
  by_contra hc
  push Not at hc
  rw [measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (hc i)] at h
  exact lt_irrefl _ h

/-- For any `d'`-cycle there is a class `D'_k` charged by `ν`, and a state of `C ∩ D'_j` is in
`D'_k` after `n ∈ E_C` steps: `j + n = k` (MT p. 114). -/
theorem exists_class_of_isCycle (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {d' : ℕ} (hd' : 0 < d')
    {D' : ZMod d' → Set X} (h : IsCycle P ψ d' D') :
    ∃ k : ZMod d', ∀ n ∈ smallTimes P C ν, ∀ j, ∀ x ∈ C ∩ D' j, j + n = k := by
  have : NeZero d' := ⟨hd'.ne'⟩
  have hνψ : ν ≪ ψ := hψ.2.2 ν (hC.isPhiIrreducible hψ.2.1 hψC)
  have hνN : ν (⋃ j, D' j)ᶜ = 0 := hνψ h.null_compl
  have hcov : C ⊆ (⋃ j, D' j ∩ C) ∪ (⋃ j, D' j)ᶜ := fun x hx => by
    by_cases hU : x ∈ ⋃ j, D' j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hU
      exact Or.inl (mem_iUnion.2 ⟨j, hj, hx⟩)
    · exact Or.inr hU
  have hU : 0 < ν (⋃ j, D' j ∩ C) := by
    have := hνC.trans_le ((measure_mono hcov).trans (measure_union_le _ _))
    rwa [hνN, add_zero] at this
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion' hU
  refine ⟨k, fun n hn j x hx => ?_⟩
  obtain ⟨-, δ, hδ, hδn⟩ := hn
  have hpos : 0 < (P ^ n) x (D' k) := by
    have h1 := hδn x hx.1 (D' k ∩ C)
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact (ENNReal.mul_pos hδ.ne' hk.ne').trans_le (h1.trans (measure_mono inter_subset_left))
  by_contra hne
  exact hpos.ne' (h.pow_apply_eq_zero n hx.2 (Ne.symm hne))

/-- **Theorem 5.4.4**, maximality (MT p. 114): for every `d'`-cycle, `d'` divides
`d = g.c.d. E_C`. -/
theorem dvd_gcd_of_isCycle (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {d' : ℕ} (hd' : 0 < d')
    {D' : ZMod d' → Set X} (h : IsCycle P ψ d' D') : d' ∣ setGcd (smallTimes P C ν) := by
  have : NeZero d' := ⟨hd'.ne'⟩
  obtain ⟨k, hk⟩ := exists_class_of_isCycle P hψ hC hψC hνC hd' h
  -- a state of `C` in one of the classes
  have hψU : 0 < ψ (C ∩ ⋃ j, D' j) := by
    have hle : ψ C ≤ ψ (C ∩ ⋃ j, D' j) + ψ (⋃ j, D' j)ᶜ := by
      rw [← measure_inter_add_sdiff C (MeasurableSet.iUnion h.measurableSet), sdiff_eq]
      gcongr
      exact inter_subset_right
    rw [h.null_compl, add_zero] at hle
    exact hψC.trans_le hle
  obtain ⟨x, hxC, hxU⟩ := nonempty_of_measure_ne_zero hψU.ne'
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxU
  have hS := smallTimes_isAddClosed P hνC
  have hMmem := mem_smallTimes_of_isSmallSet hC
  refine dvd_setGcd hS hMmem hC.2.1 fun n hn => ?_
  have e1 := hk n hn j x ⟨hxC, hj⟩
  have e2 := hk (n + n) (hS n hn n hn) j x ⟨hxC, hj⟩
  refine (ZMod.natCast_eq_zero_iff n d').1 ?_
  push_cast at e2
  linear_combination e2 - e1

/-- **Theorem 5.4.4**, comparison of cycles (MT p. 114). Let `D` be a `d`-cycle with
`D_i ⊆ D*_i`, `d = g.c.d. E_C`, as constructed in `exists_isCycle_gcd`, and `D'` a `d'`-cycle,
so that `d' ∣ d`. Then for some `k`, every `D_i` lies in `D'_{k + i}` up to a `ψ`-null set: each
`D'_j` is, up to null sets, a union of classes of `D`. -/
theorem isCycle_subset_ae (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C)
    {D : ZMod (setGcd (smallTimes P C ν)) → Set X}
    (hDsub : ∀ i, D i ⊆ cycleSet P C (setGcd (smallTimes P C ν)) i)
    {d' : ℕ} (hd' : 0 < d') {D' : ZMod d' → Set X} (h : IsCycle P ψ d' D') :
    ∃ k : ZMod d', ∀ i, ψ (D i \ D' (k + ZMod.castHom
      (dvd_gcd_of_isCycle P hψ hC hψC hνC hd' h) (ZMod d') i)) = 0 := by
  have : NeZero d' := ⟨hd'.ne'⟩
  have hdvd := dvd_gcd_of_isCycle P hψ hC hψC hνC hd' h
  obtain ⟨k, hk⟩ := exists_class_of_isCycle P hψ hC hψC hνC hd' h
  have hMmem := mem_smallTimes_of_isSmallSet hC
  -- states of `C` lie in `D'_k`
  have hCk : ∀ j, ∀ x ∈ C ∩ D' j, j = k := fun j x hx => by
    have e := hk M hMmem j x hx
    have hM0 : (M : ZMod d') = 0 := (ZMod.natCast_eq_zero_iff M d').2 (hdvd.trans
      (setGcd_dvd (smallTimes_isAddClosed P hνC) hMmem hC.2.1 hMmem))
    rw [hM0, add_zero] at e
    exact e
  refine ⟨k, fun i => measure_mono_null (fun y hy => ?_) h.null_compl⟩
  intro hyU
  obtain ⟨j, hj⟩ := mem_iUnion.1 hyU
  obtain ⟨n, hn0, hni, hn⟩ := hDsub i hy.1
  -- `Pⁿ(y, C ∩ D'_{j+n}) > 0`, so `j + n = k`
  have := isMarkovKernel_pow P n
  have h1 := h.pow_apply n hj
  rw [← prob_compl_eq_zero_iff (h.measurableSet _)] at h1
  have hpos : 0 < (P ^ n) y (C ∩ D' (j + n)) := by
    have hle : (P ^ n) y C ≤ (P ^ n) y (C ∩ D' (j + n)) + (P ^ n) y (D' (j + n))ᶜ := by
      rw [← measure_inter_add_sdiff C (h.measurableSet (j + n)), sdiff_eq]
      gcongr
      exact inter_subset_right
    rw [h1, add_zero] at hle
    exact hn.trans_le hle
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hjn := hCk (j + n) x hx
  have hcast := congrArg (ZMod.castHom hdvd (ZMod d')) hni
  rw [map_add, map_natCast, map_zero] at hcast
  refine hy.2 ?_
  have : j = k + ZMod.castHom hdvd (ZMod d') i := by linear_combination hjn - hcast
  rw [← this]
  exact hj

/-- **Theorem 5.4.4**, uniqueness (MT p. 114): any two `d`-cycles, `d = g.c.d. E_C`, agree up to
`ψ`-null sets after a relabelling `i ↦ k + i`. -/
theorem theorem_5_4_4_unique (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C)
    {D D' : ZMod (setGcd (smallTimes P C ν)) → Set X}
    (hD : IsCycle P ψ (setGcd (smallTimes P C ν)) D)
    (hD' : IsCycle P ψ (setGcd (smallTimes P C ν)) D') :
    ∃ k, ∀ i, ψ (symmDiff (D i) (D' (k + i))) = 0 := by
  have hd0 : 0 < setGcd (smallTimes P C ν) := setGcd_pos (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  have : NeZero (setGcd (smallTimes P C ν)) := ⟨hd0.ne'⟩
  obtain ⟨D₀, hD₀, hD₀sub⟩ := exists_isCycle_gcd P hψ hC hψC hνC
  -- comparison of a `d`-cycle with the constructed one
  have hcomp : ∀ E : ZMod (setGcd (smallTimes P C ν)) → Set X,
      IsCycle P ψ (setGcd (smallTimes P C ν)) E →
      ∃ k, ∀ i, ψ (symmDiff (D₀ i) (E (k + i))) = 0 := fun E hE => by
    obtain ⟨k, hk⟩ := isCycle_subset_ae P hψ hC hψC hνC hD₀sub hd0 hE
    simp only [ZMod.castHom_apply, ZMod.cast_id] at hk
    refine ⟨k, fun i => ?_⟩
    have h2 : ψ (E (k + i) \ D₀ i) = 0 := by
      have hsub : E (k + i) \ D₀ i ⊆ (⋃ i', D₀ i')ᶜ ∪
          ⋃ i', ⋃ (_ : i' ≠ i), D₀ i' \ E (k + i') := fun y hy => by
        by_cases hU : y ∈ ⋃ i', D₀ i'
        · obtain ⟨i', hi'⟩ := mem_iUnion.1 hU
          have hne : i' ≠ i := fun h => hy.2 (h ▸ hi')
          refine Or.inr (mem_iUnion.2 ⟨i', mem_iUnion.2 ⟨hne, hi', fun hE' => ?_⟩⟩)
          exact Set.disjoint_left.1 (hE.disjoint (k + i') (k + i)
            (fun h => hne (add_left_cancel h))) hE' hy.1
        · exact Or.inl hU
      refine measure_mono_null hsub (measure_union_null hD₀.null_compl ?_)
      exact measure_iUnion_null fun i' => measure_iUnion_null fun _ => hk i'
    exact measure_union_null (hk i) h2
  obtain ⟨k₁, hk₁⟩ := hcomp D hD
  obtain ⟨k₂, hk₂⟩ := hcomp D' hD'
  refine ⟨k₂ - k₁, fun i => ?_⟩
  have h1 := hk₁ (i - k₁)
  have h2 := hk₂ (i - k₁)
  rw [add_sub_cancel] at h1
  rw [show k₂ + (i - k₁) = k₂ - k₁ + i by ring] at h2
  refine measure_mono_null ((symmDiff_triangle (D i) (D₀ (i - k₁)) (D' (k₂ - k₁ + i))).trans
    (sup_le_sup (le_of_eq (symmDiff_comm _ _)) le_rfl)) ?_
  exact measure_union_null h1 h2

/-- **Theorem 5.4.4** (MT p. 113). Let `ψ` be a maximal irreducibility measure, `C ∈ B⁺(X)` a
`ν_M`-small set with `ν_M(C) > 0`, and `d = g.c.d. E_C`. (i)–(ii) There is a `d`-cycle.
Maximality: every `d'`-cycle has `d' ∣ d`; and any two `d`-cycles agree up to `ψ`-null sets after
relabelling. -/
theorem theorem_5_4_4 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    (∃ D, IsCycle P ψ (setGcd (smallTimes P C ν)) D) ∧
      (∀ d' (D' : ZMod d' → Set X), 0 < d' → IsCycle P ψ d' D' →
        d' ∣ setGcd (smallTimes P C ν)) ∧
      ∀ D D' : ZMod (setGcd (smallTimes P C ν)) → Set X,
        IsCycle P ψ (setGcd (smallTimes P C ν)) D →
        IsCycle P ψ (setGcd (smallTimes P C ν)) D' →
        ∃ k, ∀ i, ψ (symmDiff (D i) (D' (k + i))) = 0 := by
  obtain ⟨D, hD, -⟩ := exists_isCycle_gcd P hψ hC hψC hνC
  exact ⟨⟨D, hD⟩, fun d' D' hd' h => dvd_gcd_of_isCycle P hψ hC hψC hνC hd' h,
    fun D D' hD hD' => theorem_5_4_4_unique P hψ hC hψC hνC hD hD'⟩

/-- MT p. 113, from Lemma D.7.4: `C` is `δₙν`-small at every large multiple `nd` of
`d = g.c.d. E_C`. -/
theorem exists_isSmallSet_mul_gcd {P : Kernel X X} {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hνC : 0 < ν C) :
    ∃ N, ∀ n ≥ N, ∃ δ : ℝ≥0∞, 0 < δ ∧
      IsSmallSet P (n * setGcd (smallTimes P C ν)) (δ • ν) C := by
  obtain ⟨N, hN⟩ := lemma_D_7_4 (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  exact ⟨N, fun n hn => isSmallSet_of_mem_smallTimes hC.1 hC.2.2.1 (hN n hn)⟩

/-- MT p. 114: a small set `C ∈ B⁺(X)` with `ν(C) > 0` lies, up to a `ψ`-null set, inside one
class of any `d`-cycle. -/
theorem exists_class_subset_ae (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {d : ℕ} (hd : 0 < d)
    {D : ZMod d → Set X} (h : IsCycle P ψ d D) : ∃ k, ψ (C \ D k) = 0 := by
  obtain ⟨k, hk⟩ := exists_class_of_isCycle P hψ hC hψC hνC hd h
  refine ⟨k - M, measure_mono_null (fun x hx => ?_) h.null_compl⟩
  intro hU
  obtain ⟨j, hj⟩ := mem_iUnion.1 hU
  have e := hk M (mem_smallTimes_of_isSmallSet hC) j x ⟨hx.1, hj⟩
  exact hx.2 (by rwa [show k - M = j by linear_combination -e])

/-! ### The period -/

/-- `d` is the **period** of the chain (MT p. 114): a `d`-cycle exists, and `d' ≤ d` for every
`d'`-cycle. -/
def IsPeriod (P : Kernel X X) (ψ : Measure X) (d : ℕ) : Prop :=
  0 < d ∧ (∃ D, IsCycle P ψ d D) ∧ ∀ d' (D' : ZMod d' → Set X), 0 < d' → IsCycle P ψ d' D' → d' ≤ d

/-- The chain is **aperiodic** (MT p. 114) if its period is `1`. -/
def IsAperiodic (P : Kernel X X) (ψ : Measure X) : Prop := IsPeriod P ψ 1

/-- The chain is **strongly aperiodic** (MT p. 114) if there is a `ν₁`-small set `A` with
`ν₁(A) > 0`. -/
def IsStronglyAperiodic (P : Kernel X X) : Prop := ∃ ν A, IsSmallSet P 1 ν A ∧ 0 < ν A

/-- The period is unique. -/
theorem IsPeriod.unique {P : Kernel X X} {ψ : Measure X} {d d' : ℕ} (h : IsPeriod P ψ d)
    (h' : IsPeriod P ψ d') : d = d' := by
  obtain ⟨hd0, ⟨D, hD⟩, hmax⟩ := h
  obtain ⟨hd0', ⟨D', hD'⟩, hmax'⟩ := h'
  exact le_antisymm (hmax' d D hd0 hD) (hmax d' D' hd0' hD')

/-- By Theorem 5.4.4, `g.c.d. E_C` is the period, for every `ν`-small `C ∈ B⁺(X)` with
`ν(C) > 0` (MT p. 114: the cycle does not depend on the small set chosen). -/
theorem isPeriod_gcd (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    IsPeriod P ψ (setGcd (smallTimes P C ν)) := by
  obtain ⟨h1, h2, -⟩ := theorem_5_4_4 P hψ hC hψC hνC
  have hd0 : 0 < setGcd (smallTimes P C ν) := setGcd_pos (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  exact ⟨hd0, h1, fun d' D' hd' h => Nat.le_of_dvd hd0 (h2 d' D' hd' h)⟩

/-- The period equals `g.c.d. E_C` for every such `C`. -/
theorem IsPeriod.eq_gcd {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    (h : IsPeriod P ψ d) (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    d = setGcd (smallTimes P C ν) :=
  h.unique (isPeriod_gcd P hψ hC hψC hνC)

/-- On a countably generated space, every `ψ`-irreducible chain has a period. -/
theorem exists_isPeriod [MeasurableSpace.CountablyGenerated X] (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) : ∃ d, IsPeriod P ψ d := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  exact ⟨_, isPeriod_gcd P hψ hC hψC hνC⟩

/-- `E_C` does not change when `ν` is multiplied by a constant `0 < c < ∞`. -/
theorem smallTimes_smul (P : Kernel X X) (C : Set X) (ν : Measure X) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ∞) : smallTimes P C (c • ν) = smallTimes P C ν := by
  ext n
  constructor
  · rintro ⟨hn, δ, hδ, h⟩
    refine ⟨hn, δ * c, ENNReal.mul_pos hδ.ne' hc0, fun x hx => ?_⟩
    rw [← smul_smul]; exact h x hx
  · rintro ⟨hn, δ, hδ, h⟩
    refine ⟨hn, δ * c⁻¹, ENNReal.mul_pos hδ.ne' (ENNReal.inv_ne_zero.2 hct), fun x hx => ?_⟩
    rw [smul_smul, mul_assoc, ENNReal.inv_mul_cancel hc0 hct, mul_one]
    exact h x hx

/-- Irreducibility of a skeleton `Pᵐ`, `m ≥ 1`, gives irreducibility of `P`. -/
theorem isPhiIrreducible_of_pow_skeleton (P : Kernel X X) [IsMarkovKernel P] {m : ℕ}
    (hm : 1 ≤ m) {φ : Measure X}
    (h : haveI := isMarkovKernel_pow P m; IsPhiIrreducible (P ^ m) φ) : IsPhiIrreducible P φ := by
  have := isMarkovKernel_pow P m
  intro A hA hpos x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff (P ^ m) hA x).1 (h A hA hpos x)
  refine (hitProb_pos_iff P hA x).2 ⟨m * (n + 1) - 1, ?_⟩
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity)), pow_mul]
  exact hn

/-- **Proposition 5.4.5 (i)** (MT p. 114): a strongly aperiodic chain satisfies the
minorization condition (5.2), with the book's normalisation `ν(Cᶜ) = 0`. -/
theorem proposition_5_4_5_i (P : Kernel X X) [IsMarkovKernel P] (h : IsStronglyAperiodic P) :
    ∃ M : Minorization P, M.IsConcentrated := by
  obtain ⟨ν, A, hA, hνA⟩ := h
  have hle : ∀ x ∈ A, ν ≤ P x := fun x hx => by
    have := hA.2.2.2 x hx
    rwa [pow_one] at this
  have hfin : ν A ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hνA.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx A).trans prob_le_one)
  exact ⟨Minorization.ofLe hA.1 hle hνA hfin, Minorization.ofLe_isConcentrated _ _ _ _⟩

/-- **Proposition 5.4.5 (ii)** (MT p. 114): on a countably generated space the resolvent
`K_{a_ε}`, `0 < ε < 1`, of a `ψ`-irreducible chain is strongly aperiodic. -/
theorem proposition_5_4_5_ii [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {ε : ℝ≥0∞}
    (hε0 : 0 < ε) (hε1 : ε < 1) : IsStronglyAperiodic (resolvent P ε) := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, -, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hc : 0 < (1 - ε) * ε ^ m :=
    ENNReal.mul_pos (tsub_pos_of_lt hε1).ne' (pow_ne_zero _ hε0.ne')
  refine ⟨((1 - ε) * ε ^ m) • ν, C, ⟨hC.1, one_pos, smul_measure_ne_zero hC.2.2.1 hc.ne',
    fun x hx => ?_⟩, ?_⟩
  · rw [pow_one]
    exact (smul_measure_le_smul le_rfl _).trans (le_trans (Measure.le_intro fun B _ _ => by
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      gcongr
      exact hC.2.2.2 x hx) (smul_pow_le_resolvent P ε m x))
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc.ne' hνC.ne'

/-- For an aperiodic chain, `E_C` contains every large time. -/
theorem exists_forall_mem_smallTimes_of_aperiodic (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {M : ℕ}
    {ν : Measure X} {C : Set X} (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    ∃ N, ∀ n ≥ N, n ∈ smallTimes P C ν := by
  have h1 : setGcd (smallTimes P C ν) = 1 := (hap.eq_gcd hψ hC hψC hνC).symm
  obtain ⟨N, hN⟩ := lemma_D_7_4 (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rwa [h1, mul_one] at this

/-- **Proposition 5.4.5 (iii)** (MT p. 114). On a countably generated space, if a `ψ`-irreducible
chain is aperiodic, then every skeleton `Pᵐ`, `m ≥ 1`, is `ψ`-irreducible (with `ψ` maximal) and
aperiodic, and some skeleton is strongly aperiodic. -/
theorem proposition_5_4_5_iii [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    (hap : IsAperiodic P ψ) :
    (∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
      IsMaximalIrreducibility (P ^ m) ψ ∧ IsAperiodic (P ^ m) ψ) ∧
      ∃ m, 1 ≤ m ∧ IsStronglyAperiodic (P ^ m) := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  refine ⟨fun m hm => ?_, ?_⟩
  · have := isMarkovKernel_pow P m
    -- irreducibility of the skeleton
    have hirr : IsPhiIrreducible (P ^ m) ψ := by
      intro A hA hpos x
      obtain ⟨j, hj⟩ := (hitProb_pos_iff P hC.1 x).1 (hψ.2.1 C hC.1 hψC x)
      obtain ⟨r, hr⟩ := exists_pow_comp_pos hψ.2.1 hC.2.2.1 hA hpos
      set q := N + (j + 1) + (r + 1) with hq
      have hn : m * q - (j + 1) - (r + 1) ≥ N := by
        have : q ≤ m * q := Nat.le_mul_of_pos_left q hm
        omega
      obtain ⟨-, δ, hδ, hδn⟩ := hN _ hn
      set n := m * q - (j + 1) - (r + 1)
      have hν' : ∀ y ∈ C, δ • ((P ^ (r + 1) : Kernel X X) ∘ₘ ν) ≤ (P ^ (n + (r + 1))) y :=
        fun y hy => by
          rw [show n + (r + 1) = (r + 1) + n by omega, Kernel.pow_add P (r + 1) n,
            Kernel.comp_apply,
            ← Measure.comp_smul]
          exact comp_le_comp _ (hδn y hy)
      have h1 := pow_add_ge_of_le P (m := j + 1) hν' x hA
      have heq : j + 1 + (n + (r + 1)) = m * q := by
        have : q ≤ m * q := Nat.le_mul_of_pos_left q hm
        omega
      rw [heq, Measure.smul_apply, smul_eq_mul] at h1
      have hpos' : 0 < ((P ^ m) ^ q) x A := by
        rw [← pow_mul]
        exact (ENNReal.mul_pos hj.ne' (ENNReal.mul_pos hδ.ne' hr.ne').ne').trans_le h1
      refine (hitProb_pos_iff (P ^ m) hA x).2 ⟨q - 1, ?_⟩
      rwa [Nat.sub_add_cancel (by omega)]
    have hmax : IsMaximalIrreducibility (P ^ m) ψ :=
      ⟨hψ.1, hirr, fun φ hφ => hψ.2.2 φ (isPhiIrreducible_of_pow_skeleton P hm hφ)⟩
    refine ⟨hmax, ?_⟩
    -- aperiodicity of the skeleton
    obtain ⟨-, δ, hδ, hδn⟩ := hN (m * (N + 1)) (by nlinarith)
    have hCm : IsSmallSet (P ^ m) (N + 1) (δ • ν) C :=
      ⟨hC.1, by omega, smul_measure_ne_zero hC.2.2.1 hδ.ne', fun x hx => by
        rw [← pow_mul]; exact hδn x hx⟩
    have hδC : 0 < (δ • ν) C := by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ.ne' hνC.ne'
    have hδt : δ ≠ ∞ := by
      have := isMarkovKernel_pow P (m * (N + 1))
      intro htop
      obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
      have := (hδn x hx C).trans prob_le_one
      rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.top_mul hνC.ne'] at this
      exact absurd this (by simp)
    have hper := isPeriod_gcd (P ^ m) hmax hCm hψC hδC
    rw [smallTimes_smul _ _ _ hδ.ne' hδt] at hper
    -- every `t ≥ N + 1` lies in `E_C` for the skeleton
    have hmem : ∀ t, N ≤ t → t + 1 ∈ smallTimes (P ^ m) C ν := fun t ht => by
      obtain ⟨-, δ', hδ', h'⟩ := hN (m * (t + 1)) (by nlinarith)
      exact ⟨by omega, δ', hδ', fun x hx => by rw [← pow_mul]; exact h' x hx⟩
    have hS := smallTimes_isAddClosed (P ^ m) hνC
    have h1 := setGcd_dvd hS (hmem N le_rfl) (by omega) (hmem N le_rfl)
    have h2 := setGcd_dvd hS (hmem N le_rfl) (by omega) (hmem (N + 1) (by omega))
    have hg : setGcd (smallTimes (P ^ m) C ν) = 1 :=
      Nat.dvd_one.1 (by simpa using (Nat.dvd_sub h2 h1))
    rwa [hg] at hper
  · obtain ⟨-, δ, hδ, hδn⟩ := hN (N + 1) (by omega)
    refine ⟨N + 1, by omega, δ • ν, C, ⟨hC.1, one_pos, smul_measure_ne_zero hC.2.2.1 hδ.ne',
      fun x hx => by rw [pow_one]; exact hδn x hx⟩, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ.ne' hνC.ne'

/-- **Proposition 5.4.6** (MT p. 115): for a `d`-cycle, each `D_i` is an absorbing
`ψ`-irreducible set for the chain `Φ_d` with kernel `Pᵈ` (with irreducibility measure `ψ`
restricted to `D_i`). -/
theorem proposition_5_4_6 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {d : ℕ} {D : ZMod d → Set X}
    (h : IsCycle P ψ d D) (i : ZMod d) :
    haveI := isMarkovKernel_pow P d
    IsAbsorbingIrreducibleSet (P ^ d) (ψ.restrict (D i)) (D i) := by
  have := isMarkovKernel_pow P d
  refine ⟨fun x hx => ?_, fun B hB hpos x hx => ?_⟩
  · have := h.pow_apply d hx
    rwa [ZMod.natCast_self, add_zero] at this
  · rw [Measure.restrict_apply hB] at hpos
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P (hB.inter (h.measurableSet i)) x).1
      (hψ _ (hB.inter (h.measurableSet i)) hpos x)
    have hcast : ((n + 1 : ℕ) : ZMod d) = 0 := by
      by_contra hne
      have h0 := h.pow_apply_eq_zero (n + 1) hx (j := i) (by
        intro hc
        exact hne (by linear_combination -hc))
      exact hn.ne' (measure_mono_null inter_subset_right h0)
    obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ d).1 hcast
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq; omega
    refine (hitProb_pos_iff (P ^ d) hB x).2 ⟨q - 1, ?_⟩
    rw [Nat.sub_add_cancel hq0, ← pow_mul, ← hq]
    exact hn.trans_le (measure_mono inter_subset_left)

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The chain `Φ_d` on a cycle class is aperiodic (MT Proposition 5.4.6)

Meyn and Tweedie, Proposition 5.4.6, p. 115: if `Φ` has period `d` and `d`-cycle `{Dᵢ}`, then
`Φ_d` (kernel `Pᵈ`) on each `Dᵢ` is aperiodic. The first half of the proposition (each `Dᵢ` is an
absorbing `ψ`-irreducible set for `Pᵈ`) is `proposition_5_4_6` in `Cycles`.

A cycle of `Pᵈ` on `Dᵢ` is a family `E_b ⊆ Dᵢ`, `b ∈ ZMod d'`, of disjoint measurable sets with
`Pᵈ(x, E_{b+1}) = 1` on `E_b` and `ψ(Dᵢ \ ⋃ E_b) = 0`. The book proves aperiodicity by "the
definition of `d` as the largest value for which a cycle exists"; the proof here makes that
explicit by building a `dd'`-cycle of `Φ` from such a family:
`F_{l + d b} = E_b` for `l = 0` and `F_{l + d b} = {x ∈ D_{i+l} : P^{d−l}(x, E_{b+1}) = 1}` for
`0 < l < d`.

* `measure_setOf_eq_one`: if `∫ f dμ = 1` for a probability `μ` and `f ≤ 1`, then `f = 1`
  `μ`-a.s.
* `IsCycle.measure_pos`: for a maximal irreducibility measure every class of a cycle is in
  `B⁺(X)`.
* `zmod_phase_succ`, `zmod_phase_inj`, `zmod_phase_exists`: the decomposition
  `j = l + d b` of `j ∈ ZMod (d d')`.
* `isCycle_liftClass`: the lifted family is a `dd'`-cycle of `Φ`.
* **Proposition 5.4.6**, aperiodicity (`proposition_5_4_6_aperiodic`): every such family has
  `d' = 1`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- If `∫ f dμ = 1` for a probability measure `μ` and `f ≤ 1`, then `μ{f = 1} = 1`. -/
theorem measure_setOf_eq_one {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) (h : ∫⁻ x, f x ∂μ = 1) : μ {x | f x = 1} = 1 := by
  have h0 : ∫⁻ x, (1 - f x) ∂μ = 0 := by
    have := lintegral_sub (μ := μ) (f := fun _ => (1 : ℝ≥0∞)) (g := f) hf
      (by rw [h]; exact ENNReal.one_ne_top) (Filter.Eventually.of_forall hf1)
    rw [this, h, lintegral_const, measure_univ, one_mul, tsub_self]
  rw [lintegral_eq_zero_iff (f := fun x => 1 - f x) (measurable_const.sub hf)] at h0
  have hae : ∀ᵐ x ∂μ, f x = 1 := h0.mono fun x hx => le_antisymm (hf1 x)
    (by simpa [tsub_eq_zero_iff_le] using hx)
  rw [← prob_compl_eq_zero_iff (measurableSet_eq_fun hf measurable_const)]
  exact measure_eq_zero_iff_ae_notMem.2 (hae.mono fun x hx h' => h' hx)

/-- For a maximal irreducibility measure, every class of a cycle has positive measure. -/
theorem IsCycle.measure_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {d : ℕ} (hd : 0 < d) {D : ZMod d → Set X}
    (h : IsCycle P ψ d D) (i : ZMod d) : 0 < ψ (D i) := by
  have : NeZero d := ⟨hd.ne'⟩
  by_contra h0
  push Not at h0
  -- the class before a null class is null
  have hback : ∀ j, ψ (D (j + 1)) = 0 → ψ (D j) = 0 := fun j hj => by
    refine measure_mono_null (fun x hx => ?_) (hψ.hitSet_null (h.measurableSet _) hj)
    have h1 := h.step j x hx
    have h2 := pow_le_hitProb P (h.measurableSet (j + 1)) 0 x
    rw [zero_add, pow_one, h1] at h2
    exact one_pos.trans_le h2
  have hall : ∀ n : ℕ, ψ (D (i - n)) = 0 := fun n => by
    induction n with
    | zero => simpa using nonpos_iff_eq_zero.1 h0
    | succ n ih =>
      refine hback _ ?_
      rwa [show i - ((n + 1 : ℕ) : ZMod d) + 1 = i - n by push_cast; ring]
  have hnull : ∀ j, ψ (D j) = 0 := fun j => by
    have := hall (i - j).val
    rwa [ZMod.natCast_zmod_val, sub_sub_cancel] at this
  apply hψ.1
  rw [← Measure.measure_univ_eq_zero]
  refine measure_mono_null (fun x _ => ?_) (measure_union_null (measure_iUnion_null hnull)
    h.null_compl)
  by_cases hx : x ∈ ⋃ j, D j
  · exact Or.inl hx
  · exact Or.inr hx

/-! ### The phase decomposition of `ZMod (d d')` -/

omit [MeasurableSpace X] in
/-- One step in `ZMod (d d')` in terms of the decomposition `j = l + d b`, `l = j mod d`: if
`l + 1 < d` the phase becomes `l + 1` with the same `b`; otherwise it becomes `0` and `b`
increases by one (mod `d'`). -/
theorem zmod_phase_succ {d d' : ℕ} (hd : 0 < d) (hd' : 2 ≤ d') [NeZero (d * d')]
    (j : ZMod (d * d')) :
    (j.val % d + 1 < d → (j + 1).val % d = j.val % d + 1 ∧
      (((j + 1).val / d : ℕ) : ZMod d') = ((j.val / d : ℕ) : ZMod d')) ∧
    (¬ (j.val % d + 1 < d) → (j + 1).val % d = 0 ∧
      (((j + 1).val / d : ℕ) : ZMod d') = ((j.val / d : ℕ) : ZMod d') + 1) := by
  have hN1 : d * d' ≠ 1 := by nlinarith
  have hval : (j + 1).val = (j.val + 1) % (d * d') := by
    rw [ZMod.val_add, ZMod.val_one'' hN1]
  set v := j.val with hv
  have hvlt : v < d * d' := ZMod.val_lt j
  set l := v % d
  set q := v / d
  have hdecomp : d * q + l = v := Nat.div_add_mod v d
  have hl : l < d := Nat.mod_lt v hd
  have hq : q < d' := (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; exact hvlt)
  have hmul : d * (q + 1) ≤ d * d' := Nat.mul_le_mul_left d hq
  have hmul' : d * (q + 1) = d * q + d := by ring
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlt : v + 1 < d * d' := by omega
    rw [hval, Nat.mod_eq_of_lt hlt]
    have hrw : v + 1 = (l + 1) + d * q := by omega
    rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt h, zero_add]
    exact ⟨rfl, rfl⟩
  · have hl1 : l + 1 = d := by omega
    have hrw : v + 1 = 0 + d * (q + 1) := by omega
    rcases Nat.lt_or_ge (q + 1) d' with hq1 | hq1
    · have hlt : v + 1 < d * d' := by
        have := Nat.mul_lt_mul_of_pos_left hq1 hd
        omega
      rw [hval, Nat.mod_eq_of_lt hlt, hrw, Nat.add_mul_mod_self_left, Nat.zero_mod,
        Nat.add_mul_div_left _ _ hd, Nat.zero_div, zero_add]
      exact ⟨rfl, by push_cast; rfl⟩
    · have hq1' : q + 1 = d' := by omega
      have heq : v + 1 = d * d' := by rw [← hq1']; omega
      rw [hval, heq, Nat.mod_self, Nat.zero_mod, Nat.zero_div]
      refine ⟨rfl, ?_⟩
      rw [Nat.cast_zero, show ((q : ℕ) : ZMod d') + 1 = ((q + 1 : ℕ) : ZMod d') by push_cast; ring,
        hq1', ZMod.natCast_self]

omit [MeasurableSpace X] in
/-- The decomposition `j = l + d b` determines `j`. -/
theorem zmod_phase_inj {d d' : ℕ} (hd : 0 < d) [NeZero (d * d')] {j j' : ZMod (d * d')}
    (hl : j.val % d = j'.val % d)
    (hb : ((j.val / d : ℕ) : ZMod d') = ((j'.val / d : ℕ) : ZMod d')) : j = j' := by
  have hq : ∀ k : ZMod (d * d'), k.val / d < d' := fun k =>
    (Nat.div_lt_iff_lt_mul hd).2 ((ZMod.val_lt k).trans_eq (mul_comm d d'))
  have hb' : j.val / d = j'.val / d := by
    have := congrArg ZMod.val hb
    rwa [ZMod.val_cast_of_lt (hq j), ZMod.val_cast_of_lt (hq j')] at this
  refine ZMod.val_injective _ ?_
  rw [← Nat.div_add_mod j.val d, ← Nat.div_add_mod j'.val d, hl, hb']

omit [MeasurableSpace X] in
/-- Every phase `(l, b)` with `l < d` occurs. -/
theorem zmod_phase_exists {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d') [NeZero (d * d')] {l : ℕ}
    (hl : l < d) (b : ZMod d') :
    ∃ j : ZMod (d * d'), j.val % d = l ∧ ((j.val / d : ℕ) : ZMod d') = b := by
  have : NeZero d' := ⟨hd'.ne'⟩
  have hb : b.val < d' := ZMod.val_lt b
  have hlt : l + d * b.val < d * d' := by
    have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hb)
    rw [Nat.mul_succ] at this
    omega
  refine ⟨((l + d * b.val : ℕ) : ZMod (d * d')), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt hlt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [ZMod.val_cast_of_lt hlt, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hl, zero_add,
      ZMod.natCast_zmod_val]

/-! ### Lifting a cycle of `Pᵈ` on `Dᵢ` to a cycle of `P` -/

/-- The set `G_{l, b} = {x ∈ D_{i+l} : P^{d−l}(x, E_{b+1}) = 1}`. -/
def liftPiece (P : Kernel X X) {d d' : ℕ} (D : ZMod d → Set X) (i : ZMod d)
    (E : ZMod d' → Set X) (l : ℕ) (b : ZMod d') : Set X :=
  {x | x ∈ D (i + (l : ZMod d)) ∧ (P ^ (d - l)) x (E (b + 1)) = 1}

/-- The class `F_j`, `j = l + d b`, of the lifted cycle: `E_b` if `l = 0`, `G_{l, b}`
otherwise. -/
noncomputable def liftClass (P : Kernel X X) {d d' : ℕ} (D : ZMod d → Set X) (i : ZMod d)
    (E : ZMod d' → Set X) (j : ZMod (d * d')) : Set X := by
  classical
  exact if j.val % d = 0 then E ((j.val / d : ℕ) : ZMod d')
    else liftPiece P D i E (j.val % d) ((j.val / d : ℕ) : ZMod d')

/-- Two probability-one events have a probability-one intersection. -/
theorem prob_inter_eq_one {μ : Measure X} [IsProbabilityMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (h1 : μ A = 1) (h2 : μ B = 1) :
    μ (A ∩ B) = 1 := by
  rw [← prob_compl_eq_zero_iff (hA.inter hB), compl_inter]
  exact measure_union_null ((prob_compl_eq_zero_iff hA).2 h1) ((prob_compl_eq_zero_iff hB).2 h2)

variable {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d d' : ℕ}
  {D : ZMod d → Set X} {i : ZMod d} {E : ZMod d' → Set X}

omit [IsMarkovKernel P] in
/-- A state of `F_j`, `j = l + d b`, lies in `D_{i+l}` and enters `E_{b+1}` with probability one
after `d − l` steps. -/
theorem mem_liftClass {j : ZMod (d * d')} (hEsub : ∀ b, E b ⊆ D i)
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) {x : X}
    (hx : x ∈ liftClass P D i E j) :
    x ∈ D (i + ((j.val % d : ℕ) : ZMod d)) ∧
      (P ^ (d - j.val % d)) x (E (((j.val / d : ℕ) : ZMod d') + 1)) = 1 := by
  unfold liftClass at hx
  split_ifs at hx with h
  · rw [h, Nat.cast_zero, add_zero, Nat.sub_zero]
    exact ⟨hEsub _ hx, hEstep _ x hx⟩
  · exact hx

/-- The key estimate: for `l < d`, the states of `D_{i+l}` that enter no `E_{b+1}` with
probability one after `d − l` steps form a `ψ`-null set. -/
theorem measure_liftPiece_compl (hψ : IsMaximalIrreducibility P ψ) (hd : 0 < d)
    (hD : IsCycle P ψ d D) (hEm : ∀ b, MeasurableSet (E b)) (hEsub : ∀ b, E b ⊆ D i)
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) (hEnull : ψ (D i \ ⋃ b, E b) = 0)
    (hd' : 0 < d') {l : ℕ} (hld : l < d) :
    ψ (D (i + (l : ZMod d)) \ ⋃ b, liftPiece P D i E l b) = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero d' := ⟨hd'.ne'⟩
  have hGm : ∀ b, MeasurableSet (liftPiece P D i E l b) := fun b =>
    (hD.measurableSet _).inter (measurableSet_eq_fun (Kernel.measurable_coe _ (hEm _))
      measurable_const)
  set B := D (i + (l : ZMod d)) \ ⋃ b, liftPiece P D i E l b with hBdef
  have hBm : MeasurableSet B := (hD.measurableSet _).diff (MeasurableSet.iUnion hGm)
  by_contra hpos
  -- a state of some `E_{b₀}`
  have hψE : 0 < ψ (⋃ b, E b) := by
    have h1 := hD.measure_pos hψ hd i
    have h2 : ψ (D i) ≤ ψ (D i \ ⋃ b, E b) + ψ (⋃ b, E b) := by
      calc ψ (D i) ≤ ψ ((D i \ ⋃ b, E b) ∪ ⋃ b, E b) := measure_mono fun x hx => by
            by_cases h : x ∈ ⋃ b, E b
            · exact Or.inr h
            · exact Or.inl ⟨hx, h⟩
        _ ≤ _ := measure_union_le _ _
    rw [hEnull, zero_add] at h2
    exact h1.trans_le h2
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hψE.ne'
  obtain ⟨b₀, hyb⟩ := mem_iUnion.1 hy
  -- `y` reaches `B` at some time `n + 1 ≡ l (mod d)`
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hBm y).1 (hψ.2.1 B hBm (pos_iff_ne_zero.2 hpos) y)
  have hcast : ((n + 1 : ℕ) : ZMod d) = (l : ZMod d) := by
    by_contra hne
    have h0 := hD.pow_apply_eq_zero (n + 1) (hEsub b₀ hyb) (j := i + (l : ZMod d))
      (fun h => hne (by linear_combination -h))
    exact hn.ne' (measure_mono_null sdiff_subset h0)
  have hmod : (n + 1) % d = l := by
    have := (ZMod.natCast_eq_natCast_iff' (n + 1) l d).1 hcast
    rwa [Nat.mod_eq_of_lt hld] at this
  set s := (n + 1) / d
  have hns : n + 1 = d * s + l := by rw [← hmod]; exact (Nat.div_add_mod (n + 1) d).symm
  -- after `d s` steps the chain is in `E_{b₀+s}`, from which `B` is not reached in `l` steps
  have hEs : (P ^ (d * s)) y (E (b₀ + s)) = 1 := by
    have := isMarkovKernel_pow P d
    rw [pow_mul]
    exact pow_apply_eq_one_of_step (P ^ d) hEm hEstep s b₀ y hyb
  have hzero : ∀ z ∈ E (b₀ + s), (P ^ l) z B = 0 := fun z hz => by
    have := isMarkovKernel_pow P l
    have h1 : (P ^ l) z {w | (P ^ (d - l)) w (E (b₀ + s + 1)) = 1} = 1 := by
      have h2 := hEstep _ z hz
      rw [show d = l + (d - l) by omega, Kernel.pow_add_apply_eq_lintegral P l (d - l) z
        (hEm _)] at h2
      exact measure_setOf_eq_one (Kernel.measurable_coe _ (hEm _))
        (fun w => by have := isMarkovKernel_pow P (d - l); exact prob_le_one) h2
    have h3 := hD.pow_apply l (hEsub _ hz)
    have h4 := prob_inter_eq_one (hD.measurableSet _) (measurableSet_eq_fun
      (Kernel.measurable_coe _ (hEm _)) measurable_const) h3 h1
    rw [← prob_compl_eq_zero_iff ((hD.measurableSet _).inter (measurableSet_eq_fun
      (Kernel.measurable_coe _ (hEm _)) measurable_const))] at h4
    refine measure_mono_null (show B ⊆ (D (i + (l : ZMod d)) ∩
      {w | (P ^ (d - l)) w (E (b₀ + s + 1)) = 1})ᶜ from
        fun w hw hw' => hw.2 (mem_iUnion.2 ⟨b₀ + s, hw'⟩)) h4
  have := isMarkovKernel_pow P (d * s)
  rw [hns, Kernel.pow_add_apply_eq_lintegral P (d * s) l y hBm] at hn
  have hae : ∀ᵐ z ∂(P ^ (d * s)) y, z ∈ E (b₀ + s) :=
    mem_ae_iff.2 ((prob_compl_eq_zero_iff (hEm (b₀ + s))).2 hEs)
  have h0 : ∫⁻ z, (P ^ l) z B ∂(P ^ (d * s)) y = 0 := by
    rw [lintegral_congr_ae (hae.mono fun z hz => hzero z hz), lintegral_zero]
  exact hn.ne' h0

/-- The lifted family `F_{l + d b}` is a `dd'`-cycle of `Φ`. -/
theorem isCycle_liftClass (hψ : IsMaximalIrreducibility P ψ) (hd : 0 < d)
    (hD : IsCycle P ψ d D) (hd' : 2 ≤ d') [NeZero (d * d')] (hEm : ∀ b, MeasurableSet (E b))
    (hEsub : ∀ b, E b ⊆ D i) (hEdisj : ∀ b c, b ≠ c → Disjoint (E b) (E c))
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) (hEnull : ψ (D i \ ⋃ b, E b) = 0) :
    IsCycle P ψ (d * d') (liftClass P D i E) := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero d' := ⟨by omega⟩
  have hGm : ∀ l b, MeasurableSet (liftPiece P D i E l b) := fun l b =>
    (hD.measurableSet _).inter (measurableSet_eq_fun (Kernel.measurable_coe _ (hEm _))
      measurable_const)
  -- the casts `l ↦ (l : ZMod d)` are injective below `d`
  have hcastinj : ∀ l l' : ℕ, l < d → l' < d → (l : ZMod d) = (l' : ZMod d) → l = l' :=
    fun l l' hl hl' h => by
      have := congrArg ZMod.val h
      rwa [ZMod.val_cast_of_lt hl, ZMod.val_cast_of_lt hl'] at this
  refine ⟨fun j => ?_, fun j j' hjj' => ?_, fun j x hx => ?_, ?_⟩
  · unfold liftClass
    split_ifs
    · exact hEm _
    · exact hGm _ _
  · refine Set.disjoint_left.2 fun x hx hx' => hjj' ?_
    obtain ⟨h1, h2⟩ := mem_liftClass hEsub hEstep hx
    obtain ⟨h1', h2'⟩ := mem_liftClass hEsub hEstep hx'
    have hl : j.val % d = j'.val % d := by
      by_contra hne
      refine Set.disjoint_left.1 (hD.disjoint _ _ fun h => hne (hcastinj _ _
        (Nat.mod_lt _ hd) (Nat.mod_lt _ hd) (add_left_cancel h))) h1 h1'
    refine zmod_phase_inj hd hl ?_
    by_contra hne
    rw [hl] at h2
    have := isMarkovKernel_pow P (d - j'.val % d)
    have hdisj : Disjoint (E (((j.val / d : ℕ) : ZMod d') + 1))
        (E (((j'.val / d : ℕ) : ZMod d') + 1)) :=
      hEdisj _ _ fun h => hne (add_right_cancel h)
    have hsum := measure_union (μ := (P ^ (d - j'.val % d)) x) hdisj (hEm _)
    rw [h2, h2'] at hsum
    have hle := prob_le_one (μ := (P ^ (d - j'.val % d)) x)
      (s := E (((j.val / d : ℕ) : ZMod d') + 1) ∪ E (((j'.val / d : ℕ) : ZMod d') + 1))
    rw [hsum] at hle
    norm_num at hle
  · -- the step `F_j → F_{j+1}`
    obtain ⟨h1, h2⟩ := mem_liftClass hEsub hEstep hx
    obtain ⟨hlt, hge⟩ := zmod_phase_succ hd hd' j
    by_cases hc : j.val % d + 1 < d
    · obtain ⟨e1, e2⟩ := hlt hc
      have hF : liftClass P D i E (j + 1) =
          liftPiece P D i E (j.val % d + 1) ((j.val / d : ℕ) : ZMod d') := by
        unfold liftClass
        simp only [e1, e2, Nat.add_one_ne_zero, ite_false]
      rw [hF]
      have hD1 := hD.step _ x h1
      have hreach : P x {y | (P ^ (d - (j.val % d + 1))) y
          (E (((j.val / d : ℕ) : ZMod d') + 1)) = 1} = 1 := by
        rw [show d - j.val % d = 1 + (d - (j.val % d + 1)) by omega,
          Kernel.pow_add_apply_eq_lintegral P 1 _ x (hEm _), pow_one] at h2
        exact measure_setOf_eq_one (Kernel.measurable_coe _ (hEm _))
          (fun y => by have := isMarkovKernel_pow P (d - (j.val % d + 1)); exact prob_le_one) h2
      have := prob_inter_eq_one (hD.measurableSet _) (measurableSet_eq_fun
        (Kernel.measurable_coe _ (hEm _)) measurable_const) hD1 hreach
      have hidx : i + ((j.val % d + 1 : ℕ) : ZMod d) = i + ((j.val % d : ℕ) : ZMod d) + 1 := by
        push_cast; ring
      unfold liftPiece
      rw [hidx]
      exact this
    · obtain ⟨e1, e2⟩ := hge hc
      have hF : liftClass P D i E (j + 1) = E (((j.val / d : ℕ) : ZMod d') + 1) := by
        unfold liftClass
        simp only [e1, e2, ite_true]
      rw [hF]
      have hd1 : d - j.val % d = 1 := by have := Nat.mod_lt j.val hd; omega
      rw [hd1, pow_one] at h2
      exact h2
  · -- the complement of the union is `ψ`-null
    have hcov : (⋃ j, liftClass P D i E j)ᶜ ⊆ (⋃ m, D m)ᶜ ∪ (D i \ ⋃ b, E b) ∪
        ⋃ l : Fin d, (D (i + ((l : ℕ) : ZMod d)) \ ⋃ b, liftPiece P D i E l b) := by
      intro x hx
      by_cases hU : x ∈ ⋃ m, D m
      · obtain ⟨m, hm⟩ := mem_iUnion.1 hU
        set l := (m - i).val with hl
        have hld : l < d := ZMod.val_lt _
        have hm' : m = i + (l : ZMod d) := by rw [hl, ZMod.natCast_zmod_val]; ring
        rw [hm'] at hm
        by_cases hl0 : l = 0
        · refine Or.inl (Or.inr ⟨by simpa [hl0] using hm, fun hE => hx ?_⟩)
          obtain ⟨b, hb⟩ := mem_iUnion.1 hE
          obtain ⟨j, hj1, hj2⟩ := zmod_phase_exists hd (by omega) (l := 0) hd b
          refine mem_iUnion.2 ⟨j, ?_⟩
          unfold liftClass
          simp only [hj1, hj2, ite_true]
          exact hb
        · refine Or.inr (mem_iUnion.2 ⟨⟨l, hld⟩, hm, fun hG => hx ?_⟩)
          obtain ⟨b, hb⟩ := mem_iUnion.1 hG
          obtain ⟨j, hj1, hj2⟩ := zmod_phase_exists hd (by omega) hld b
          refine mem_iUnion.2 ⟨j, ?_⟩
          unfold liftClass
          simp only [hj1, hj2, hl0, ite_false]
          exact hb
      · exact Or.inl (Or.inl hU)
    refine measure_mono_null hcov (measure_union_null (measure_union_null hD.null_compl
      hEnull) (measure_iUnion_null fun l => ?_))
    exact measure_liftPiece_compl hψ hd hD hEm hEsub hEstep hEnull (by omega) l.2

/-- **Proposition 5.4.6**, aperiodicity (MT p. 115). Let `Φ` have period `d` and `d`-cycle `{Dᵢ}`.
Then `Φ_d` on `Dᵢ` is aperiodic: every cycle `E_b ⊆ Dᵢ`, `b ∈ ZMod d'`, of `Pᵈ` (disjoint
measurable sets with `Pᵈ(x, E_{b+1}) = 1` on `E_b` and `ψ(Dᵢ \ ⋃ E_b) = 0`) has `d' = 1`. -/
theorem proposition_5_4_6_aperiodic (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {d : ℕ} (hper : IsPeriod P ψ d) {D : ZMod d → Set X}
    (hD : IsCycle P ψ d D) (i : ZMod d) {d' : ℕ} (hd' : 0 < d') {E : ZMod d' → Set X}
    (hEm : ∀ b, MeasurableSet (E b)) (hEsub : ∀ b, E b ⊆ D i)
    (hEdisj : ∀ b c, b ≠ c → Disjoint (E b) (E c))
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) (hEnull : ψ (D i \ ⋃ b, E b) = 0) :
    d' = 1 := by
  obtain ⟨hd, -, hmax⟩ := hper
  by_contra hne
  have hd'2 : 2 ≤ d' := by omega
  have : NeZero (d * d') := ⟨by positivity⟩
  have h := isCycle_liftClass hψ hd hD hd'2 hEm hEsub hEdisj hEstep hEnull
  have := hmax (d * d') _ (by positivity) h
  have : d * d' ≤ d * 1 := by rwa [mul_one]
  have := Nat.le_of_mul_le_mul_left this hd
  omega

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The period of the forward recurrence time chain (MT §5.4.4)

Meyn and Tweedie, §5.4.4, p. 115: for the forward recurrence time chain on the integers with
renewal distribution `p`, the period of the state `0` is `d = g.c.d.{n : p(n) > 0}` ("a simple
exercise").

* `fwdRecKernel p` (the chain of MT §3.3.1 on `ℤ₊`): from `0`, jump to `n − 1` with probability
  `p(n)`; from `j ≥ 1`, move to `j − 1`.
* `fwdRec_pow_le`, `fwdRec_pow_self`, `fwdRec_pow_ge`: the deterministic descent
  `Pᵏ(j, ·) = δ_{j−k}` for `k ≤ j`, and `Pᵏ(j, ·) = P^{k−j}(0, ·)` for `k ≥ j`.
* `fwdRec_return_pos`: every `n` with `p(n) > 0` is a return time to `0`;
  `fwdRec_return_decomp`: every return time `n` is `m + (n − m)` with `p(m) > 0` and `n − m` a
  return time or `0`.
* `periodAt_fwdRec` (MT p. 115): `d(0) = g.c.d.{n : p(n) > 0}`.

**Corrections.** None (the renewal distribution must have `p(0) = 0`).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The transition laws of the forward recurrence time chain on `ℤ₊` (MT §3.3.1): from `0` the
chain jumps to `n − 1` with probability `p(n)`; from `j ≥ 1` it moves to `j − 1`. -/
noncomputable def fwdRecMeas (p : Measure ℕ) (j : ℕ) : Measure ℕ :=
  if j = 0 then p.map (fun n => n - 1) else Measure.dirac (j - 1)

/-- The forward recurrence time chain. -/
noncomputable def fwdRecKernel (p : Measure ℕ) : Kernel ℕ ℕ :=
  ⟨fwdRecMeas p, measurable_of_countable _⟩

/-- The forward recurrence time chain is a transition kernel when `p` is a probability. -/
theorem isMarkovKernel_fwdRecKernel (p : Measure ℕ) [IsProbabilityMeasure p] :
    IsMarkovKernel (fwdRecKernel p) := by
  refine ⟨fun j => ⟨?_⟩⟩
  change fwdRecMeas p j univ = 1
  unfold fwdRecMeas
  split_ifs
  · rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ, preimage_univ,
      measure_univ]
  · simp

variable {p : Measure ℕ}

/-- The descent: `Pᵏ(j, ·) = δ_{j−k}` for `k ≤ j`. -/
theorem fwdRec_pow_le {j k : ℕ} (hk : k ≤ j) : (fwdRecKernel p ^ k) j = Measure.dirac (j - k) := by
  induction k with
  | zero => rw [pow_zero_apply, Nat.sub_zero]
  | succ k ih =>
    rw [pow_succ']
    change (fwdRecKernel p ∘ₖ (fwdRecKernel p ^ k)) j = _
    rw [Kernel.comp_apply, ih (by omega), Measure.dirac_bind (Kernel.measurable _)]
    change fwdRecMeas p (j - k) = _
    have hne : j - k ≠ 0 := by omega
    simp only [fwdRecMeas, hne, ite_false]
    rw [show j - k - 1 = j - (k + 1) by omega]

/-- `Pʲ(j, ·) = δ₀`. -/
theorem fwdRec_pow_self (j : ℕ) : (fwdRecKernel p ^ j) j = Measure.dirac 0 := by
  rw [fwdRec_pow_le le_rfl, Nat.sub_self]

/-- `Pᵏ(j, ·) = P^{k−j}(0, ·)` for `k ≥ j`. -/
theorem fwdRec_pow_ge {j k : ℕ} (hk : j ≤ k) :
    (fwdRecKernel p ^ k) j = (fwdRecKernel p ^ (k - j)) 0 := by
  rw [show k = (k - j) + j by omega, Kernel.pow_add, Kernel.comp_apply, fwdRec_pow_self,
    Measure.dirac_bind (Kernel.measurable _), Nat.add_sub_cancel]

/-- `Pⁿ⁺¹(0, {0}) = Σₘ p(m) Pⁿ(m − 1, {0})`. -/
theorem fwdRec_pow_succ_zero (n : ℕ) :
    (fwdRecKernel p ^ (n + 1)) 0 {0} =
      ∑' m, (fwdRecKernel p ^ n) (m - 1) {0} * p {m} := by
  rw [add_comm, Kernel.pow_add_apply_eq_lintegral _ 1 n 0 (measurableSet_singleton 0), pow_one]
  change ∫⁻ y, _ ∂fwdRecMeas p 0 = _
  simp only [fwdRecMeas, ite_true]
  rw [lintegral_map (Kernel.measurable_coe _ (measurableSet_singleton 0))
    (measurable_of_countable _), lintegral_countable']

/-- MT p. 115: every `n` with `p(n) > 0` is a return time to `0`. -/
theorem fwdRec_return_pos (hp0 : p {0} = 0) {n : ℕ} (hn : 0 < p {n}) :
    n ∈ returnSet (fwdRecKernel p) 0 := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => by rw [h, hp0] at hn; exact lt_irrefl _ hn
  refine ⟨hn1, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn1
  rw [fwdRec_pow_succ_zero]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (k + 1))
  rw [Nat.add_sub_cancel, fwdRec_pow_self]
  simpa using hn

/-- Every return time `n` to `0` splits as `n = m + (n − m)`, with `p(m) > 0` and `n − m` either
`0` or a return time. -/
theorem fwdRec_return_decomp (hp0 : p {0} = 0) {n : ℕ}
    (hn : n ∈ returnSet (fwdRecKernel p) 0) :
    ∃ m, m ≤ n ∧ 0 < p {m} ∧ (m = n ∨ n - m ∈ returnSet (fwdRecKernel p) 0) := by
  obtain ⟨hn1, hpos⟩ := hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn1
  rw [fwdRec_pow_succ_zero] at hpos
  obtain ⟨m, hm⟩ : ∃ m, 0 < (fwdRecKernel p ^ k) (m - 1) {0} * p {m} := by
    by_contra hc
    push Not at hc
    exact hpos.ne' (ENNReal.tsum_eq_zero.2 fun m => nonpos_iff_eq_zero.1 (hc m))
  have hpm : 0 < p {m} := pos_of_mul_pos_right hm zero_le
  have hP : 0 < (fwdRecKernel p ^ k) (m - 1) {0} := pos_of_mul_pos_left hm zero_le
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h => by rw [h, hp0] at hpm; exact lt_irrefl _ hpm
  -- the chain started at `m − 1` is at `0` at time `k` only if `m − 1 ≤ k`
  have hmk : m - 1 ≤ k := by
    by_contra hlt
    rw [fwdRec_pow_le (by omega), Measure.dirac_apply' _ (measurableSet_singleton 0),
      indicator_of_notMem (by simp; omega)] at hP
    exact lt_irrefl _ hP
  refine ⟨m, by omega, hpm, ?_⟩
  rw [fwdRec_pow_ge hmk] at hP
  rcases Nat.eq_or_lt_of_le hmk with h | h
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rwa [show k + 1 - m = k - (m - 1) by omega]

/-- **The period of the forward recurrence time chain** (MT p. 115): if `p(0) = 0`, then
`d(0) = g.c.d.{n : p(n) > 0}`. -/
theorem periodAt_fwdRec (hp0 : p {0} = 0) :
    periodAt (fwdRecKernel p) 0 = setGcd {n | 0 < p {n}} := by
  unfold periodAt setGcd
  congr 1
  ext d
  constructor
  · exact fun h n hn => h n (fwdRec_return_pos hp0 hn)
  · intro h n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      obtain ⟨m, hmn, hpm, hcase⟩ := fwdRec_return_decomp hp0 hn
      rcases hcase with rfl | hrest
      · exact h m hpm
      · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, hp0] at hpm; exact lt_irrefl _ hpm
        have h1 := ih (n - m) (by have := hrest.1; omega) hrest
        rw [show n = m + (n - m) by omega]
        exact dvd_add (h m hpm) h1

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Random recursions as transition kernels

Copied from the `MarkovModels` project (MT Chapters 1–2), with the namespace renamed, for
the model examples of Chapter 4.

Almost every model in MT, Chapters 1–2, is a random recursion `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)` driven by
an i.i.d. disturbance sequence with law `Γ` and an independent initial state (the conventions of
MT, §2, p. 22). This module builds the kernel of such a recursion once, so that each model of
the book is an instance.

* `recursionKernel Γ F`: `P(x, A) = Γ{w : F(x, w) ∈ A}`, the kernel of `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)`
  (MT, (2.4), p. 26; (NSS1), p. 29). It is a Markov kernel (`isMarkovKernel_recursionKernel`).
* `controlMap F k`: the maps `Fₖ(x₀, u₁, …, uₖ)` of MT, (2.5), p. 27, which define the
  associated control model CM(F) (MT, (2.6) and (2.8), pp. 27–29).
* `orbit F x ω`: the sample path driven by a fixed disturbance sequence `ω`; it is the control
  map evaluated at `(ω₁, …, ωₙ)` (`orbit_eq_controlMap`).
* `recursionKernel_pow_apply`: the `n`-step kernel is the image of the product measure `Γⁿ`
  under the control map, `Pⁿ(x, ·) = Γ^{⊗n} ∘ Fₙ(x, ·)⁻¹`.
* `law_orbit`: driven by an i.i.d. sequence `ω ~ Γ^{⊗ℕ}` (Mathlib's `Measure.infinitePi`), the
  sample path `Φₙ` has law `Pⁿ(x, ·)`: the recursion realizes the chain.
* `recursionKernel_comp_noise`: a recursion `F(x, g(v))` driven by `v ~ Γ'` has the kernel of
  `F(x, w)` driven by `w ~ Γ' ∘ g⁻¹`; this is how the storage and queueing models reduce to
  random walk on a half line (MT, §2.4.3, p. 44).
* `recursionKernel_const_noise`: a recursion that ignores its disturbance is the deterministic
  kernel of the semi-dynamical system `xₙ₊₁ = F(xₙ)` (MT, (1.3), p. 7; (2.3), p. 26; (DS1),
  p. 547).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X W V : Type*}

/-- The control maps `Fₖ : X × Wᵏ → X` of MT, (2.5), p. 27: `F₀(x) = x` and
`Fₖ₊₁(x₀, u₁, …, uₖ₊₁) = F(Fₖ(x₀, u₁, …, uₖ), uₖ₊₁)`. The trajectories
`xₖ = Fₖ(x₀, u₁, …, uₖ)` form the associated control model CM(F) (MT, (2.6) and (2.8),
pp. 27–29). -/
def controlMap (F : X × W → X) : (k : ℕ) → X → (Fin k → W) → X
  | 0, x, _ => x
  | k + 1, x, u => F (controlMap F k x (Fin.init u), u (Fin.last k))

/-- `F₀(x) = x`. -/
@[simp] theorem controlMap_zero (F : X × W → X) (x : X) (u : Fin 0 → W) :
    controlMap F 0 x u = x := rfl

/-- `Fₖ₊₁(x, u) = F(Fₖ(x, u₁, …, uₖ), uₖ₊₁)` (MT, (2.5)). -/
theorem controlMap_succ (F : X × W → X) (k : ℕ) (x : X) (u : Fin (k + 1) → W) :
    controlMap F (k + 1) x u = F (controlMap F k x (Fin.init u), u (Fin.last k)) := rfl

/-- `F₁(x₀, u₁) = F(x₀, u₁)` (MT, p. 27). -/
theorem controlMap_one (F : X × W → X) (x : X) (u : Fin 1 → W) :
    controlMap F 1 x u = F (x, u 0) := rfl

/-- The control maps also decompose at the first step:
`Fₖ₊₁(x, u₁, u₂, …, uₖ₊₁) = Fₖ(F(x, u₁), u₂, …, uₖ₊₁)`. -/
theorem controlMap_succ_cons (F : X × W → X) (k : ℕ) (x : X) (w : W) (u : Fin k → W) :
    controlMap F (k + 1) x (Fin.cons w u) = controlMap F k (F (x, w)) u := by
  induction k generalizing x w with
  | zero => rfl
  | succ k ih =>
    have h1 : Fin.init (Fin.cons w u : Fin (k + 2) → W) = Fin.cons w (Fin.init u) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [Fin.init, Fin.cons_succ]
    rw [controlMap_succ, controlMap_succ F k (F (x, w)) u, ← ih, h1, Fin.cons_last]

/-- The sample path of the recursion driven by a fixed disturbance sequence `ω`, following MT's
indexing: `Φ₀ = x` and `Φₙ₊₁ = F(Φₙ, ωₙ₊₁)` (the coordinate `ω₀` is unused). -/
def orbit (F : X × W → X) (x : X) (ω : ℕ → W) : ℕ → X
  | 0 => x
  | n + 1 => F (orbit F x ω n, ω (n + 1))

/-- `Φ₀ = x`. -/
@[simp] theorem orbit_zero (F : X × W → X) (x : X) (ω : ℕ → W) : orbit F x ω 0 = x := rfl

/-- `Φₙ₊₁ = F(Φₙ, ωₙ₊₁)`. -/
theorem orbit_succ (F : X × W → X) (x : X) (ω : ℕ → W) (n : ℕ) :
    orbit F x ω (n + 1) = F (orbit F x ω n, ω (n + 1)) := rfl

/-- The sample path is the control map evaluated at the disturbances:
`Φₙ = Fₙ(x, ω₁, …, ωₙ)` (MT, (2.6), p. 27). -/
theorem orbit_eq_controlMap (F : X × W → X) (x : X) (ω : ℕ → W) (n : ℕ) :
    orbit F x ω n = controlMap F n x (fun i => ω (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbit_succ, ih, controlMap_succ]
    rfl

variable [MeasurableSpace X] [MeasurableSpace W] [MeasurableSpace V]

/-- The transition kernel of the random recursion `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)` with disturbance law `Γ`:
`P(x, ·)` is the image of `Γ` under `w ↦ F(x, w)` (MT, (2.4), p. 26). It is built from the
disturbance law by `Kernel.map`. -/
noncomputable def recursionKernel (Γ : Measure W) (F : X × W → X) : Kernel X X :=
  (Kernel.id ×ₖ Kernel.const X Γ).map F

/-- The kernel of a random recursion at `x` is the image of the disturbance law under
`F(x, ·)`. -/
theorem recursionKernel_apply (Γ : Measure W) [SFinite Γ] {F : X × W → X} (hF : Measurable F)
    (x : X) : recursionKernel Γ F x = Γ.map fun w => F (x, w) := by
  rw [recursionKernel, Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  rfl

/-- `P(x, A) = Γ{w : F(x, w) ∈ A}` for a random recursion. -/
theorem recursionKernel_apply' (Γ : Measure W) [SFinite Γ] {F : X × W → X} (hF : Measurable F)
    (x : X) {A : Set X} (hA : MeasurableSet A) :
    recursionKernel Γ F x A = Γ {w | F (x, w) ∈ A} := by
  rw [recursionKernel_apply Γ hF x,
    Measure.map_apply (f := fun w => F (x, w)) (hF.comp measurable_prodMk_left) hA]
  rfl

/-- The kernel of a random recursion with a probability disturbance law is a Markov kernel. -/
theorem isMarkovKernel_recursionKernel (Γ : Measure W) [IsProbabilityMeasure Γ]
    {F : X × W → X} (hF : Measurable F) : IsMarkovKernel (recursionKernel Γ F) := by
  unfold recursionKernel
  exact Kernel.IsMarkovKernel.map _ hF

/-- Reducing the noise: the recursion `F(x, g(v))` driven by `v ~ Γ'` has the same kernel as
`F(x, w)` driven by the image law `w ~ Γ' ∘ g⁻¹`. -/
theorem recursionKernel_comp_noise (Γ' : Measure V) [SFinite Γ'] {F : X × W → X}
    (hF : Measurable F) {g : V → W} (hg : Measurable g) :
    recursionKernel Γ' (fun p => F (p.1, g p.2)) = recursionKernel (Γ'.map g) F := by
  have hF' : Measurable fun p : X × V => F (p.1, g p.2) :=
    hF.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  ext1 x
  rw [recursionKernel_apply _ hF' x, recursionKernel_apply _ hF x,
    Measure.map_map (g := fun w => F (x, w)) (hF.comp measurable_prodMk_left) hg]
  rfl

/-- A recursion that ignores its disturbance is the deterministic kernel of the semi-dynamical
system `xₙ₊₁ = T(xₙ)` (MT, (1.3), p. 7, and (DS1), p. 547). -/
theorem recursionKernel_const_noise (Γ : Measure W) [IsProbabilityMeasure Γ] {T : X → X}
    (hT : Measurable T) :
    recursionKernel Γ (fun p => T p.1) = Kernel.deterministic T hT := by
  ext1 x
  rw [recursionKernel_apply Γ (F := fun p => T p.1) (hT.comp measurable_fst) x,
    Kernel.deterministic_apply]
  change Measure.map (fun _ => T x) Γ = _
  rw [Measure.map_const, measure_univ, one_smul]

/-- The control maps are jointly measurable when `F` is. -/
theorem measurable_controlMap {F : X × W → X} (hF : Measurable F) (k : ℕ) :
    Measurable fun p : X × (Fin k → W) => controlMap F k p.1 p.2 := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    have hinit : Measurable fun u : Fin (k + 1) → W => Fin.init u :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply _
    exact hF.comp ((ih.comp (measurable_fst.prodMk (hinit.comp measurable_snd))).prodMk
      ((measurable_pi_apply (Fin.last k)).comp measurable_snd))

/-- Each section `u ↦ Fₖ(x, u)` of a control map is measurable. -/
theorem measurable_controlMap_right {F : X × W → X} (hF : Measurable F) (k : ℕ) (x : X) :
    Measurable (controlMap F k x) :=
  (measurable_controlMap hF k).comp measurable_prodMk_left

/-- **The `n`-step kernel of a random recursion.** `Pⁿ(x, ·)` is the image of the product law
`Γ^{⊗n}` of `(W₁, …, Wₙ)` under the control map `Fₙ(x, ·)`. -/
theorem recursionKernel_pow_apply (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : Measurable F) (n : ℕ) (x : X) :
    (recursionKernel Γ F ^ n) x = (Measure.pi fun _ : Fin n => Γ).map (controlMap F n x) := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero]
    change Kernel.id x = _
    rw [Kernel.id_apply]
    have hc : controlMap F 0 x = fun _ => x := rfl
    rw [hc, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    ext A hA
    rw [pow_succ']
    change (recursionKernel Γ F ∘ₖ (recursionKernel Γ F ^ n)) x A = _
    rw [Kernel.comp_apply' _ _ _ hA, ih,
      lintegral_map (Kernel.measurable_coe _ hA) (measurable_controlMap_right hF n x),
      Measure.map_apply (measurable_controlMap_right hF (n + 1) x) hA]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Γ) (Fin.last n)
    have hS : MeasurableSet (controlMap F (n + 1) x ⁻¹' A) :=
      measurable_controlMap_right hF (n + 1) x hA
    rw [← hmp.symm.measure_preimage_equiv, Measure.prod_apply_symm
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => W) (Fin.last n)).symm.measurable
        hS)]
    refine lintegral_congr fun u => ?_
    rw [recursionKernel_apply' Γ hF _ hA]
    congr 1
    ext w
    have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => W) (Fin.last n)).symm (w, u)
        = Fin.snoc u w := by
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    change _ ↔ controlMap F (n + 1) x
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => W) (Fin.last n)).symm (w, u)) ∈ A
    rw [he, controlMap_succ, Fin.init_snoc, Fin.snoc_last]
    rfl

/-- `Pⁿ(x, A) = Γ^{⊗n}{u : Fₙ(x, u) ∈ A}`. -/
theorem recursionKernel_pow_apply' (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : Measurable F) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (recursionKernel Γ F ^ n) x A =
      (Measure.pi fun _ : Fin n => Γ) {u | controlMap F n x u ∈ A} := by
  rw [recursionKernel_pow_apply Γ hF n x, Measure.map_apply (measurable_controlMap_right hF n x) hA]
  rfl

/-- The disturbances `(ω₁, …, ωₙ)` of an i.i.d. sequence `ω ~ Γ^{⊗ℕ}` have the product law
`Γ^{⊗n}`. -/
theorem infinitePi_map_shift (Γ : Measure W) [IsProbabilityMeasure Γ] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun ω : ℕ → W => fun i : Fin n => ω (i + 1)) =
      Measure.pi fun _ : Fin n => Γ := by
  have hm : Measurable fun ω : ℕ → W => fun i : Fin n => ω (i + 1) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set S : Finset ℕ := Finset.univ.image fun i : Fin n => (i : ℕ) + 1 with hS
  set t : ℕ → Set W := fun k => if h : 1 ≤ k ∧ k - 1 < n then s ⟨k - 1, h.2⟩ else Set.univ with ht
  have hpre : (fun ω : ℕ → W => fun i : Fin n => ω (i + 1)) ⁻¹' Set.univ.pi s =
      Set.pi (S : Set ℕ) t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, hS, ht]
    refine forall_congr' fun i => ?_
    have h1 : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 - 1 < n := ⟨by omega, by simp⟩
    rw [dite_eq_left h1]
    simp
  have hmt : ∀ k ∈ S, MeasurableSet (t k) := fun k _ => by
    simp only [ht]
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre, Measure.infinitePi_pi (fun _ : ℕ => Γ) hmt]
  rw [hS, Finset.prod_image (fun a _ b _ h => Fin.ext (by simpa using h))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 - 1 < n := ⟨by omega, by simp⟩
  simp only [ht, dite_eq_left h1]
  congr 2

/-- **The random recursion realizes the chain.** If the disturbances `ω₁, ω₂, …` are i.i.d. with
law `Γ`, the sample path `Φₙ = Fₙ(x, ω₁, …, ωₙ)` has law `Pⁿ(x, ·)`. -/
theorem law_orbit (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X} (hF : Measurable F)
    (x : X) (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun ω => orbit F x ω n) =
      (recursionKernel Γ F ^ n) x := by
  have hm : Measurable fun ω : ℕ → W => fun i : Fin n => ω (i + 1) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have h : (fun ω => orbit F x ω n) =
      controlMap F n x ∘ fun ω : ℕ → W => fun i : Fin n => ω (i + 1) := by
    funext ω
    exact orbit_eq_controlMap F x ω n
  rw [h, ← Measure.map_map (measurable_controlMap_right hF n x) hm, infinitePi_map_shift,
    recursionKernel_pow_apply Γ hF n x]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition kernels of random recursions (MT §3.5.5)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelKernels.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

Meyn and Tweedie, §3.5.5, pp. 71–72: the kernel of the scalar nonlinear state space model
SNSS(F), and more generally of any random recursion `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)`, together with the
general fact behind every model of §§3.3 and 3.5: driven by i.i.d. noise independent of `X₀`,
such a recursion is a Markov chain with that kernel.

The kernel itself is `recursionKernel Γ F` (from `ModelRecursion`), `P(x, ·) = Γ ∘ F(x, ·)⁻¹`.

* `recursionKernel_eq_lintegral_indicator`: `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)` (MT p. 72).
* `kfun_recursionKernel`, `kfunR_recursionKernel`: `Ph(x) = ∫ h(F(x, w)) Γ(dw)` for nonnegative
  and for real measurable `h` (MT p. 72).
* `eq_3_44`: (3.44), `Pᵏ(x, A) = ∫ 1{Fₖ(x, w₁, …, wₖ) ∈ A} Γ(dw₁)⋯Γ(dwₖ)`, with the product
  measure `Γ^{⊗k}`; `recursionKernel_pow_succ_apply` gives the iterated form
  `Pᵏ⁺¹(x, A) = ∫ Pᵏ(F(x, w), A) Γ(dw)`.
* `recursion_eq_controlMap`: a process with `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` satisfies
  `Xₖ = Fₖ(X₀, W₁, …, Wₖ)` (MT p. 72).
* `isMarkovChain_canonPath`: on the canonical space `X × V^ℕ` with law `μ ⊗ Γ^{⊗ℕ}`, the
  recursion `canonPath F` is a Markov chain with kernel `P` and initial law `μ`. It is proved with
  `isMarkovChain_of_step` along the history filtration `histFilt`.
* `isMarkovChain_of_recursion`: on any probability space, a recursion whose initial state and
  noise have joint law `μ ⊗ Γ^{⊗ℕ}` is a Markov chain with kernel `P`.
* `IsIIDNoise` and `isMarkovChain_of_iid`: the book's hypotheses, `W₁, W₂, …` i.i.d. with law `Γ`
  and independent of `X₀` (SNSS2), imply the joint law above, so the recursion is a Markov chain
  with kernel `P` (MT p. 72, "since `{Wₙ}` is assumed i.i.d.").
* `IsMarkovChain.map_eq`: the law of `Φₙ` for any Markov chain is `μPⁿ` (3.8).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]

/-- The SNSS(F) kernel (MT p. 72): `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)`. -/
theorem recursionKernel_eq_lintegral_indicator (Γ : Measure V) [SFinite Γ] {F : X × V → X}
    (hF : Measurable F) (x : X) {A : Set X} (hA : MeasurableSet A) :
    recursionKernel Γ F x A = ∫⁻ w, A.indicator 1 (F (x, w)) ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [recursionKernel_apply Γ hF x, ← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) hFx]

/-- MT p. 72: `Ph(x) = E[h(Xₙ₊₁) | Xₙ = x] = ∫ h(F(x, w)) Γ(dw)` for measurable `h ≥ 0`. -/
theorem kfun_recursionKernel (Γ : Measure V) [SFinite Γ] {F : X × V → X} (hF : Measurable F)
    {h : X → ℝ≥0∞} (hh : Measurable h) (x : X) :
    kfun (recursionKernel Γ F) h x = ∫⁻ w, h (F (x, w)) ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [kfun, recursionKernel_apply Γ hF x, lintegral_map hh hFx]

/-- MT p. 72: `Ph(x) = ∫ h(F(x, w)) Γ(dw)` for real measurable `h` (bounded `h` in the
book). -/
theorem kfunR_recursionKernel (Γ : Measure V) [SFinite Γ] {F : X × V → X} (hF : Measurable F)
    {h : X → ℝ} (hh : Measurable h) (x : X) :
    kfunR (recursionKernel Γ F) h x = ∫ w, h (F (x, w)) ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [kfunR, recursionKernel_apply Γ hF x,
    integral_map hFx.aemeasurable hh.aestronglyMeasurable]

/-- (3.44), MT p. 72: `Pᵏ(x, A) = ∫⋯∫ 1{Fₖ(x, w₁, …, wₖ) ∈ A} Γ(dw₁)⋯Γ(dwₖ)`, the
integral against the product law `Γ^{⊗k}` of `(W₁, …, Wₖ)`. -/
theorem eq_3_44 (Γ : Measure V) [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F)
    (k : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (recursionKernel Γ F ^ k) x A =
      ∫⁻ u, A.indicator 1 (controlMap F k x u) ∂(Measure.pi fun _ : Fin k => Γ) := by
  rw [recursionKernel_pow_apply Γ hF k x, ← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) (measurable_controlMap_right hF k x)]

/-- The iterated form of (3.44): `Pᵏ⁺¹(x, A) = ∫ Pᵏ(F(x, w), A) Γ(dw)`. -/
theorem recursionKernel_pow_succ_apply (Γ : Measure V) [IsProbabilityMeasure Γ]
    {F : X × V → X} (hF : Measurable F) (k : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (recursionKernel Γ F ^ (k + 1)) x A =
      ∫⁻ w, (recursionKernel Γ F ^ k) (F (x, w)) A ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [pow_succ_apply _ k x hA, recursionKernel_apply Γ hF x,
    lintegral_map (Kernel.measurable_coe _ hA) hFx]

/-! ### The recursion on the canonical space `X × V^ℕ` -/

/-- The history `(x, w₀, …, w_{n−1})` of a point `(x, w)` of the canonical space. Coordinate
`wₖ` of the canonical noise sequence plays the role of `Wₖ₊₁`. -/
def histMap (n : ℕ) (p : X × (ℕ → V)) : X × (Fin n → V) := (p.1, fun i => p.2 i)

/-- The history map is measurable. -/
theorem measurable_histMap (n : ℕ) : Measurable (histMap (X := X) (V := V) n) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp
    measurable_snd)

/-- The canonical recursion `Ψₙ(x, w) = Fₙ(x, w₀, …, w_{n−1})`: `Ψ₀ = x` and
`Ψₙ₊₁ = F(Ψₙ, wₙ)`. -/
def canonPath (F : X × V → X) (n : ℕ) (p : X × (ℕ → V)) : X :=
  controlMap F n p.1 fun i : Fin n => p.2 i

omit [MeasurableSpace X] [MeasurableSpace V] in
/-- `Ψ₀(x, w) = x`. -/
theorem canonPath_zero (F : X × V → X) (p : X × (ℕ → V)) : canonPath F 0 p = p.1 := rfl

omit [MeasurableSpace X] [MeasurableSpace V] in
/-- `Ψₙ₊₁ = F(Ψₙ, wₙ)`. -/
theorem canonPath_succ (F : X × V → X) (n : ℕ) (p : X × (ℕ → V)) :
    canonPath F (n + 1) p = F (canonPath F n p, p.2 n) := rfl

/-- Each `Ψₙ` is measurable. -/
theorem measurable_canonPath {F : X × V → X} (hF : Measurable F) (n : ℕ) :
    Measurable (canonPath F n) :=
  (measurable_controlMap hF n).comp (measurable_histMap n)

/-- The history filtration `𝓖ₙ = σ(x, w₀, …, w_{n−1})` on the canonical space. -/
def histFilt : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (X × (ℕ → V))) where
  seq n := MeasurableSpace.comap (histMap n) inferInstance
  mono' m n hmn := by
    have hproj : Measurable fun q : X × (Fin n → V) =>
        ((q.1, fun i : Fin m => q.2 (Fin.castLE hmn i)) : X × (Fin m → V)) :=
      measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp
        measurable_snd)
    have h : histMap (X := X) (V := V) m =
        (fun q : X × (Fin n → V) => ((q.1, fun i : Fin m => q.2 (Fin.castLE hmn i)) :
          X × (Fin m → V))) ∘ histMap n := rfl
    change MeasurableSpace.comap (histMap m) _ ≤ MeasurableSpace.comap (histMap n) _
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hproj.comap_le
  le' n := (measurable_histMap n).comap_le

/-- The first `n` coordinates of an i.i.d. sequence `w ∼ Γ^{⊗ℕ}` have law `Γ^{⊗n}`. -/
theorem infinitePi_map_fin (Γ : Measure V) [IsProbabilityMeasure Γ] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun ω : ℕ → V => fun i : Fin n => ω i) =
      Measure.pi fun _ : Fin n => Γ := by
  have hm : Measurable fun ω : ℕ → V => fun i : Fin n => ω i :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set S : Finset ℕ := Finset.range n with hS
  set t : ℕ → Set V := fun k => if h : k < n then s ⟨k, h⟩ else Set.univ with ht
  have hpre : (fun ω : ℕ → V => fun i : Fin n => ω i) ⁻¹' Set.univ.pi s =
      Set.pi (S : Set ℕ) t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hS, ht,
      Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h k hk
      rw [dite_eq_left hk]
      exact h ⟨k, hk⟩
    · intro h i
      have := h i i.2
      rwa [dite_eq_left i.2] at this
  have hmt : ∀ k ∈ S, MeasurableSet (t k) := fun k _ => by
    simp only [ht]
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre, Measure.infinitePi_pi (fun _ : ℕ => Γ) hmt, hS, Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [ht, dite_eq_left i.2]

/-- Splitting off the last coordinate: under `Γ^{⊗(n+1)}`, `(u₀, …, u_{n−1})` and `uₙ` are
independent with laws `Γ^{⊗n}` and `Γ`. -/
theorem pi_map_init_last (Γ : Measure V) [IsProbabilityMeasure Γ] (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => Γ).map (fun u => (Fin.init u, u (Fin.last n))) =
      (Measure.pi fun _ : Fin n => Γ).prod Γ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Γ) (Fin.last n)
  have h : (fun u : Fin (n + 1) → V => (Fin.init u, u (Fin.last n))) =
      Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) (Fin.last n)) := by
    funext u
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  rw [h, ← Measure.map_map measurable_swap hmp.measurable, hmp.map_eq, Measure.prod_swap]

/-- Under `μ ⊗ Γ^{⊗ℕ}`, the history `(x, w₀, …, w_{n−1})` and the next noise `wₙ` are
independent, with laws `μ ⊗ Γ^{⊗n}` and `Γ`. -/
theorem law_hist_next (μ : Measure X) [SFinite μ] (Γ : Measure V) [IsProbabilityMeasure Γ]
    (n : ℕ) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fun p => (histMap n p, p.2 n)) =
      (μ.prod (Measure.pi fun _ : Fin n => Γ)).prod Γ := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hAB : Measurable fun w : ℕ → V => ((fun i : Fin n => w i), w n) :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply n)
  have hν : ν.map (fun w : ℕ → V => ((fun i : Fin n => w i), w n)) =
      (Measure.pi fun _ : Fin n => Γ).prod Γ := by
    have hc : (fun w : ℕ → V => ((fun i : Fin n => w i), w n)) =
        (fun u : Fin (n + 1) → V => (Fin.init u, u (Fin.last n))) ∘
          (fun w : ℕ → V => fun i : Fin (n + 1) => w i) := by
      funext w
      rfl
    have hg : Measurable fun u : Fin (n + 1) → V => (Fin.init u, u (Fin.last n)) :=
      (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hf : Measurable fun w : ℕ → V => fun i : Fin (n + 1) => w i :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    rw [hc, ← Measure.map_map hg hf,
      infinitePi_map_fin, pi_map_init_last]
  have h1 : (μ.prod ν).map (Prod.map id fun w : ℕ → V => ((fun i : Fin n => w i), w n)) =
      μ.prod ((Measure.pi fun _ : Fin n => Γ).prod Γ) := by
    rw [← Measure.map_prod_map _ _ measurable_id hAB, Measure.map_id, hν]
  have hmp := (measurePreserving_prodAssoc μ (Measure.pi fun _ : Fin n => Γ) Γ).symm
  have h2 : (fun p : X × (ℕ → V) => (histMap n p, p.2 n)) =
      (MeasurableEquiv.prodAssoc (α := X) (β := Fin n → V) (γ := V)).symm ∘
        (Prod.map id fun w : ℕ → V => ((fun i : Fin n => w i), w n)) := by
    funext p
    rfl
  rw [h2, ← Measure.map_map hmp.measurable (measurable_id.prodMap hAB), h1, hmp.map_eq]

/-- The one-step property of the canonical recursion: for `G ∈ 𝓖ₙ` and measurable `f ≥ 0`,
`∫_G f(Ψₙ₊₁) = ∫_G Pf(Ψₙ)`. -/
theorem canon_step (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) (n : ℕ)
    {G : Set (X × (ℕ → V))} (hG : MeasurableSet[histFilt n] G) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p in G, f (canonPath F (n + 1) p) ∂(μ.prod (Measure.infinitePi fun _ => Γ)) =
      ∫⁻ p in G, ∫⁻ y, f y ∂recursionKernel Γ F (canonPath F n p)
        ∂(μ.prod (Measure.infinitePi fun _ => Γ)) := by
  obtain ⟨S, hS, rfl⟩ := hG
  set ρ := μ.prod (Measure.infinitePi fun _ : ℕ => Γ)
  set Θ : X × (ℕ → V) → (X × (Fin n → V)) × V := fun p => (histMap n p, p.2 n) with hΘdef
  have hΘ : Measurable Θ :=
    (measurable_histMap n).prodMk ((measurable_pi_apply n).comp measurable_snd)
  have hcm : Measurable fun q : X × (Fin n → V) => controlMap F n q.1 q.2 :=
    measurable_controlMap hF n
  have hφ : Measurable fun z : (X × (Fin n → V)) × V =>
      f (F (controlMap F n z.1.1 z.1.2, z.2)) :=
    hf.comp (hF.comp ((hcm.comp measurable_fst).prodMk measurable_snd))
  have hpre : histMap n ⁻¹' S = Θ ⁻¹' (S ×ˢ univ) := by
    ext p
    simp [Θ]
  have hL : ∫⁻ p in histMap n ⁻¹' S, f (canonPath F (n + 1) p) ∂ρ =
      ∫⁻ q in S, ∫⁻ v, f (F (controlMap F n q.1 q.2, v)) ∂Γ
        ∂(μ.prod (Measure.pi fun _ : Fin n => Γ)) := by
    rw [hpre]
    change ∫⁻ p in Θ ⁻¹' (S ×ˢ univ),
      (fun z : (X × (Fin n → V)) × V => f (F (controlMap F n z.1.1 z.1.2, z.2))) (Θ p) ∂ρ = _
    rw [← setLIntegral_map (hS.prod MeasurableSet.univ) hφ hΘ, law_hist_next,
      setLIntegral_prod _ hφ.aemeasurable]
    simp only [Measure.restrict_univ]
  have hmarg : ρ.map (histMap n) = μ.prod (Measure.pi fun _ : Fin n => Γ) := by
    have : histMap n = Prod.fst ∘ Θ := rfl
    rw [this, ← Measure.map_map measurable_fst hΘ, law_hist_next, Measure.map_fst_prod,
      measure_univ, one_smul]
  have hψ : Measurable fun q : X × (Fin n → V) =>
      ∫⁻ v, f (F (controlMap F n q.1 q.2, v)) ∂Γ :=
    hφ.lintegral_prod_right'
  rw [hL, ← hmarg, setLIntegral_map hS hψ (measurable_histMap n)]
  refine lintegral_congr fun p => ?_
  exact (kfun_recursionKernel Γ hF hf _).symm

/-- **The recursion on the canonical space is a Markov chain** (MT p. 72): under
`μ ⊗ Γ^{⊗ℕ}`, `Ψₙ₊₁ = F(Ψₙ, wₙ)` is a Markov chain with kernel `P(x, A) = Γ{w : F(x, w) ∈ A}`
and initial law `μ`. -/
theorem isMarkovChain_canonPath (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) :
    IsMarkovChain (recursionKernel Γ F) μ (μ.prod (Measure.infinitePi fun _ => Γ))
      (canonPath F) := by
  refine isMarkovChain_of_step _ μ (𝓖 := histFilt) (fun n => ?_) ?_
    (fun n G hG f hf => canon_step μ Γ hF n hG hf)
  · exact (measurable_controlMap hF n).comp (comap_measurable (histMap n))
  · rw [show canonPath F 0 = Prod.fst from rfl, Measure.map_fst_prod, measure_univ, one_smul]

omit [MeasurableSpace X] [MeasurableSpace V] in
variable {Ω : Type*} in
/-- MT p. 72: a process with `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` satisfies `Xₖ = Fₖ(X₀, W₁, …, Wₖ)`. -/
theorem recursion_eq_controlMap {F : X × V → X} {Φ : ℕ → Ω → X} {W : ℕ → Ω → V}
    (hrec : ∀ n ω, Φ (n + 1) ω = F (Φ n ω, W (n + 1) ω)) (k : ℕ) (ω : Ω) :
    Φ k ω = controlMap F k (Φ 0 ω) fun i => W (i + 1) ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [hrec, ih]
    rfl

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- **A random recursion is a Markov chain** (MT p. 72, and the general fact behind §3.5).
On any space `(Ω, ℙ)`, if `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` and `(X₀, (W₁, W₂, …))` has law `μ ⊗ Γ^{⊗ℕ}`,
then `X` is a Markov chain with kernel `P(x, A) = Γ{w : F(x, w) ∈ A}` and initial law `μ`. -/
theorem isMarkovChain_of_recursion (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) {pr : Measure Ω}
    {Φ : ℕ → Ω → X} {W : ℕ → Ω → V} (hΦ0 : Measurable (Φ 0)) (hW : ∀ n, Measurable (W n))
    (hrec : ∀ n ω, Φ (n + 1) ω = F (Φ n ω, W (n + 1) ω))
    (hlaw : pr.map (fun ω => (Φ 0 ω, fun n => W (n + 1) ω)) =
      μ.prod (Measure.infinitePi fun _ => Γ)) :
    IsMarkovChain (recursionKernel Γ F) μ pr Φ := by
  set Θ : Ω → X × (ℕ → V) := fun ω => (Φ 0 ω, fun n => W (n + 1) ω)
  have hΘ : Measurable Θ := hΦ0.prodMk (measurable_pi_iff.2 fun n => hW (n + 1))
  have hcomp : ∀ n, Φ n = canonPath F n ∘ Θ := fun n => by
    funext ω
    exact recursion_eq_controlMap hrec n ω
  have hc := isMarkovChain_canonPath μ Γ hF
  refine ⟨fun n => hcomp n ▸ (measurable_canonPath hF n).comp hΘ, fun n A hA => ?_⟩
  have hset : {ω | ∀ i ≤ n, Φ i ω ∈ A i} = Θ ⁻¹' {p | ∀ i ≤ n, canonPath F i p ∈ A i} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hcomp, Function.comp_apply]
  have hmeas : MeasurableSet {p : X × (ℕ → V) | ∀ i ≤ n, canonPath F i p ∈ A i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurable_canonPath hF i (hA i)
  rw [hset, ← Measure.map_apply hΘ hmeas, hlaw]
  exact hc.fdd n A hA

variable {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) (X₀ : Ω → X) (W : ℕ → Ω → V)
  (Γ : Measure V) in
/-- The noise hypotheses of the book (SNSS2), (SLM2), (RW1), (Q1)–(Q2), …: the disturbances
`W₁, W₂, …` are i.i.d. with law `Γ` and independent of the initial state `X₀`. The coordinate
`W₀` is not used. -/
structure IsIIDNoise : Prop where
  /-- Each `Wₙ` is a random variable. -/
  measurable : ∀ n, Measurable (W n)
  /-- `Wₙ₊₁ ∼ Γ`. -/
  law : ∀ n, pr.map (W (n + 1)) = Γ
  /-- `W₁, W₂, …` are mutually independent. -/
  iIndep : iIndepFun (fun n => W (n + 1)) pr
  /-- The noise sequence is independent of `X₀`. -/
  indep : IndepFun X₀ (fun ω n => W (n + 1) ω) pr

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- Under `IsIIDNoise`, the initial state and the noise have joint law `μ ⊗ Γ^{⊗ℕ}`. -/
theorem IsIIDNoise.map_eq {pr : Measure Ω} [IsProbabilityMeasure pr] {X₀ : Ω → X}
    {W : ℕ → Ω → V} {Γ : Measure V} (h : IsIIDNoise pr X₀ W Γ) (hX₀ : Measurable X₀) :
    pr.map (fun ω => (X₀ ω, fun n => W (n + 1) ω)) =
      (pr.map X₀).prod (Measure.infinitePi fun _ => Γ) := by
  have hWm : Measurable fun ω n => W (n + 1) ω :=
    measurable_pi_iff.2 fun n => h.measurable (n + 1)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX₀.aemeasurable hWm.aemeasurable).1 h.indep,
    h.iIndep.map_fun_eq_infinitePi_map (fun n => h.measurable (n + 1))]
  simp_rw [h.law]

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- **I.i.d. noise makes a recursion Markov** (MT p. 72). If `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` with
`W₁, W₂, …` i.i.d. with law `Γ` and independent of `X₀ ∼ μ`, then `X` is a Markov chain with
kernel `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)` and initial law `μ`. -/
theorem isMarkovChain_of_iid (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) {pr : Measure Ω}
    [IsProbabilityMeasure pr] {Φ : ℕ → Ω → X} {W : ℕ → Ω → V} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = F (Φ n ω, W (n + 1) ω)) (hinit : pr.map (Φ 0) = μ)
    (hW : IsIIDNoise pr (Φ 0) W Γ) :
    IsMarkovChain (recursionKernel Γ F) μ pr Φ := by
  refine isMarkovChain_of_recursion μ Γ hF hΦ0 hW.measurable hrec ?_
  rw [hW.map_eq hΦ0, hinit]

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- (3.8) for any Markov chain: the law of `Φₙ` is `μPⁿ`. -/
theorem IsMarkovChain.map_eq {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] {pr : Measure Ω} {Φ : ℕ → Ω → X} (h : IsMarkovChain P μ pr Φ)
    (n : ℕ) : pr.map (Φ n) = (P ^ n) ∘ₘ μ := by
  have hΦ : Measurable fun ω n => Φ n ω := measurable_pi_iff.2 h.measurable
  have hc : Φ n = (fun ω : ℕ → X => ω n) ∘ fun ω n => Φ n ω := rfl
  rw [hc, ← Measure.map_map (measurable_pi_apply n) hΦ, law_eq_pathMeasure P μ h,
    pathMeasure_map_coord]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Regeneration at random indices

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/Regeneration.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

The tool behind the Markov property of the renewal skeletons and of the GI/G/1 ladder chain
(MT §§3.5.3–3.5.4): an i.i.d. sequence starts afresh after a random index that is determined by
its past, and a process that is a function of the past and of such a fresh future is a Markov
chain.

* `truncSeq`, `tailSeq`, `indepFun_truncSeq_tailSeq`, `infinitePi_map_tailSeq`,
  `infinitePi_map_trunc_tail`: under `Γ^{⊗ℕ}` the first `k` terms and the tail from `k` on are
  independent, and the tail is again `Γ^{⊗ℕ}`.
* `lintegral_regeneration`: splitting over the values of the random index, the future at the
  index has, given the past, the law `ν` conditioned on the event that defines the index.
* `isMarkovChain_of_regeneration`: such a process is a Markov chain (via
  `isMarkovChain_of_step` on its natural filtration `pastFilt`).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The first `k` terms of a sequence, padded with zeros. -/
def truncSeq (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ := fun i => if i < k then w i else 0

/-- The sequence from index `k` on, `(w_k, w_{k+1}, …)`. -/
def tailSeq (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ := fun i => w (k + i)

/-- Truncation is measurable. -/
theorem measurable_truncSeq (k : ℕ) : Measurable (truncSeq k) :=
  measurable_pi_iff.2 fun i => by
    unfold truncSeq
    split_ifs
    · exact measurable_pi_apply i
    · exact measurable_const

/-- The tail map is measurable. -/
theorem measurable_tailSeq (k : ℕ) : Measurable (tailSeq k) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (k + i)

/-- The coordinates of an i.i.d. sequence `Γ^{⊗ℕ}` are independent. -/
theorem iIndep_coords (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    iIndep (fun i => MeasurableSpace.comap (fun w : ℕ → ℝ => w i) inferInstance)
      (Measure.infinitePi fun _ : ℕ => Γ) :=
  (iIndepFun_iff_iIndep _ _ _).1
    (iIndepFun_infinitePi (P := fun _ : ℕ => Γ) (X := fun _ => id) (fun _ => measurable_id))

/-- Under `Γ^{⊗ℕ}` the first `k` terms and the tail from `k` on are independent. -/
theorem indepFun_truncSeq_tailSeq (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    IndepFun (truncSeq k) (tailSeq k) (Measure.infinitePi fun _ : ℕ => Γ) := by
  set m : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun i => MeasurableSpace.comap (fun w : ℕ → ℝ => w i) inferInstance
  have hle : ∀ i, m i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  have hind := indep_iSup_of_disjoint hle (iIndep_coords Γ)
    (S := Iio k) (T := Ici k) (by
      rw [Set.disjoint_left]
      intro i hi hi'
      exact absurd (mem_Ici.1 hi') (not_le.2 (mem_Iio.1 hi)))
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
  · simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro i
    by_cases hi : i < k
    · simp only [truncSeq, hi, ite_true]
      exact le_iSup₂ (f := fun j (_ : j ∈ Iio k) => m j) i hi
    · simp only [truncSeq, hi, ite_false]
      exact (measurable_const (a := (0 : ℝ))).comap_le.trans bot_le
  · simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro i
    exact le_iSup₂ (f := fun j (_ : j ∈ Ici k) => m j) (k + i) (by simp)

/-- The tail of an i.i.d. sequence is again i.i.d. with the same law. -/
theorem infinitePi_map_tailSeq (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (tailSeq k) = Measure.infinitePi fun _ : ℕ => Γ := by
  have h := (iIndep_coords Γ).precomp (g := fun i => k + i) (fun a b hab => by simpa using hab)
  have h' : iIndepFun (fun i (w : ℕ → ℝ) => w (k + i)) (Measure.infinitePi fun _ : ℕ => Γ) :=
    (iIndepFun_iff_iIndep _ _ _).2 h
  have := h'.map_fun_eq_infinitePi_map (fun i => measurable_pi_apply (k + i))
  rw [show tailSeq k = fun w i => w (k + i) from rfl, this]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval _ _

/-- Under `Γ^{⊗ℕ}`, the pair (first `k` terms, tail from `k`) has law
`(law of the first k terms) ⊗ Γ^{⊗ℕ}`. -/
theorem infinitePi_map_trunc_tail (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun w => (truncSeq k w, tailSeq k w)) =
      ((Measure.infinitePi fun _ : ℕ => Γ).map (truncSeq k)).prod
        (Measure.infinitePi fun _ : ℕ => Γ) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_truncSeq k).aemeasurable
    (measurable_tailSeq k).aemeasurable).1 (indepFun_truncSeq_tailSeq Γ k),
    infinitePi_map_tailSeq]

variable {Ω β γ Y : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace Y]

/-- An integral against the conditional measure `ν[|D]` on a section `D = Sₓ` of a set. -/
theorem lintegral_cond_eq (ν : Measure γ) {S : Set (Y × γ)} (hS : MeasurableSet S)
    (g : Y × γ → ℝ≥0∞) (x : Y) :
    ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) =
      (ν {y | (x, y) ∈ S})⁻¹ * ∫⁻ y, S.indicator g (x, y) ∂ν := by
  have hSx : MeasurableSet {y | (x, y) ∈ S} := measurable_prodMk_left hS
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator hSx]
  congr 1

/-- `x ↦ ∫ g(x, y) ν[|Sₓ](dy)` is measurable. -/
theorem measurable_lintegral_cond (ν : Measure γ) [SFinite ν] {S : Set (Y × γ)}
    (hS : MeasurableSet S) {g : Y × γ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) := by
  simp_rw [lintegral_cond_eq ν hS g]
  exact (measurable_measure_prodMk_left hS).inv.mul (hg.indicator hS).lintegral_prod_right'

/-- `ν(Sₓ) ∫ g(x, ·) dν[|Sₓ] = ∫_{Sₓ} g(x, ·) dν`, also when `ν(Sₓ) = 0`. -/
theorem mul_lintegral_cond (ν : Measure γ) [IsFiniteMeasure ν] {S : Set (Y × γ)}
    (hS : MeasurableSet S) (g : Y × γ → ℝ≥0∞) (x : Y) :
    ν {y | (x, y) ∈ S} * ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) =
      ∫⁻ y, S.indicator g (x, y) ∂ν := by
  rw [lintegral_cond_eq ν hS g, ← mul_assoc]
  by_cases h0 : ν {y | (x, y) ∈ S} = 0
  · have hSx : MeasurableSet {y | (x, y) ∈ S} := measurable_prodMk_left hS
    have : ∫⁻ y, S.indicator g (x, y) ∂ν = 0 := by
      have he : (fun y => S.indicator g (x, y)) = {y | (x, y) ∈ S}.indicator (fun y => g (x, y)) :=
        by
        ext y
        by_cases hy : (x, y) ∈ S <;> simp [hy]
      rw [he, lintegral_indicator hSx]
      exact setLIntegral_measure_zero _ _ h0
    rw [this, mul_zero]
  · rw [ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

/-- **Regeneration at a random index.** Let `τ` be a random index such that, for each `k`, the
event `{τ = k}` is (almost surely) determined by a "past" `Bₖ` together with the event that the
"future" `Fₖ` lies in the section `S_{V}` of a set `S`, where `V` is a function of the past on
`{τ = k}`; and let the future be independent of the past with law `ν`. Then the future at `τ`,
given the past, has the conditional law `ν[|S_V]`:
`∫ g(V, F_τ) dP = ∫ ∫ g(V, y) ν[|S_V](dy) dP`. -/
theorem lintegral_regeneration (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure γ)
    [IsProbabilityMeasure ν] (τ : Ω → ℕ) (hτ : ∀ k, MeasurableSet {ω | τ ω = k})
    (B : ℕ → Ω → β) (hB : ∀ k, Measurable (B k)) (Fu : ℕ → Ω → γ)
    (hFu : ∀ k, Measurable (Fu k))
    (hlaw : ∀ k, P.map (fun ω => (B k ω, Fu k ω)) = (P.map (B k)).prod ν)
    (V : Ω → Y) {S : Set (Y × γ)} (hS : MeasurableSet S)
    (hpast : ∀ k, ∃ T : Set β, MeasurableSet T ∧ ∃ h : β → Y, Measurable h ∧
      ∀ᵐ ω ∂P, (τ ω = k ↔ (B k ω ∈ T ∧ (h (B k ω), Fu k ω) ∈ S)) ∧
        (τ ω = k → V ω = h (B k ω)))
    {g : Y × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (V ω, Fu (τ ω) ω) ∂P =
      ∫⁻ ω, ∫⁻ y, g (V ω, y) ∂(ν[|{y | (V ω, y) ∈ S}]) ∂P := by
  have hU : (univ : Set Ω) = ⋃ k, {ω | τ ω = k} := by
    ext ω
    simp
  have hdisj : Pairwise fun a b => Disjoint {ω : Ω | τ ω = a} {ω : Ω | τ ω = b} :=
    fun a b hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  have split : ∀ F : Ω → ℝ≥0∞, ∫⁻ ω, F ω ∂P = ∑' k, ∫⁻ ω in {ω | τ ω = k}, F ω ∂P := fun F => by
    rw [← setLIntegral_univ, hU, lintegral_iUnion hτ hdisj]
  rw [split, split]
  refine tsum_congr fun k => ?_
  obtain ⟨T, hT, h, hh, hae⟩ := hpast k
  set c : Y → ℝ≥0∞ := fun x => ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) with hc
  have hcm : Measurable c := measurable_lintegral_cond ν hS hg
  have hSB : MeasurableSet {q : β × γ | (h q.1, q.2) ∈ S} :=
    ((hh.comp measurable_fst).prodMk measurable_snd) hS
  have hE : MeasurableSet (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}) :=
    (measurable_fst hT).inter hSB
  have hBF : Measurable fun ω => (B k ω, Fu k ω) := (hB k).prodMk (hFu k)
  have hL : ∫⁻ ω in {ω | τ ω = k}, g (V ω, Fu (τ ω) ω) ∂P =
      ∫⁻ ω, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q => g (h q.1, q.2)) (B k ω, Fu k ω) ∂P := by
    rw [← lintegral_indicator (hτ k)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω ⟨h1, h2⟩
    by_cases hk : τ ω = k
    · have hm : (B k ω, Fu k ω) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} := h1.1 hk
      rw [indicator_of_mem (show ω ∈ {ω | τ ω = k} from hk), indicator_of_mem hm, h2 hk, hk]
    · have hm : (B k ω, Fu k ω) ∉ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} :=
        fun hm => hk (h1.2 hm)
      rw [indicator_of_notMem (show ω ∉ {ω | τ ω = k} from hk), indicator_of_notMem hm]
  have hR : ∫⁻ ω in {ω | τ ω = k}, c (V ω) ∂P =
      ∫⁻ ω, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q => c (h q.1)) (B k ω, Fu k ω) ∂P := by
    rw [← lintegral_indicator (hτ k)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω ⟨h1, h2⟩
    by_cases hk : τ ω = k
    · have hm : (B k ω, Fu k ω) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} := h1.1 hk
      rw [indicator_of_mem (show ω ∈ {ω | τ ω = k} from hk), indicator_of_mem hm, h2 hk]
    · have hm : (B k ω, Fu k ω) ∉ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} :=
        fun hm => hk (h1.2 hm)
      rw [indicator_of_notMem (show ω ∉ {ω | τ ω = k} from hk), indicator_of_notMem hm]
  change _ = ∫⁻ ω in {ω | τ ω = k}, c (V ω) ∂P
  rw [hL, hR]
  have hf1 : Measurable ((Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
      (fun q : β × γ => g (h q.1, q.2))) :=
    (hg.comp ((hh.comp measurable_fst).prodMk measurable_snd)).indicator hE
  have hf2 : Measurable ((Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
      (fun q : β × γ => c (h q.1))) :=
    (hcm.comp (hh.comp measurable_fst)).indicator hE
  rw [← lintegral_map hf1 hBF, ← lintegral_map hf2 hBF, hlaw k,
    lintegral_prod _ hf1.aemeasurable, lintegral_prod _ hf2.aemeasurable]
  refine lintegral_congr fun b => ?_
  by_cases hb : b ∈ T
  · have e1 : ∀ y, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q : β × γ => g (h q.1, q.2)) (b, y) = S.indicator g (h b, y) := fun y => by
      by_cases hy : (h b, y) ∈ S
      · rw [indicator_of_mem (show (b, y) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}
          from ⟨hb, hy⟩), indicator_of_mem hy]
      · rw [indicator_of_notMem (fun hm => hy hm.2), indicator_of_notMem hy]
    have e2 : ∀ y, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q : β × γ => c (h q.1)) (b, y) =
          {y | (h b, y) ∈ S}.indicator (fun _ => c (h b)) y := fun y => by
      by_cases hy : (h b, y) ∈ S
      · rw [indicator_of_mem (show (b, y) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}
          from ⟨hb, hy⟩), indicator_of_mem (show y ∈ {y | (h b, y) ∈ S} from hy)]
      · rw [indicator_of_notMem (fun hm => hy hm.2),
          indicator_of_notMem (show y ∉ {y | (h b, y) ∈ S} from hy)]
    simp_rw [e1, e2]
    rw [lintegral_indicator_const (s := {y | (h b, y) ∈ S}) (measurable_prodMk_left hS), mul_comm,
      hc,
      mul_lintegral_cond ν hS g (h b)]
  · have e : ∀ F : β × γ → ℝ≥0∞, ∀ y,
        (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator F (b, y) = 0 :=
      fun F y => indicator_of_notMem (fun hm => hb hm.1) _
    simp_rw [e]

/-- An integral over `v⁻¹(C)` as an integral against the indicator of `C ∘ v`. -/
theorem setLIntegral_preimage_eq {Z : Type*} [MeasurableSpace Z] (P : Measure Ω) {v : Ω → Z}
    (hv : Measurable v) {C : Set Z} (hC : MeasurableSet C) (F : Ω → ℝ≥0∞) :
    ∫⁻ ω in v ⁻¹' C, F ω ∂P = ∫⁻ ω, C.indicator 1 (v ω) * F ω ∂P := by
  rw [← lintegral_indicator (hv hC)]
  refine lintegral_congr fun ω => ?_
  by_cases h : v ω ∈ C
  · rw [indicator_of_mem (show ω ∈ v ⁻¹' C from h), indicator_of_mem h, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem (show ω ∉ v ⁻¹' C from h), indicator_of_notMem h, zero_mul]

variable {X : Type*} [MeasurableSpace X] in
/-- The natural filtration `σ(Ψ₀, …, Ψₙ)` of a process. -/
def pastFilt (Ψ : ℕ → Ω → X) (hΨ : ∀ n, Measurable (Ψ n)) :
    MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq n := MeasurableSpace.comap (fun ω (j : Fin (n + 1)) => Ψ j ω) inferInstance
  mono' m n hmn := by
    have hproj : Measurable fun v : Fin (n + 1) → X => fun j : Fin (m + 1) =>
        v (Fin.castLE (by omega) j) := measurable_pi_iff.2 fun j => measurable_pi_apply _
    have h : (fun ω (j : Fin (m + 1)) => Ψ j ω) =
        (fun v : Fin (n + 1) → X => fun j : Fin (m + 1) => v (Fin.castLE (by omega) j)) ∘
          (fun ω (j : Fin (n + 1)) => Ψ j ω) := rfl
    change MeasurableSpace.comap (fun ω (j : Fin (m + 1)) => Ψ j ω) _ ≤
      MeasurableSpace.comap (fun ω (j : Fin (n + 1)) => Ψ j ω) _
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hproj.comap_le
  le' n := (measurable_pi_iff.2 fun j : Fin (n + 1) => hΨ j).comap_le

variable {X : Type*} [MeasurableSpace X] in
/-- **A process that regenerates is a Markov chain.** Suppose that at each time `n` there is
a random index `τₙ` at which the process regenerates: given the past `σ(Ψ₀, …, Ψₙ)`, the future
noise `F_{n,τₙ}` has law `ν` conditioned on the section `S_{Ψₙ}`, and `Ψₙ₊₁ = Φ(Ψₙ, F_{n,τₙ})`
(all hypotheses almost surely). Then `Ψ` is a Markov chain with kernel
`Q(x, ·) = ν[|Sₓ] ∘ Φ(x, ·)⁻¹`. -/
theorem isMarkovChain_of_regeneration (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure γ)
    [IsProbabilityMeasure ν] (μ : Measure X) (Ψ : ℕ → Ω → X) (hΨ : ∀ n, Measurable (Ψ n))
    (h0 : P.map (Ψ 0) = μ) (τ : ℕ → Ω → ℕ) (hτ : ∀ n k, MeasurableSet {ω | τ n ω = k})
    (B : ℕ → ℕ → Ω → β) (hB : ∀ n k, Measurable (B n k)) (Fu : ℕ → ℕ → Ω → γ)
    (hFu : ∀ n k, Measurable (Fu n k))
    (hlaw : ∀ n k, P.map (fun ω => (B n k ω, Fu n k ω)) = (P.map (B n k)).prod ν)
    {S : Set (X × γ)} (hS : MeasurableSet S)
    (hpast : ∀ n k, ∃ T : Set β, MeasurableSet T ∧ ∃ h : β → (Fin (n + 1) → X), Measurable h ∧
      ∀ᵐ ω ∂P, (τ n ω = k ↔ (B n k ω ∈ T ∧ (h (B n k ω) (Fin.last n), Fu n k ω) ∈ S)) ∧
        (τ n ω = k → ∀ j : Fin (n + 1), Ψ j ω = h (B n k ω) j))
    {Φ : X × γ → X} (hΦ : Measurable Φ)
    (hstep : ∀ n, ∀ᵐ ω ∂P, Ψ (n + 1) ω = Φ (Ψ n ω, Fu n (τ n ω) ω))
    (Q : Kernel X X) (hQ : ∀ x, Q x = (ν[|{y | (x, y) ∈ S}]).map fun y => Φ (x, y)) :
    IsMarkovChain Q μ P Ψ := by
  refine isMarkovChain_of_step Q μ (𝓖 := pastFilt Ψ hΨ) (fun n => ?_) h0
    (fun n G hG f hf => ?_)
  · exact (measurable_pi_apply (Fin.last n)).comp
      (comap_measurable (fun ω (j : Fin (n + 1)) => Ψ j ω))
  obtain ⟨C, hC, rfl⟩ := hG
  set pv : Ω → (Fin (n + 1) → X) := fun ω j => Ψ j ω with hpvdef
  have hpv : Measurable pv := measurable_pi_iff.2 fun j => hΨ j
  set S' : Set ((Fin (n + 1) → X) × γ) := {q | (q.1 (Fin.last n), q.2) ∈ S} with hS'def
  have hS' : MeasurableSet S' :=
    (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk measurable_snd) hS
  set g : (Fin (n + 1) → X) × γ → ℝ≥0∞ :=
    fun q => C.indicator 1 q.1 * f (Φ (q.1 (Fin.last n), q.2)) with hgdef
  have hg : Measurable g :=
    ((measurable_one.indicator hC).comp measurable_fst).mul
      (hf.comp (hΦ.comp (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk
        measurable_snd)))
  have hreg := lintegral_regeneration P ν (τ n) (hτ n) (B n) (hB n) (Fu n) (hFu n) (hlaw n) pv
    hS' (g := g) (fun k => by
      obtain ⟨T, hT, h, hh, hae⟩ := hpast n k
      refine ⟨T, hT, h, hh, ?_⟩
      filter_upwards [hae] with ω ⟨h1, h2⟩
      exact ⟨h1, fun hk => funext fun j => h2 hk j⟩) hg
  change ∫⁻ ω in pv ⁻¹' C, f (Ψ (n + 1) ω) ∂P = ∫⁻ ω in pv ⁻¹' C, ∫⁻ y, f y ∂Q (Ψ n ω) ∂P
  rw [setLIntegral_preimage_eq P hpv hC, setLIntegral_preimage_eq P hpv hC]
  have hL : ∫⁻ ω, C.indicator 1 (pv ω) * f (Ψ (n + 1) ω) ∂P =
      ∫⁻ ω, g (pv ω, Fu n (τ n ω) ω) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep n] with ω hω
    rw [hω]
    rfl
  rw [hL, hreg]
  refine lintegral_congr fun ω => ?_
  have hΦx : Measurable fun y => Φ (Ψ n ω, y) := hΦ.comp measurable_prodMk_left
  rw [hQ, lintegral_map hf hΦx]
  change ∫⁻ y, C.indicator 1 (pv ω) * f (Φ (Ψ n ω, y)) ∂(ν[|{y | (Ψ n ω, y) ∈ S}]) = _
  exact lintegral_const_mul _ (hf.comp hΦx)

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Random walks

Copied from the `MarkovModels` project (MT Chapters 1–2), with the namespace renamed, for
the model examples of Chapter 4.

MT, §1.2.3, pp. 10–12, and (RW1), (RW2), (RWHL1) of Appendix C, p. 544.

* `randomWalkKernel Γ`: random walk `Φₖ₊₁ = Φₖ + Wₖ₊₁` with increment law `Γ` (MT, (RW1),
  (1.5)–(1.6), p. 11), on any measurable additive commutative monoid: `ℝ`, `ℝⁿ`, `ℤ`, `ℕ`.
  `P(x, A) = Γ(A − x)`; on `ℝ`, `P(x, (−∞, y]) = Γ(−∞, y − x]`
  (`randomWalkKernel_real_apply_Iic`).
* `orbit_randomWalk`: the sample path is `Φₙ = Φ₀ + W₁ + ⋯ + Wₙ`.
* `convPow Γ n`: the `n`-fold convolution power `Γ^{n∗}`, the law of `W₁ + ⋯ + Wₙ`;
  `randomWalkKernel_pow_apply`: `Pⁿ(x, ·)` is `Γ^{n∗}` shifted by `x`.
* `IsSpreadOut Γ`: (RW2), p. 544: some convolution power is not singular with respect to
  Lebesgue measure.
* `halfLineWalkKernel Γ`: random walk on a half line `Φₖ₊₁ = [Φₖ + Wₖ₊₁]⁺` on `ℝ≥0`
  (MT, (RWHL1), (1.7), p. 12). `P(x, {0}) = Γ(−∞, −x]` (`halfLineWalkKernel_apply_zero`) and
  `P(x, [0, y]) = Γ(−∞, y − x]` (`halfLineWalkKernel_apply_Iic`).
* The path claims of MT, p. 12: the reflected walk follows the unrestricted walk while that stays
  non-negative (`halfLineOrbit_eq_of_nonneg`), and leaves `0` only at a positive increment
  (`halfLineOrbit_succ_of_eq_zero`). Lindley's representation
  `Φₙ = max(x + Sₙ, max_{k ≤ n}(Sₙ − Sₖ))` (`halfLineOrbit_eq_lindley`) makes the first precise.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- Random walk on `G` (MT, (RW1), p. 11): `Φₖ₊₁ = Φₖ + Wₖ₊₁` with i.i.d. increments of law
`Γ`, as a random recursion with `F(x, w) = x + w`. -/
noncomputable def randomWalkKernel (Γ : Measure G) : Kernel G G :=
  recursionKernel Γ fun p => p.1 + p.2

omit [AddCommMonoid G] [MeasurableAdd₂ G] in
/-- The step map `(x, w) ↦ x + w` is measurable. -/
theorem measurable_add_step [Add G] [MeasurableAdd₂ G] :
    Measurable fun p : G × G => p.1 + p.2 :=
  measurable_fst.add measurable_snd

/-- `P(x, ·)` is the increment law shifted by `x`. -/
theorem randomWalkKernel_apply (Γ : Measure G) [SFinite Γ] (x : G) :
    randomWalkKernel Γ x = Γ.map (x + ·) :=
  recursionKernel_apply Γ measurable_add_step x

/-- `P(x, A) = Γ{w : x + w ∈ A}`. -/
theorem randomWalkKernel_apply' (Γ : Measure G) [SFinite Γ] (x : G) {A : Set G}
    (hA : MeasurableSet A) : randomWalkKernel Γ x A = Γ {w | x + w ∈ A} :=
  recursionKernel_apply' Γ measurable_add_step x hA

/-- Random walk is a Markov kernel. -/
theorem isMarkovKernel_randomWalkKernel (Γ : Measure G) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (randomWalkKernel Γ) :=
  isMarkovKernel_recursionKernel Γ measurable_add_step

/-- On `ℝ`, `P(x, (−∞, y]) = Γ(−∞, y − x]`: the transition law is the distribution function
of (1.6) shifted by `x`. -/
theorem randomWalkKernel_real_apply_Iic (Γ : Measure ℝ) [SFinite Γ] (x y : ℝ) :
    randomWalkKernel Γ x (Iic y) = Γ (Iic (y - x)) := by
  rw [randomWalkKernel_apply' Γ x measurableSet_Iic]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_Iic]
  constructor <;> intro h <;> linarith

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- The control maps of random walk are partial sums: `Fₙ(x, u) = x + u₁ + ⋯ + uₙ`. -/
theorem controlMap_add (n : ℕ) (x : G) (u : Fin n → G) :
    controlMap (fun p : G × G => p.1 + p.2) n x u = x + ∑ i, u i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [controlMap_succ, ih, Fin.sum_univ_castSucc, add_assoc]
    rfl

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- The sample path of random walk is `Φₙ = Φ₀ + W₁ + ⋯ + Wₙ`. -/
theorem orbit_randomWalk (x : G) (ω : ℕ → G) (n : ℕ) :
    orbit (fun p : G × G => p.1 + p.2) x ω n = x + ∑ i ∈ Finset.range n, ω (i + 1) := by
  rw [orbit_eq_controlMap, controlMap_add, Fin.sum_univ_eq_sum_range (fun i => ω (i + 1))]

/-- The `n`-fold convolution power `Γ^{n∗}`: the law of `W₁ + ⋯ + Wₙ` for i.i.d. `Wᵢ ~ Γ`. -/
noncomputable def convPow (Γ : Measure G) (n : ℕ) : Measure G :=
  (Measure.pi fun _ : Fin n => Γ).map fun u => ∑ i, u i

/-- `u ↦ u₁ + ⋯ + uₙ` is measurable. -/
theorem measurable_sum_fin (n : ℕ) : Measurable fun u : Fin n → G => ∑ i, u i :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- **`n`-step random walk.** `Pⁿ(x, ·)` is `Γ^{n∗}` shifted by `x`. -/
theorem randomWalkKernel_pow_apply (Γ : Measure G) [IsProbabilityMeasure Γ] (n : ℕ) (x : G) :
    (randomWalkKernel Γ ^ n) x = (convPow Γ n).map (x + ·) := by
  rw [randomWalkKernel, recursionKernel_pow_apply Γ measurable_add_step n x, convPow,
    Measure.map_map (measurable_const_add x) (measurable_sum_fin n)]
  congr 1
  funext u
  exact controlMap_add n x u

/-- (RW2), MT p. 544: the random walk (or its increment law `Γ`) is *spread out* if some
convolution power `Γ^{n∗}`, `n ≥ 1`, is not singular with respect to Lebesgue measure. -/
def IsSpreadOut (Γ : Measure ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ¬ convPow Γ n ⟂ₘ (volume : Measure ℝ)

/-- The step map `(x, w) ↦ [x + w]⁺` of random walk on a half line. -/
noncomputable def halfLineStep (p : ℝ≥0 × ℝ) : ℝ≥0 := Real.toNNReal (p.1 + p.2)

/-- The half-line step is measurable. -/
theorem measurable_halfLineStep : Measurable halfLineStep :=
  ((measurable_coe_nnreal_real.comp measurable_fst).add measurable_snd).real_toNNReal

/-- Random walk on a half line (MT, (RWHL1), (1.7), p. 12): `Φₖ₊₁ = [Φₖ + Wₖ₊₁]⁺` on
`ℝ≥0 = [0, ∞)`, with i.i.d. increments of law `Γ` on `ℝ`. -/
noncomputable def halfLineWalkKernel (Γ : Measure ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel Γ halfLineStep

/-- Random walk on a half line is a Markov kernel. -/
theorem isMarkovKernel_halfLineWalkKernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (halfLineWalkKernel Γ) :=
  isMarkovKernel_recursionKernel Γ measurable_halfLineStep

/-- `P(x, A) = Γ{w : [x + w]⁺ ∈ A}`. -/
theorem halfLineWalkKernel_apply' (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) {A : Set ℝ≥0}
    (hA : MeasurableSet A) :
    halfLineWalkKernel Γ x A = Γ {w | Real.toNNReal (x + w) ∈ A} :=
  recursionKernel_apply' Γ measurable_halfLineStep x hA

/-- The walk is held at zero with probability `P(x, {0}) = Γ(−∞, −x]`. -/
theorem halfLineWalkKernel_apply_zero (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) :
    halfLineWalkKernel Γ x {0} = Γ (Iic (-(x : ℝ))) := by
  rw [halfLineWalkKernel_apply' Γ x (measurableSet_singleton 0)]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, Real.toNNReal_eq_zero, mem_Iic]
  constructor <;> intro h <;> linarith

/-- `P(x, [0, y]) = Γ(−∞, y − x]` for `y ≥ 0`. -/
theorem halfLineWalkKernel_apply_Iic (Γ : Measure ℝ) [SFinite Γ] (x y : ℝ≥0) :
    halfLineWalkKernel Γ x (Iic y) = Γ (Iic ((y : ℝ) - x)) := by
  rw [halfLineWalkKernel_apply' Γ x measurableSet_Iic]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_Iic, Real.toNNReal_le_iff_le_coe]
  constructor <;> intro h <;> linarith

/-- `P(x, (y, ∞)) = Γ(y − x, ∞)` for `y ≥ 0`. -/
theorem halfLineWalkKernel_apply_Ioi (Γ : Measure ℝ) [SFinite Γ] (x y : ℝ≥0) :
    halfLineWalkKernel Γ x (Ioi y) = Γ (Ioi ((y : ℝ) - x)) := by
  rw [halfLineWalkKernel_apply' Γ x measurableSet_Ioi]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_Ioi, Real.lt_toNNReal_iff_coe_lt]
  constructor <;> intro h <;> linarith

/-- A path of random walk on a half line, `Φ₀ = x`, `Φₙ₊₁ = [Φₙ + ωₙ₊₁]⁺`. -/
noncomputable def halfLineOrbit (x : ℝ≥0) (ω : ℕ → ℝ) : ℕ → ℝ≥0 := orbit halfLineStep x ω

/-- The partial sums `Sₙ = ω₁ + ⋯ + ωₙ` of the increments. -/
def partialSum (ω : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ω (i + 1)

/-- In real coordinates the reflected walk satisfies `Φₙ₊₁ = max(Φₙ + ωₙ₊₁, 0)`. -/
theorem halfLineOrbit_succ_coe (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ) :
    (halfLineOrbit x ω (n + 1) : ℝ) = max ((halfLineOrbit x ω n : ℝ) + ω (n + 1)) 0 :=
  Real.coe_toNNReal' _

/-- MT, p. 12: the reflected walk follows the paths of the unrestricted random walk as long as
the latter stays non-negative: if `x + Sₖ ≥ 0` for all `k ≤ n` then `Φₙ = x + Sₙ`. -/
theorem halfLineOrbit_eq_of_nonneg (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ)
    (h : ∀ k ≤ n, 0 ≤ (x : ℝ) + partialSum ω k) :
    (halfLineOrbit x ω n : ℝ) = x + partialSum ω n := by
  induction n with
  | zero => simp [halfLineOrbit, partialSum]
  | succ n ih =>
    rw [halfLineOrbit_succ_coe, ih fun k hk => h k (by omega)]
    have hS : partialSum ω (n + 1) = partialSum ω n + ω (n + 1) := Finset.sum_range_succ _ _
    have h1 := h (n + 1) le_rfl
    rw [hS, ← add_assoc] at h1 ⊢
    exact max_eq_left h1

/-- MT, p. 12: the walk leaves zero only when the next increment is positive. -/
theorem halfLineOrbit_succ_of_eq_zero (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ)
    (h : halfLineOrbit x ω n = 0) :
    halfLineOrbit x ω (n + 1) = Real.toNNReal (ω (n + 1)) := by
  change Real.toNNReal ((halfLineOrbit x ω n : ℝ) + ω (n + 1)) = _
  rw [h, NNReal.coe_zero, zero_add]

/-- **Lindley's representation.** The reflected walk is
`Φₙ = max(x + Sₙ, max_{0 ≤ k ≤ n}(Sₙ − Sₖ))`. -/
theorem halfLineOrbit_eq_lindley (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ) :
    (halfLineOrbit x ω n : ℝ) = max ((x : ℝ) + partialSum ω n)
      ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => partialSum ω n - partialSum ω k) := by
  induction n with
  | zero =>
    simp only [halfLineOrbit, orbit_zero, partialSum, Finset.range_zero, Finset.sum_empty,
      add_zero, zero_add, Finset.range_one, Finset.sup'_singleton, sub_self]
    exact (max_eq_left x.2).symm
  | succ n ih =>
    rw [halfLineOrbit_succ_coe, ih]
    have hS : partialSum ω (n + 1) = partialSum ω n + ω (n + 1) := Finset.sum_range_succ _ _
    have hsup : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω n - partialSum ω k) + ω (n + 1) =
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω (n + 1) - partialSum ω k) := by
      rw [Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one (· + ω (n + 1))
        (fun a b => (max_add_add_right a b (ω (n + 1))).symm)]
      refine Finset.sup'_congr _ rfl fun k _ => ?_
      simp only [Function.comp_apply, hS]
      ring
    have hins : (Finset.range (n + 1 + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω (n + 1) - partialSum ω k) =
        max 0 ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω (n + 1) - partialSum ω k)) := by
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun k hk => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hk) with hk' | rfl
        · exact le_max_of_le_right (Finset.le_sup' (fun k => partialSum ω (n + 1) -
            partialSum ω k) (Finset.mem_range.mpr hk'))
        · simp
      · refine max_le ?_ (Finset.sup'_le _ _ fun k hk => ?_)
        · have := Finset.le_sup' (fun k => partialSum ω (n + 1) - partialSum ω k)
            (Finset.self_mem_range_succ (n + 1))
          rwa [sub_self] at this
        · exact Finset.le_sup' (fun k => partialSum ω (n + 1) - partialSum ω k)
            (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    rw [← max_add_add_right, hsup, hins, hS, ← add_assoc, max_comm 0, ← max_assoc]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Countable-space models

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelCountableModels.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

That module was in turn copied from the `MarkovModels` project
(`MarkovModels/CountableModels.lean`).

Countable-space chains previewed in MT, Chapters 1–2: the random walk on `ℤ₊` (reflected at `0`)
that the embedded queue length chains of §2.4.2 follow (MT, (2.28), p. 41), and the birth–death
chain on `ℤ₊`.

* `reflectedWalkKernel p`: `Nₙ₊₁ = [Nₙ + ξₙ₊₁]⁺` on `ℕ` with increments `ξ ~ p` on `ℤ`. Up to
  `0` the chain moves like the free walk, `P(j, {i}) = p{i − j}` for `i ≥ 1`
  (`reflectedWalkKernel_apply_pos`); `0` collects the whole lower tail,
  `P(j, {0}) = p(−∞, −j]` (`reflectedWalkKernel_apply_zero`).
* **Correction to (2.28).** MT claim that the queue length at arrivals satisfies
  `P(Nₙ₊₁ = j + k | Nₙ = j, …) = p_k` for all `k ≥ −j`, a random walk on `ℤ₊`. Taken literally,
  for all `j`, this forces the chain never to move down (`not_down_of_eq_2_28`): row `0` already
  has total mass `Σ_{k ≥ 0} p_k = 1`. For a random walk on `ℤ₊` the identity holds only for
  `j + k ≥ 1`, the boundary state `0` receiving the tail mass instead
  (`reflectedWalkKernel_apply_pos`, `reflectedWalkKernel_apply_zero`); `reflectedWalk_2_28_fails`
  is a concrete instance where `P(j, {0}) ≠ p_{−j}`.
* `birthDeathKernel b d`: from `i` up with probability `bᵢ`, down with probability `dᵢ`
  (staying at `0` instead of moving below it), and otherwise staying put.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The step `(j, ξ) ↦ [j + ξ]⁺` of random walk on `ℤ₊`. -/
def reflectStep (q : ℕ × ℤ) : ℕ := ((q.1 : ℤ) + q.2).toNat

/-- Random walk on `ℤ₊ = ℕ`: `Nₙ₊₁ = [Nₙ + ξₙ₊₁]⁺` with i.i.d. increments of law `p` on `ℤ`. -/
noncomputable def reflectedWalkKernel (p : Measure ℤ) : Kernel ℕ ℕ :=
  recursionKernel p reflectStep

/-- The reflected walk on `ℤ₊` is a Markov kernel. -/
theorem isMarkovKernel_reflectedWalkKernel (p : Measure ℤ) [IsProbabilityMeasure p] :
    IsMarkovKernel (reflectedWalkKernel p) :=
  isMarkovKernel_recursionKernel p (measurable_of_countable _)

/-- Away from `0` the reflected walk moves as the free walk: `P(j, {i}) = p{i − j}` for `i ≥ 1`. -/
theorem reflectedWalkKernel_apply_pos (p : Measure ℤ) [SFinite p] (j i : ℕ) (hi : 1 ≤ i) :
    reflectedWalkKernel p j {i} = p {(i : ℤ) - j} := by
  rw [reflectedWalkKernel, recursionKernel_apply' p (measurable_of_countable _) j
    (measurableSet_singleton i)]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, reflectStep]
  omega

/-- `0` collects the lower tail: `P(j, {0}) = p(−∞, −j]`. -/
theorem reflectedWalkKernel_apply_zero (p : Measure ℤ) [SFinite p] (j : ℕ) :
    reflectedWalkKernel p j {0} = p (Iic (-(j : ℤ))) := by
  rw [reflectedWalkKernel, recursionKernel_apply' p (measurable_of_countable _) j
    (measurableSet_singleton 0)]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, mem_Iic, reflectStep]
  omega

/-- **Correction to (2.28).** If a Markov kernel on `ℕ` satisfied `P(j, {j + k}) = p_k` for every
`j` and every `k ≥ −j`, as (2.28) states, then it could never move down: `P(j, {i}) = 0` for
`i < j`. -/
theorem not_down_of_eq_2_28 (P : Kernel ℕ ℕ) [IsMarkovKernel P] (p : ℤ → ℝ≥0∞)
    (h : ∀ (j : ℕ) (k : ℤ), -(j : ℤ) ≤ k → P j {((j : ℤ) + k).toNat} = p k) (j i : ℕ)
    (hij : i < j) : P j {i} = 0 := by
  have hdisj : ∀ n : ℕ, Pairwise (Function.onFun Disjoint fun k : ℕ => ({n + k} : Set ℕ)) :=
    fun n a b hab => by
      simp only [Function.onFun, disjoint_singleton]
      omega
  have hup : ∀ n : ℕ, P n (Ici n) = ∑' k : ℕ, p k := by
    intro n
    have hU : Ici n = ⋃ k : ℕ, ({n + k} : Set ℕ) := by
      ext m
      simp only [mem_Ici, mem_iUnion, mem_singleton_iff]
      exact ⟨fun hm => ⟨m - n, by omega⟩, fun ⟨k, hk⟩ => by omega⟩
    rw [hU, measure_iUnion (hdisj n) fun _ => measurableSet_singleton _]
    refine tsum_congr fun k => ?_
    have := h n k (by omega)
    rw [← this]
    congr 2
  have h0 : ∑' k : ℕ, p k = 1 := by
    rw [← hup 0, show Ici (0 : ℕ) = univ from Ici_bot, measure_univ]
  have hlow : P j (Iio j) = 0 := by
    have hc : (Iio j)ᶜ = Ici j := by
      ext m
      simp
    have := measure_add_measure_compl (μ := P j) (measurableSet_Iio (a := j))
    rw [hc, hup j, h0, measure_univ] at this
    have h1 : P j (Iio j) + 1 = 0 + 1 := by rw [this, zero_add]
    exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp h1
  exact measure_mono_null (singleton_subset_iff.mpr hij) hlow

/-- The increment law of `reflectedWalk_2_28_fails`: `ξ ∈ {−2, 1}` with probability `1/2`
each. -/
noncomputable def twoPointLaw : Measure ℤ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (-2) + Measure.dirac 1)

/-- An instance of the failure of (2.28) at `k = −j`: for increments `ξ ∈ {−2, 1}` with
probability `1/2` each, `P(1, {0}) = 1/2` while `p_{−1} = 0`. -/
theorem reflectedWalk_2_28_fails :
    reflectedWalkKernel twoPointLaw 1 {0} ≠ twoPointLaw {(1 : ℤ) + (-1)} := by
  rw [reflectedWalkKernel_apply_zero]
  simp only [twoPointLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul, Nat.cast_one]
  rw [Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic,
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  norm_num [indicator]

/-- The birth–death chain on `ℤ₊`: from `i`, up to `i + 1` with probability `bᵢ`, down to
`i − 1` with probability `dᵢ` (at `0` this means staying at `0`), and otherwise stay at `i`. -/
noncomputable def birthDeathKernel (b d : ℕ → ℝ≥0∞) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun i => b i • Measure.dirac (i + 1) + d i • Measure.dirac (i - 1) +
    (1 - (b i + d i)) • Measure.dirac i

/-- The birth–death transition law from `i`. -/
theorem birthDeathKernel_apply (b d : ℕ → ℝ≥0∞) (i : ℕ) :
    birthDeathKernel b d i = b i • Measure.dirac (i + 1) + d i • Measure.dirac (i - 1) +
      (1 - (b i + d i)) • Measure.dirac i := rfl

/-- The birth–death chain is a Markov kernel when `bᵢ + dᵢ ≤ 1`. -/
theorem isMarkovKernel_birthDeathKernel (b d : ℕ → ℝ≥0∞) (h : ∀ i, b i + d i ≤ 1) :
    IsMarkovKernel (birthDeathKernel b d) := by
  refine ⟨fun i => ⟨?_⟩⟩
  simp only [birthDeathKernel_apply, Measure.add_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_tsub_cancel_of_le (h i)]

/-- The birth–death chain moves up with probability `bᵢ`. -/
theorem birthDeathKernel_apply_succ (b d : ℕ → ℝ≥0∞) (i : ℕ) :
    birthDeathKernel b d i {i + 1} = b i := by
  simp only [birthDeathKernel_apply, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp [indicator]

/-- The birth–death chain moves down from `i + 1` with probability `dᵢ₊₁`. -/
theorem birthDeathKernel_apply_pred (b d : ℕ → ℝ≥0∞) (i : ℕ) :
    birthDeathKernel b d (i + 1) {i} = d (i + 1) := by
  simp only [birthDeathKernel_apply, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  have hne : i + 1 + 1 ≠ i := by omega
  simp [indicator, hne]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GI/G/1, GI/M/1 and M/G/1 queues

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelQueues.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

That module was in turn copied from the `MarkovModels` project (`MarkovModels/Queues.lean`).

MT, §2.4.2, pp. 40–43, and (Q1)–(Q5) of Appendix C, pp. 544–545. The queue has i.i.d.
interarrival times `T ~ G` (Q1) and independent i.i.d. service times `S ~ H` (Q2), one server
and first-come-first-served service (Q3).

* `waitingTimeKernel H G`: the waiting time of the `n`-th customer (equivalently the residual
  workload found by an arrival) follows Lindley's recursion `Wₙ₊₁ = [Wₙ + Sₙ − Tₙ₊₁]⁺`
  (`lindleyStep`); it is random walk on a half line with increment `S − T`
  (`waitingTimeKernel_eq_halfLineWalk`).
* `giM1Kernel q`: the GI/M/1 queue length `Nₙ = N(Tₙ−)` just before arrivals (MT, (2.28), p. 41),
  `Nₙ₊₁ = [Nₙ + 1 − Dₙ₊₁]⁺` with `D` the number of exponential service completions possible in
  an interarrival time, of law `q`. It rises by at most one (`giM1Kernel_apply_up`, MT, p. 41);
  `P(j, {j + 1 − i}) = q{i}` for `i ≤ j` (`giM1Kernel_apply_le`) and `P(j, {0}) = q[j + 1, ∞)`
  (`giM1Kernel_apply_zero`). `giM1Kernel_not_2_28` shows that (2.28), read literally, fails.
* `mG1Kernel a`: the M/G/1 queue length `N*ₙ` just after departures (MT, p. 43),
  `N*ₙ₊₁ = [N*ₙ − 1]⁺ + Aₙ₊₁` with `A` the number of arrivals during a service, of law `a`.
* The memoryless property behind the GI/M/1 and M/G/1 assumptions (MT, (Q4)–(Q5), p. 42):
  `P(S > t + z | S > z) = e^{−μt}` for exponential `S` (`expMeasure_memoryless`), and the
  up-step probability `P(S > T) = ∫ e^{−μt} G(dt)` (`expMeasure_prod_lt`). For other service laws
  the conditional probabilities in (2.30) differ (`dirac_not_memoryless`), which is why `N` is not
  Markov for a general GI/G/1 queue.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-! ### The GI/G/1 waiting time chain -/

/-- Lindley's recursion `Wₙ₊₁ = [Wₙ + Sₙ − Tₙ₊₁]⁺` with disturbance `(Sₙ, Tₙ₊₁)`. -/
noncomputable def lindleyStep (p : ℝ≥0 × (ℝ × ℝ)) : ℝ≥0 :=
  Real.toNNReal (p.1 + p.2.1 - p.2.2)

/-- Lindley's step is measurable. -/
theorem measurable_lindleyStep : Measurable lindleyStep :=
  (((measurable_coe_nnreal_real.comp measurable_fst).add
    (measurable_fst.comp measurable_snd)).sub (measurable_snd.comp measurable_snd)).real_toNNReal

/-- The GI/G/1 waiting time chain (Lindley's recursion), with service law `H` and interarrival
law `G` independent, so that `(Sₙ, Tₙ₊₁) ~ H ⊗ G`. -/
noncomputable def waitingTimeKernel (H G : Measure ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel (H.prod G) lindleyStep

/-- The waiting time chain is a Markov kernel. -/
theorem isMarkovKernel_waitingTimeKernel (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] : IsMarkovKernel (waitingTimeKernel H G) :=
  isMarkovKernel_recursionKernel _ measurable_lindleyStep

/-- The waiting time chain is random walk on a half line with increment `S − T`. -/
theorem waitingTimeKernel_eq_halfLineWalk (H G : Measure ℝ) [SFinite H] [SFinite G] :
    waitingTimeKernel H G = halfLineWalkKernel ((H.prod G).map fun p => p.1 - p.2) := by
  rw [halfLineWalkKernel, ← recursionKernel_comp_noise _ measurable_halfLineStep
    (g := fun p : ℝ × ℝ => p.1 - p.2) (measurable_fst.sub measurable_snd), waitingTimeKernel]
  congr 1
  funext p
  simp only [lindleyStep, halfLineStep, add_sub_assoc]

/-! ### The GI/M/1 queue length at arrivals -/

/-- The GI/M/1 step `(j, d) ↦ [j + 1 − d]⁺`: the arrival joins the `j` customers present and up
to `d` of them are served before the next arrival. -/
def giM1Step (p : ℕ × ℕ) : ℕ := p.1 + 1 - p.2

/-- The GI/M/1 queue length chain at arrival times, with `q` the law of the number of service
completions possible in one interarrival time (a mixed Poisson law under (Q4)). -/
noncomputable def giM1Kernel (q : Measure ℕ) : Kernel ℕ ℕ :=
  recursionKernel q giM1Step

/-- The GI/M/1 chain is a Markov kernel. -/
theorem isMarkovKernel_giM1Kernel (q : Measure ℕ) [IsProbabilityMeasure q] :
    IsMarkovKernel (giM1Kernel q) :=
  isMarkovKernel_recursionKernel q (measurable_of_countable _)

/-- `P(j, A) = q{d : [j + 1 − d]⁺ ∈ A}`. -/
theorem giM1Kernel_apply' (q : Measure ℕ) [SFinite q] (j : ℕ) (A : Set ℕ) :
    giM1Kernel q j A = q {d | j + 1 - d ∈ A} :=
  recursionKernel_apply' q (measurable_of_countable _) j (Set.to_countable A).measurableSet

/-- MT, p. 41: the queue length just before arrivals rises by at most one. -/
theorem giM1Kernel_apply_up (q : Measure ℕ) [SFinite q] (j : ℕ) :
    giM1Kernel q j (Ioi (j + 1)) = 0 := by
  rw [giM1Kernel_apply' q j]
  convert measure_empty (μ := q)
  ext d
  simp only [mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false]
  omega

/-- From `j`, the chain moves to `j + 1 − i` with probability `q{i}`, for `i ≤ j`. -/
theorem giM1Kernel_apply_le (q : Measure ℕ) [SFinite q] {i j : ℕ} (hij : i ≤ j) :
    giM1Kernel q j {j + 1 - i} = q {i} := by
  rw [giM1Kernel_apply' q j]
  congr 1
  ext d
  simp only [mem_ofPred_eq, mem_singleton_iff]
  omega

/-- From `j`, the queue empties before the next arrival with probability `q[j + 1, ∞)`. -/
theorem giM1Kernel_apply_zero (q : Measure ℕ) [SFinite q] (j : ℕ) :
    giM1Kernel q j {0} = q (Ici (j + 1)) := by
  rw [giM1Kernel_apply' q j]
  congr 1
  ext d
  simp only [mem_ofPred_eq, mem_singleton_iff, mem_Ici]
  omega

/-- **Correction to (2.28).** If two service completions in an interarrival time have positive
probability, the GI/M/1 chain does not satisfy (2.28) literally: no `p` gives
`P(j, {j + k}) = p_k` for all `k ≥ −j`. -/
theorem giM1Kernel_not_2_28 (q : Measure ℕ) [IsProbabilityMeasure q] (hq : q {2} ≠ 0) :
    ¬ ∃ p : ℤ → ℝ≥0∞, ∀ (j : ℕ) (k : ℤ), -(j : ℤ) ≤ k →
      giM1Kernel q j {((j : ℤ) + k).toNat} = p k := by
  rintro ⟨p, hp⟩
  have := isMarkovKernel_giM1Kernel q
  have h0 := not_down_of_eq_2_28 (giM1Kernel q) p hp 1 0 one_pos
  rw [giM1Kernel_apply_zero] at h0
  exact hq (measure_mono_null (singleton_subset_iff.mpr (mem_Ici.mpr le_rfl)) h0)

/-! ### The M/G/1 queue length at departures -/

/-- The M/G/1 step `(j, a) ↦ [j − 1]⁺ + a`: the departing customer leaves and `a` customers
arrive during the next service. -/
def mG1Step (p : ℕ × ℕ) : ℕ := p.1 - 1 + p.2

/-- The M/G/1 queue length chain at departure times, with `a` the law of the number of arrivals
during one service time (a mixed Poisson law under (Q5)). -/
noncomputable def mG1Kernel (a : Measure ℕ) : Kernel ℕ ℕ :=
  recursionKernel a mG1Step

/-- The M/G/1 chain is a Markov kernel. -/
theorem isMarkovKernel_mG1Kernel (a : Measure ℕ) [IsProbabilityMeasure a] :
    IsMarkovKernel (mG1Kernel a) :=
  isMarkovKernel_recursionKernel a (measurable_of_countable _)

/-- From `j ≥ 1` the chain moves to `j − 1 + i` with probability `a{i}`. -/
theorem mG1Kernel_apply (a : Measure ℕ) [SFinite a] {j : ℕ} (hj : 1 ≤ j) (i : ℕ) :
    mG1Kernel a j {j - 1 + i} = a {i} := by
  rw [mG1Kernel, recursionKernel_apply' a (measurable_of_countable _) j
    (measurableSet_singleton _)]
  congr 1
  ext d
  simp only [mem_ofPred_eq, mem_singleton_iff, mG1Step]
  omega

/-- An empty queue after a departure behaves as a queue with one customer left: the next
departure is that of the next arrival. -/
theorem mG1Kernel_zero (a : Measure ℕ) [SFinite a] : mG1Kernel a 0 = mG1Kernel a 1 := by
  rw [mG1Kernel, recursionKernel_apply a (measurable_of_countable _),
    recursionKernel_apply a (measurable_of_countable _)]
  rfl

/-! ### Exponential service times and the memoryless property -/

/-- The exponential survival function: `P(S > x) = e^{−μx}` for `x ≥ 0`. -/
theorem expMeasure_Ioi {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure μ (Ioi x) = ENNReal.ofReal (Real.exp (-(μ * x))) := by
  have := isProbabilityMeasure_expMeasure hμ
  have he : Real.exp (-(μ * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hμ,
    ite_eq_left hx, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1
  ring

/-- **The memoryless property** (MT, p. 42): for exponential service times,
`P(S > t + z) = e^{−μt} P(S > z)`, i.e. `P(S > t + z | S > z) = e^{−μt}` whatever the elapsed
service `z`. -/
theorem expMeasure_memoryless {μ : ℝ} (hμ : 0 < μ) {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) :
    expMeasure μ (Ioi (t + z)) = ENNReal.ofReal (Real.exp (-(μ * t))) * expMeasure μ (Ioi z) := by
  rw [expMeasure_Ioi hμ (by linarith), expMeasure_Ioi hμ hz,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- MT, p. 42: with exponential service and interarrival law `G` on `[0, ∞)`, the probability
that the job in service outlasts the next interarrival time is `P(S > T) = ∫ e^{−μt} G(dt)`. -/
theorem expMeasure_prod_lt {μ : ℝ} (hμ : 0 < μ) (G : Measure ℝ) [SFinite G]
    (hG : G (Iio 0) = 0) :
    ((expMeasure μ).prod G) {p | p.2 < p.1} =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(μ * t))) ∂G := by
  have := isProbabilityMeasure_expMeasure hμ
  rw [Measure.prod_apply_symm (measurableSet_lt measurable_snd measurable_fst)]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ t ∂G, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hG
  filter_upwards [hae] with t ht
  rw [← expMeasure_Ioi hμ ht]
  rfl

/-- MT, (2.30), p. 42: for most service laws the residual service depends on the elapsed
service. For a deterministic service time `S = 1`, `P(S > 1/2 | S > 0) = 1` but
`P(S > 1 | S > 1/2) = 0`. -/
theorem dirac_not_memoryless :
    (Measure.dirac (1 : ℝ)) (Ioi (1 / 2 + 0)) / (Measure.dirac (1 : ℝ)) (Ioi 0) ≠
      (Measure.dirac (1 : ℝ)) (Ioi (1 / 2 + 1 / 2)) / (Measure.dirac (1 : ℝ)) (Ioi (1 / 2)) := by
  rw [Measure.dirac_apply' _ measurableSet_Ioi, Measure.dirac_apply' _ measurableSet_Ioi,
    Measure.dirac_apply' _ measurableSet_Ioi, Measure.dirac_apply' _ measurableSet_Ioi]
  norm_num [indicator]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Storage models

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelStorage.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

That module was in turn copied from the `MarkovModels` project (`MarkovModels/Storage.lean`).

MT, §2.4.3–2.4.4, pp. 43–46, the Commentary, p. 47, and (SSM1)–(SSM2), (CSM1)–(CSM2) of
Appendix C, p. 545.

* `storageKernel H G r`: the simple storage model (Moran dam), `Φₙ₊₁ = [Φₙ + Sₙ − Jₙ]⁺` with
  inputs `S ~ H`, interarrival times `T ~ G` and release `J = rT` (MT, (SSM1)–(SSM2), p. 44). It
  is random walk on a half line with increment `W = S − J` (`storageKernel_eq_halfLineWalk`,
  MT, p. 44). The law of `J` satisfies (2.31), `P(J ≤ x) = G(−∞, x/r]` (`releaseLaw_Iic`), and
  the mean increment is `α − β`, mean input minus mean output (`storage_mean_increment`, MT,
  p. 44). With `r = 1` the model is the GI/G/1 waiting time chain (`storageKernel_one`, MT,
  p. 47).
* `releaseTime r x = ∫₀ˣ r(y)⁻¹ dy` (MT, (2.32), p. 45): strictly increasing for a positive
  continuous rate (`releaseTime_strictMonoOn`), and maps `[0, x]` one-to-one onto `[0, R(x)]`
  (`releaseTime_bijOn`), so `q(x, t) = R⁻¹(R(x) − t)` is well defined for `0 ≤ t ≤ R(x)`.
  **Correction:** MT say `R⁻¹(t)` is defined for all `t`; for `r(y) = 1 + y²`, `R = arctan` never
  reaches `π/2` (`releaseTime_not_surjective`).
* `contentKernel G q Hin`: the content-dependent storage model as printed in (CSM2), MT, p. 46,
  `Φₙ₊₁ = [Φₙ − Jₙ + Sₙ(Φₙ − Jₙ)]⁺`: release over an interarrival time (the level `q(x, T)`),
  then an input with level-dependent law `H_y`. The law of `Jₙ` is (2.33)
  (`contentRelease_Iic`), and `contentKernel_apply'` gives the transition law.
  **Correction:** that order (release, then input) gives the content just *after* inputs, not just
  before them as MT state; with constant release rate and input law it is not the simple storage
  model (`contentKernel_ne_storageKernel`). The content before inputs is `contentPreInputKernel`
  (input, then release), which reduces to the simple storage model
  (`contentPreInputKernel_eq_storageKernel`).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-! ### The simple storage model -/

/-- The simple storage step `Φ' = [Φ + S − rT]⁺` with disturbance `(S, T)`. -/
noncomputable def storageStep (r : ℝ) (p : ℝ≥0 × (ℝ × ℝ)) : ℝ≥0 :=
  Real.toNNReal (p.1 + p.2.1 - r * p.2.2)

/-- The storage step is measurable. -/
theorem measurable_storageStep (r : ℝ) : Measurable (storageStep r) :=
  (((measurable_coe_nnreal_real.comp measurable_fst).add
    (measurable_fst.comp measurable_snd)).sub
      (measurable_const.mul (measurable_snd.comp measurable_snd))).real_toNNReal

/-- The simple storage model with release rate `r` (MT, (SSM1)–(SSM2), p. 44): the contents
`Φₙ` just before the `n`-th input, with inputs `S ~ H` and interarrival times `T ~ G`
independent. -/
noncomputable def storageKernel (H G : Measure ℝ) (r : ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel (H.prod G) (storageStep r)

/-- The simple storage model is a Markov kernel. -/
theorem isMarkovKernel_storageKernel (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (r : ℝ) : IsMarkovKernel (storageKernel H G r) :=
  isMarkovKernel_recursionKernel _ (measurable_storageStep r)

/-- MT, p. 44: the simple storage model is random walk on a half line with increments
`Wₙ = Sₙ − Jₙ`, `Jₙ = rTₙ`. -/
theorem storageKernel_eq_halfLineWalk (H G : Measure ℝ) [SFinite H] [SFinite G] (r : ℝ) :
    storageKernel H G r = halfLineWalkKernel ((H.prod G).map fun p => p.1 - r * p.2) := by
  rw [halfLineWalkKernel, ← recursionKernel_comp_noise _ measurable_halfLineStep
    (g := fun p : ℝ × ℝ => p.1 - r * p.2)
    (measurable_fst.sub (measurable_const.mul measurable_snd)), storageKernel]
  congr 1
  funext p
  simp only [storageStep, halfLineStep, add_sub_assoc]

/-- (2.31), MT p. 44: the release `J = rT` between inputs has `P(J ≤ x) = G(−∞, x/r]`. -/
theorem releaseLaw_Iic (G : Measure ℝ) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (G.map (r * ·)) (Iic x) = G (Iic (x / r)) := by
  rw [Measure.map_apply (measurable_const_mul r) measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_preimage, mem_Iic]
  rw [le_div_iff₀ hr, mul_comm]

/-- The commentary of MT, p. 47: the residual workload of the GI/G/1 queue is the storage model
with unit release rate. -/
theorem storageKernel_one (H G : Measure ℝ) : storageKernel H G 1 = waitingTimeKernel H G := by
  rw [storageKernel, waitingTimeKernel]
  congr 1
  funext p
  simp only [storageStep, lindleyStep, one_mul]

/-- MT, p. 44: the mean increment of the storage model is `α − β`, the mean input
`α = ∫ x H(dx)` minus the mean output between inputs `β = ∫ rx G(dx)`. -/
theorem storage_mean_increment (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH : Integrable id H) (hG : Integrable id G) (r : ℝ) :
    ∫ w, w ∂((H.prod G).map fun p => p.1 - r * p.2) = (∫ x, x ∂H) - ∫ x, r * x ∂G := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - r * p.2 :=
    measurable_fst.sub (measurable_const.mul measurable_snd)
  rw [integral_map (f := fun w : ℝ => w) hm.aemeasurable measurable_id.aestronglyMeasurable]
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (H.prod G) := hH.comp_fst G
  have h2 : Integrable (fun p : ℝ × ℝ => r * p.2) (H.prod G) := (hG.const_mul r).comp_snd H
  rw [integral_sub h1 h2, integral_fun_fst (fun x : ℝ => x),
    integral_fun_snd (fun x : ℝ => r * x)]
  simp

/-! ### Content-dependent release -/

/-- The time to empty from level `x` without input, `R(x) = ∫₀ˣ r(y)⁻¹ dy` (MT, (2.32), p. 45). -/
noncomputable def releaseTime (r : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, (r y)⁻¹

/-- `R` is continuous for a positive continuous release rate. -/
theorem continuous_releaseTime {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) :
    Continuous (releaseTime r) :=
  intervalIntegral.continuous_primitive
    (fun a b => (hr.inv₀ fun y => (hpos y).ne').intervalIntegrable a b) 0

/-- MT, p. 45: `R` is strictly increasing for a positive continuous release rate. -/
theorem releaseTime_strictMono {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) :
    StrictMono (releaseTime r) := by
  intro a b hab
  have hint : ∀ c d, IntervalIntegrable (fun y => (r y)⁻¹) MeasureSpace.volume c d :=
    fun c d => (hr.inv₀ fun y => (hpos y).ne').intervalIntegrable c d
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)
  have hpos' : 0 < ∫ y in a..b, (r y)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint a b)
      (fun y _ => inv_pos.mpr (hpos y)) hab
  simp only [releaseTime]
  linarith

/-- `R` is strictly increasing on `[0, ∞)`. -/
theorem releaseTime_strictMonoOn {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) :
    StrictMonoOn (releaseTime r) (Ici 0) :=
  (releaseTime_strictMono hr hpos).strictMonoOn _

/-- **Corrected inverse.** For a positive continuous release rate and `x ≥ 0`, `R` maps `[0, x]`
one-to-one onto `[0, R(x)]`. Hence `q(x, t) = R⁻¹(R(x) − t)` is well defined for
`0 ≤ t ≤ R(x)`, which is all the model uses. -/
theorem releaseTime_bijOn {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) {x : ℝ}
    (hx : 0 ≤ x) : BijOn (releaseTime r) (Icc 0 x) (Icc 0 (releaseTime r x)) := by
  have hmono := releaseTime_strictMono hr hpos
  have h0 : releaseTime r 0 = 0 := intervalIntegral.integral_same
  refine ⟨fun y hy => ⟨?_, hmono.monotone hy.2⟩, (hmono.strictMonoOn _).injOn, fun s hs => ?_⟩
  · rw [← h0]
    exact hmono.monotone hy.1
  · rw [← h0] at hs
    exact intermediate_value_Icc hx (continuous_releaseTime hr hpos).continuousOn hs

/-- `R(x) = arctan x` for the release rate `r(y) = 1 + y²`. -/
theorem releaseTime_one_add_sq (x : ℝ) : releaseTime (fun y => 1 + y ^ 2) x = Real.arctan x := by
  simp only [releaseTime, ← one_div]
  rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]

/-- **Correction to MT, p. 45.** `R⁻¹(t)` need not be defined for all `t ≥ 0`: for
`r(y) = 1 + y²` the time to empty is `R(x) = arctan x < π/2` for every level `x`. -/
theorem releaseTime_not_surjective :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ x, releaseTime (fun y => 1 + y ^ 2) x ≠ t :=
  ⟨Real.pi / 2, by positivity, fun x => by
    rw [releaseTime_one_add_sq]
    exact (Real.arctan_lt_pi_div_two x).ne⟩

/-- The input kernel `y ↦ law of [y + S(y)]⁺` with `S(y) ~ H_y`. -/
noncomputable def inputKernel (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  (Kernel.id ×ₖ Hin).map halfLineStep

/-- The input kernel at `y` is the image of `H_y` under `s ↦ [y + s]⁺`. -/
theorem inputKernel_apply (Hin : Kernel ℝ≥0 ℝ) [IsSFiniteKernel Hin] (y : ℝ≥0) :
    inputKernel Hin y = (Hin y).map fun s => Real.toNNReal (y + s) := by
  rw [inputKernel, Kernel.map_apply _ measurable_halfLineStep, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map measurable_halfLineStep measurable_prodMk_left]
  rfl

/-- The content-dependent storage model as printed in (CSM2), MT p. 46: from level `x`, release
for an interarrival time `T ~ G` to the level `q(x, T)` (so `J = x − q(x, T)`), then add an input
`S ~ H_y` with `y = q(x, T)`. -/
noncomputable def contentKernel (G : Measure ℝ) (q : ℝ≥0 × ℝ → ℝ≥0) (Hin : Kernel ℝ≥0 ℝ) :
    Kernel ℝ≥0 ℝ≥0 :=
  inputKernel Hin ∘ₖ recursionKernel G q

/-- The content-dependent storage model taken just before inputs: add the input `S ~ H_x`, then
release for an interarrival time `T ~ G`. -/
noncomputable def contentPreInputKernel (G : Measure ℝ) (q : ℝ≥0 × ℝ → ℝ≥0)
    (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel G q ∘ₖ inputKernel Hin

/-- Both content-dependent kernels are Markov kernels. -/
theorem isMarkovKernel_contentKernel (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin] :
    IsMarkovKernel (contentKernel G q Hin) ∧ IsMarkovKernel (contentPreInputKernel G q Hin) := by
  have := isMarkovKernel_recursionKernel G hq
  have : IsMarkovKernel (inputKernel Hin) := by
    unfold inputKernel
    exact Kernel.IsMarkovKernel.map _ measurable_halfLineStep
  exact ⟨by unfold contentKernel; infer_instance, by unfold contentPreInputKernel; infer_instance⟩

/-- (2.33), MT p. 46: given `Φₙ = x`, the release `Jₙ = x − q(x, Tₙ)` has
`P(Jₙ ≤ y) = ∫ G(dt) 1{J_x(t) ≤ y}`. -/
theorem contentRelease_Iic (G : Measure ℝ) {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (x : ℝ≥0)
    (y : ℝ) :
    (G.map fun t => (x : ℝ) - q (x, t)) (Iic y) =
      ∫⁻ t, (Iic y).indicator 1 ((x : ℝ) - q (x, t)) ∂G := by
  have hm : Measurable fun t => (x : ℝ) - q (x, t) :=
    measurable_const.sub (measurable_coe_nnreal_real.comp (hq.comp measurable_prodMk_left))
  rw [Measure.map_apply hm measurableSet_Iic, ← lintegral_indicator_one (hm measurableSet_Iic)]
  rfl

/-- The transition law of (CSM2): `P(x, A) = ∫ G(dt) H_{q(x,t)}{s : [q(x, t) + s]⁺ ∈ A}`. -/
theorem contentKernel_apply' (G : Measure ℝ) [SFinite G] {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q)
    (Hin : Kernel ℝ≥0 ℝ) [IsSFiniteKernel Hin] (x : ℝ≥0) {A : Set ℝ≥0} (hA : MeasurableSet A) :
    contentKernel G q Hin x A =
      ∫⁻ t, Hin (q (x, t)) {s | Real.toNNReal (q (x, t) + s) ∈ A} ∂G := by
  rw [contentKernel, Kernel.comp_apply' _ _ _ hA, recursionKernel_apply G hq,
    lintegral_map (g := fun w => q (x, w)) (Kernel.measurable_coe _ hA)
      (hq.comp measurable_prodMk_left)]
  refine lintegral_congr fun t => ?_
  rw [inputKernel_apply, Measure.map_apply (f := fun s => Real.toNNReal (q (x, t) + s))
    (measurable_halfLineStep.comp measurable_prodMk_left) hA]
  rfl

/-- **Correction to (CSM2).** With constant release rate `1` (`q(x, t) = [x − t]⁺`), unit inputs
and unit interarrival times, (CSM2) moves from `0` to `1` with probability one, whereas the
contents just before inputs, the simple storage model, stay at `0`. -/
theorem contentKernel_ne_storageKernel :
    contentKernel (Measure.dirac 1) (fun p => Real.toNNReal (p.1 - p.2))
        (Kernel.const ℝ≥0 (Measure.dirac 1)) 0 {1} ≠
      storageKernel (Measure.dirac 1) (Measure.dirac 1) 1 0 {1} := by
  have hq : Measurable fun p : ℝ≥0 × ℝ => Real.toNNReal (p.1 - p.2) :=
    ((measurable_coe_nnreal_real.comp measurable_fst).sub measurable_snd).real_toNNReal
  rw [contentKernel_apply' _ hq _ 0 (measurableSet_singleton 1), lintegral_dirac,
    storageKernel,
    recursionKernel_apply' _ (measurable_storageStep 1) 0 (measurableSet_singleton 1),
    Measure.dirac_prod_dirac, Kernel.const_apply, Measure.dirac_apply, Measure.dirac_apply]
  norm_num [indicator, storageStep]

/-- **Corrected content-dependent model.** With constant release rate `r ≥ 0`
(`q(x, t) = [x − rt]⁺`), level-independent input law `H` and interarrival law `G` on `[0, ∞)`,
the content just before inputs is the simple storage model. -/
theorem contentPreInputKernel_eq_storageKernel (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hG : G (Iio 0) = 0) {r : ℝ} (hr : 0 ≤ r) :
    contentPreInputKernel G (fun p => Real.toNNReal (p.1 - r * p.2)) (Kernel.const ℝ≥0 H) =
      storageKernel H G r := by
  have hq : Measurable fun p : ℝ≥0 × ℝ => Real.toNNReal (p.1 - r * p.2) :=
    ((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_const.mul measurable_snd)).real_toNNReal
  ext x A hA
  rw [contentPreInputKernel, Kernel.comp_apply' _ _ _ hA, inputKernel_apply, Kernel.const_apply,
    lintegral_map (g := fun s : ℝ => Real.toNNReal (x + s)) (Kernel.measurable_coe _ hA)
      (measurable_halfLineStep.comp measurable_prodMk_left),
    storageKernel, recursionKernel_apply' _ (measurable_storageStep r) x hA,
    Measure.prod_apply (s := {w | storageStep r (x, w) ∈ A})
      ((measurable_storageStep r).comp measurable_prodMk_left hA)]
  refine lintegral_congr fun s => ?_
  rw [recursionKernel_apply' G hq _ hA]
  refine measure_congr ?_
  have hae : ∀ᵐ t ∂G, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hG
  filter_upwards [hae] with t ht
  change (Real.toNNReal ((Real.toNNReal (x + s) : ℝ) - r * t) ∈ A) =
    (Real.toNNReal (x + s - r * t) ∈ A)
  have hrt : 0 ≤ r * t := mul_nonneg hr ht
  have hkey : Real.toNNReal ((Real.toNNReal (x + s) : ℝ) - r * t) =
      Real.toNNReal (x + s - r * t) := by
    rcases le_or_gt 0 ((x : ℝ) + s) with h | h
    · rw [Real.coe_toNNReal _ h]
    · rw [Real.toNNReal_of_nonpos h.le, NNReal.coe_zero, Real.toNNReal_of_nonpos (by linarith),
        Real.toNNReal_of_nonpos (by linarith)]
  rw [hkey]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Renewal processes and recurrence time chains

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelRenewal.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

That module was in turn copied from the `MarkovModels` project (`MarkovModels/Renewal.lean`).

MT, §2.4.1, pp. 38–40, and (RT1)–(RT4) of Appendix C, p. 543.

* `renewalKernel p`: the renewal process `Zₙ₊₁ = Zₙ + Yₙ₊₁` on `ℤ₊` with increment law `p`, a
  random walk on `ℕ`. With `p(0) = 0` it moves up at every step (`renewalKernel_apply_Ioi`), and
  every renewal sequence tends to infinity (`le_renewal`): the chain is evanescent (MT, p. 38).
* `seqConv a b`: the convolution `a ∗ b (n) = Σ_{j ≤ n} a(j) b(n − j)` (MT, p. 39), with both forms
  of the definition (`seqConv_eq_sum_range`, `seqConv_comm`), and `seqConvPow a k = a^{k∗}`.
* `renewal_law`: for a delayed renewal process with delay law `a`,
  `P(Z_k = n) = a ∗ p^{k∗}(n)` (MT, p. 39); `renewal_law_one` is
  `P(Z₁ = n) = Σ_{j ≤ n} a(j) p(n − j)` (MT, p. 38).
* `forwardKernel p`: the forward recurrence time chain (MT, (RT1), p. 39): from `k > 1` it moves
  deterministically to `k − 1`, from `1` it is renewed with law `p`.
  `backwardKernel p`: the backward recurrence time (age) chain (MT, (RT2)): from age `j` it
  drops to `0` with the conditional renewal probability `p(j + 1)/p(j, ∞)` and otherwise ages by
  one.
* The pathwise dynamics described in MT, p. 39, for the recurrence times `fwdTime Z` and
  `bwdTime Z` of a strictly increasing sequence `Z` of renewal epochs (`fwdTime_succ_of_one_lt`,
  `fwdTime_succ_of_eq_one`, `bwdTime_succ_of_renewal`, `bwdTime_succ_of_not_renewal`).
  **Correction:** (RT2) takes an infimum over an empty set for `n < Z₀` (`bwdTime_set_empty`), so
  `V⁻(n)` is only defined from the first renewal on.
* `fwdTimeCts`, `bwdTimeCts` and their `δ`-skeletons: (RT3)–(RT4), p. 543.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### The renewal process -/

/-- The (delayed) renewal process `Zₙ₊₁ = Zₙ + Yₙ₊₁` on `ℤ₊` with i.i.d. increments of law `p`
(MT, p. 38): random walk on `ℕ`. -/
noncomputable def renewalKernel (p : Measure ℕ) : Kernel ℕ ℕ := randomWalkKernel p

/-- The renewal process is a Markov kernel. -/
theorem isMarkovKernel_renewalKernel (p : Measure ℕ) [IsProbabilityMeasure p] :
    IsMarkovKernel (renewalKernel p) :=
  isMarkovKernel_randomWalkKernel p

/-- `P(z, {n}) = p(n − z)` for `z ≤ n`, and `0` for `z > n`. -/
theorem renewalKernel_apply_singleton (p : Measure ℕ) [SFinite p] (z n : ℕ) :
    renewalKernel p z {n} = if z ≤ n then p {n - z} else 0 := by
  rw [renewalKernel, randomWalkKernel_apply' p z (measurableSet_singleton n)]
  split_ifs with h
  · congr 1
    ext w
    simp only [mem_ofPred_eq, mem_singleton_iff]
    omega
  · convert measure_empty (μ := p)
    ext w
    simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
    omega

/-- With `p(0) = 0` the renewal process moves up at every step: `P(z, (z, ∞)) = 1`. -/
theorem renewalKernel_apply_Ioi (p : Measure ℕ) [IsProbabilityMeasure p] (hp : p {0} = 0)
    (z : ℕ) : renewalKernel p z (Ioi z) = 1 := by
  rw [renewalKernel, randomWalkKernel_apply' p z measurableSet_Ioi]
  have h : {w : ℕ | z + w ∈ Ioi z} = ({0} : Set ℕ)ᶜ := by
    ext w
    simp only [mem_ofPred_eq, mem_Ioi, mem_compl_iff, mem_singleton_iff]
    omega
  rw [h, prob_compl_eq_one_sub (measurableSet_singleton 0), hp, tsub_zero]

/-- MT, p. 38: a renewal sequence with increments `≥ 1` is strictly increasing, so `Zₙ ≥ n`;
the renewal process is evanescent. -/
theorem le_renewal {Z : ℕ → ℕ} (hZ : StrictMono Z) (n : ℕ) : n ≤ Z n := hZ.id_le n

/-! ### Convolutions of sequences -/

/-- The convolution `a ∗ b (n) = Σ_{i + j = n} a(i) b(j)` (MT, p. 39), as the coefficients of the
product of generating functions. -/
noncomputable def seqConv (a b : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b)

/-- `a ∗ b (n) = Σ_{j=0}^{n} a(j) b(n − j)`. -/
theorem seqConv_eq_sum_range (a b : ℕ → ℝ≥0∞) (n : ℕ) :
    seqConv a b n = ∑ j ∈ Finset.range (n + 1), a j * b (n - j) := by
  rw [seqConv, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]

/-- The two forms of MT, p. 39: `Σ_j b(j) a(n − j) = Σ_j a(j) b(n − j)`. -/
theorem seqConv_comm (a b : ℕ → ℝ≥0∞) : seqConv a b = seqConv b a := by
  funext n
  rw [seqConv, seqConv, mul_comm]

/-- The `k`-th convolution power `a^{k∗}` (MT, p. 39); `a^{0∗}` is the unit mass at `0`. -/
noncomputable def seqConvPow (a : ℕ → ℝ≥0∞) (k : ℕ) (n : ℕ) : ℝ≥0∞ :=
  PowerSeries.coeff n (PowerSeries.mk a ^ k)

/-- Coefficients of a power series rebuild it. -/
theorem mk_coeff_eq (φ : PowerSeries ℝ≥0∞) :
    PowerSeries.mk (fun n => PowerSeries.coeff n φ) = φ := by
  ext n
  simp

/-- The generating function of `a ∗ b` is the product of the generating functions. -/
theorem mk_seqConv (a b : ℕ → ℝ≥0∞) :
    PowerSeries.mk (seqConv a b) = PowerSeries.mk a * PowerSeries.mk b := by
  ext n
  rw [PowerSeries.coeff_mk]
  rfl

/-- The generating function of `a^{k∗}` is the `k`-th power of that of `a`. -/
theorem mk_seqConvPow (a : ℕ → ℝ≥0∞) (k : ℕ) :
    PowerSeries.mk (seqConvPow a k) = PowerSeries.mk a ^ k := by
  ext n
  rw [PowerSeries.coeff_mk]
  rfl

/-- `a^{(k+1)∗} = a^{k∗} ∗ a`. -/
theorem seqConvPow_succ (a : ℕ → ℝ≥0∞) (k : ℕ) :
    seqConvPow a (k + 1) = seqConv (seqConvPow a k) a := by
  funext n
  change PowerSeries.coeff n (PowerSeries.mk a ^ (k + 1)) =
    PowerSeries.coeff n (PowerSeries.mk (seqConvPow a k) * PowerSeries.mk a)
  rw [mk_seqConvPow, pow_succ]

/-- One step of the renewal process from an initial law `μ`:
`P(Z₁ = n) = Σ_{j ≤ n} μ(j) p(n − j)`. -/
theorem bind_renewalKernel_singleton (μ : Measure ℕ) (p : Measure ℕ) [SFinite p] (n : ℕ) :
    (μ.bind (renewalKernel p)) {n} = seqConv (fun i => μ {i}) (fun i => p {i}) n := by
  rw [Measure.bind_apply (measurableSet_singleton n) (Kernel.aemeasurable _),
    lintegral_countable', seqConv_eq_sum_range]
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [renewalKernel_apply_singleton,
      ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_comm]
  · intro j hj
    have hj' : ¬ j ≤ n := by
      rw [Finset.mem_range] at hj
      omega
    rw [renewalKernel_apply_singleton, ite_eq_right hj', zero_mul]

/-- **MT, p. 39.** For a delayed renewal process with delay law `a` (the law of `Z₀`) and
increment law `p`, `P(Z_k = n) = a ∗ p^{k∗}(n)`. -/
theorem renewal_law (a : Measure ℕ) (p : Measure ℕ) [IsProbabilityMeasure p] (k n : ℕ) :
    (a.bind (renewalKernel p ^ k)) {n} =
      seqConv (fun i => a {i}) (seqConvPow (fun i => p {i}) k) n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero]
    change (a.bind Kernel.id) {n} = _
    have hid : (⇑(Kernel.id : Kernel ℕ ℕ)) = Measure.dirac := funext Kernel.id_apply
    rw [hid, Measure.bind_dirac]
    change a {n} = PowerSeries.coeff n
      (PowerSeries.mk (fun i => a {i}) * PowerSeries.mk (seqConvPow (fun i => p {i}) 0))
    rw [mk_seqConvPow, pow_zero, mul_one, PowerSeries.coeff_mk]
  | succ k ih =>
    have hstep : a.bind (renewalKernel p ^ (k + 1)) =
        (a.bind (renewalKernel p ^ k)).bind (renewalKernel p) := by
      rw [pow_succ', Measure.bind_bind (Kernel.aemeasurable _) (Kernel.aemeasurable _)]
      rfl
    rw [hstep, bind_renewalKernel_singleton, seqConvPow_succ]
    have hfun : (fun i => (a.bind (renewalKernel p ^ k)) {i}) =
        seqConv (fun i => a {i}) (seqConvPow (fun i => p {i}) k) := funext ih
    rw [hfun]
    change PowerSeries.coeff n (PowerSeries.mk (seqConv (fun i => a {i})
        (seqConvPow (fun i => p {i}) k)) * PowerSeries.mk fun i => p {i}) =
      PowerSeries.coeff n (PowerSeries.mk (fun i => a {i}) *
        PowerSeries.mk (seqConv (seqConvPow (fun i => p {i}) k) fun i => p {i}))
    rw [mk_seqConv, mk_seqConv, mul_assoc]

/-- MT, p. 38: `P(Z₁ = n) = Σ_{j=0}^{n} a(j) p(n − j)`. -/
theorem renewal_law_one (a : Measure ℕ) (p : Measure ℕ) [IsProbabilityMeasure p] (n : ℕ) :
    (a.bind (renewalKernel p)) {n} = ∑ j ∈ Finset.range (n + 1), a {j} * p {n - j} := by
  rw [bind_renewalKernel_singleton, seqConv_eq_sum_range]

/-! ### The forward and backward recurrence time chains -/

/-- The forward recurrence time step: from `k > 1` move to `k − 1`; from `k ≤ 1` (a renewal at
the next time) take a fresh lifetime `y ~ p`. -/
def fwdStep (q : ℕ × ℕ) : ℕ := if 1 < q.1 then q.1 - 1 else q.2

/-- The forward recurrence time (residual lifetime) chain `V⁺` (MT, (RT1), p. 39). -/
noncomputable def forwardKernel (p : Measure ℕ) : Kernel ℕ ℕ := recursionKernel p fwdStep

/-- The forward recurrence time chain is a Markov kernel. -/
theorem isMarkovKernel_forwardKernel (p : Measure ℕ) [IsProbabilityMeasure p] :
    IsMarkovKernel (forwardKernel p) :=
  isMarkovKernel_recursionKernel p (measurable_of_countable _)

/-- MT, p. 39: from `k > 1` the forward recurrence time moves deterministically to `k − 1`. -/
theorem forwardKernel_of_one_lt (p : Measure ℕ) [IsProbabilityMeasure p] {k : ℕ} (hk : 1 < k) :
    forwardKernel p k = Measure.dirac (k - 1) := by
  rw [forwardKernel, recursionKernel_apply p (measurable_of_countable _)]
  have : (fun w => fwdStep (k, w)) = fun _ => k - 1 := by
    funext w
    simp [fwdStep, hk]
  rw [this, Measure.map_const, measure_univ, one_smul]

/-- MT, p. 39: from `1` a renewal occurs and the new forward recurrence time has law `p`. -/
theorem forwardKernel_one (p : Measure ℕ) [SFinite p] : forwardKernel p 1 = p := by
  rw [forwardKernel, recursionKernel_apply p (measurable_of_countable _)]
  have : (fun w => fwdStep (1, w)) = id := by
    funext w
    simp [fwdStep]
  rw [this, Measure.map_id]

/-- The conditional renewal probability (hazard) at age `j`: `p(j + 1)/p(j, ∞)`. -/
noncomputable def hazard (p : Measure ℕ) (j : ℕ) : ℝ≥0∞ := p {j + 1} / p (Ioi j)

/-- The hazard is a probability. -/
theorem hazard_le_one (p : Measure ℕ) (j : ℕ) : hazard p j ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono (by simp))

/-- The backward recurrence time (age) chain `V⁻` (MT, (RT2), p. 39): from age `j` it drops to
`0` with the conditional probability of a renewal and otherwise ages by one. -/
noncomputable def backwardKernel (p : Measure ℕ) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun j =>
    hazard p j • Measure.dirac 0 + (1 - hazard p j) • Measure.dirac (j + 1)

/-- The backward transition law from age `j`. -/
theorem backwardKernel_apply (p : Measure ℕ) (j : ℕ) :
    backwardKernel p j = hazard p j • Measure.dirac 0 + (1 - hazard p j) • Measure.dirac (j + 1) :=
  rfl

/-- The backward recurrence time chain is a Markov kernel. -/
theorem isMarkovKernel_backwardKernel (p : Measure ℕ) : IsMarkovKernel (backwardKernel p) := by
  refine ⟨fun j => ⟨?_⟩⟩
  simp only [backwardKernel_apply, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le (hazard_le_one p j)

/-- From age `j` the chain is renewed with probability `p(j + 1)/p(j, ∞)`. -/
theorem backwardKernel_apply_zero (p : Measure ℕ) (j : ℕ) :
    backwardKernel p j {0} = hazard p j := by
  rw [backwardKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  simp [indicator]

/-- From age `j` the chain ages by one with probability `1 − p(j + 1)/p(j, ∞)`. -/
theorem backwardKernel_apply_succ (p : Measure ℕ) (j : ℕ) :
    backwardKernel p j {j + 1} = 1 - hazard p j := by
  rw [backwardKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  simp [indicator]

/-! ### Pathwise recurrence times -/

/-- The forward recurrence time `V⁺(n) = inf(Zₘ − n : Zₘ > n)` of a sequence of renewal epochs
(MT, (RT1), p. 39). -/
noncomputable def fwdTime (Z : ℕ → ℕ) (n : ℕ) : ℕ := sInf {d | ∃ m, n < Z m ∧ d = Z m - n}

/-- The backward recurrence time `V⁻(n) = inf(n − Zₘ : Zₘ ≤ n)` (MT, (RT2), p. 39). -/
noncomputable def bwdTime (Z : ℕ → ℕ) (n : ℕ) : ℕ := sInf {d | ∃ m, Z m ≤ n ∧ d = n - Z m}

/-- The set in (RT1) is nonempty for a strictly increasing sequence of epochs. -/
theorem fwdTime_set_nonempty {Z : ℕ → ℕ} (hZ : StrictMono Z) (n : ℕ) :
    {d | ∃ m, n < Z m ∧ d = Z m - n}.Nonempty :=
  ⟨Z (n + 1) - n, n + 1, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (hZ.id_le (n + 1)), rfl⟩

/-- `V⁺(n) ≥ 1`. -/
theorem one_le_fwdTime {Z : ℕ → ℕ} (hZ : StrictMono Z) (n : ℕ) : 1 ≤ fwdTime Z n := by
  obtain ⟨m, hm, hd⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ n)
  rw [fwdTime, hd]
  omega

/-- **MT, p. 39.** If `V⁺(n) = k > 1`, then one time unit later `V⁺(n + 1) = k − 1`. -/
theorem fwdTime_succ_of_one_lt {Z : ℕ → ℕ} (hZ : StrictMono Z) {n : ℕ}
    (h : 1 < fwdTime Z n) : fwdTime Z (n + 1) = fwdTime Z n - 1 := by
  have hno : ∀ m, Z m ≠ n + 1 := fun m hm => by
    have := Nat.sInf_le (s := {d | ∃ m, n < Z m ∧ d = Z m - n}) ⟨m, by omega, rfl⟩
    rw [← fwdTime] at this
    omega
  obtain ⟨m₀, hm₀, hd₀⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ n)
  rw [← fwdTime] at hd₀
  apply le_antisymm
  · refine Nat.sInf_le ⟨m₀, ?_, ?_⟩
    · have := hno m₀
      omega
    · omega
  · obtain ⟨m₁, hm₁, hd₁⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ (n + 1))
    rw [← fwdTime] at hd₁
    have := Nat.sInf_le (s := {d | ∃ m, n < Z m ∧ d = Z m - n}) ⟨m₁, by omega, rfl⟩
    rw [← fwdTime] at this
    omega

/-- **MT, p. 39.** If `V⁺(n) = 1`, a renewal occurs at `n + 1`, say `Z_{m₀} = n + 1`, and the new
forward recurrence time is the next lifetime `V⁺(n + 1) = Z_{m₀+1} − Z_{m₀}`. -/
theorem fwdTime_succ_of_eq_one {Z : ℕ → ℕ} (hZ : StrictMono Z) {n : ℕ} (h : fwdTime Z n = 1) :
    ∃ m₀, Z m₀ = n + 1 ∧ fwdTime Z (n + 1) = Z (m₀ + 1) - Z m₀ := by
  obtain ⟨m₀, hm₀, hd₀⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ n)
  rw [← fwdTime, h] at hd₀
  have hZm₀ : Z m₀ = n + 1 := by omega
  refine ⟨m₀, hZm₀, le_antisymm ?_ ?_⟩
  · refine Nat.sInf_le ⟨m₀ + 1, ?_, by rw [hZm₀]⟩
    have := hZ (Nat.lt_add_one m₀)
    omega
  · obtain ⟨m₁, hm₁, hd₁⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ (n + 1))
    rw [← fwdTime] at hd₁
    have hlt : m₀ < m₁ := hZ.lt_iff_lt.mp (by omega)
    have := hZ.monotone (show m₀ + 1 ≤ m₁ by omega)
    omega

/-- **Correction to (RT2).** Before the first renewal the set in (RT2) is empty, so `V⁻(n)` is
undefined for `n < Z₀`; e.g. for the epochs `Zₘ = m + 1` at `n = 0`. -/
theorem bwdTime_set_empty {Z : ℕ → ℕ} (hZ : StrictMono Z) {n : ℕ} (hn : n < Z 0) :
    {d | ∃ m, Z m ≤ n ∧ d = n - Z m} = ∅ := by
  ext d
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
  intro m hm
  have := hZ.monotone (Nat.zero_le m)
  omega

/-- The concrete instance: the epochs `Zₘ = m + 1` have no renewal at or before `n = 0`. -/
theorem bwdTime_set_empty_example : {d | ∃ m, m + 1 ≤ 0 ∧ d = 0 - (m + 1)} = (∅ : Set ℕ) :=
  bwdTime_set_empty (Z := fun m => m + 1) (fun _ _ h => by simpa using h) Nat.one_pos

/-- **MT, p. 39.** At a renewal epoch the age drops to `0`. -/
theorem bwdTime_succ_of_renewal {Z : ℕ → ℕ} {n m : ℕ} (hm : Z m = n + 1) :
    bwdTime Z (n + 1) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨m, hm.le, by omega⟩)

/-- **MT, p. 39.** Between renewals the age increases by one: if `Z₀ ≤ n` and no renewal occurs at
`n + 1`, then `V⁻(n + 1) = V⁻(n) + 1`. -/
theorem bwdTime_succ_of_not_renewal {Z : ℕ → ℕ} {n : ℕ} (h0 : Z 0 ≤ n)
    (hno : ∀ m, Z m ≠ n + 1) : bwdTime Z (n + 1) = bwdTime Z n + 1 := by
  have h1 : {d | ∃ m, Z m ≤ n ∧ d = n - Z m}.Nonempty := ⟨n - Z 0, 0, h0, rfl⟩
  have h2 : {d | ∃ m, Z m ≤ n + 1 ∧ d = n + 1 - Z m}.Nonempty := ⟨n + 1 - Z 0, 0, by omega, rfl⟩
  obtain ⟨m₀, hm₀, hd₀⟩ := Nat.sInf_mem h1
  obtain ⟨m₁, hm₁, hd₁⟩ := Nat.sInf_mem h2
  rw [← bwdTime] at hd₀ hd₁
  apply le_antisymm
  · have := Nat.sInf_le (s := {d | ∃ m, Z m ≤ n + 1 ∧ d = n + 1 - Z m}) ⟨m₀, by omega, rfl⟩
    rw [← bwdTime] at this
    omega
  · have hm₁' : Z m₁ ≤ n := by
      have := hno m₁
      omega
    have := Nat.sInf_le (s := {d | ∃ m, Z m ≤ n ∧ d = n - Z m}) ⟨m₁, hm₁', rfl⟩
    rw [← bwdTime] at this
    omega

/-! ### Continuous time recurrence processes and their skeletons -/

/-- The forward recurrence time process `V⁺(t) = inf(Zₙ − t : Zₙ > t, n ≥ 1)` of a renewal process
in continuous time with epochs `Zₙ` (MT, (RT3), p. 543). -/
noncomputable def fwdTimeCts (Z : ℕ → ℝ) (t : ℝ) : ℝ :=
  sInf {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t}

/-- The backward recurrence time process `V⁻(t) = inf(t − Zₙ : Zₙ ≤ t, n ≥ 1)` (MT, (RT4)). -/
noncomputable def bwdTimeCts (Z : ℕ → ℝ) (t : ℝ) : ℝ :=
  sInf {d | ∃ n, 1 ≤ n ∧ Z n ≤ t ∧ d = t - Z n}

/-- The forward recurrence time `δ`-skeleton `V⁺_δ(n) = V⁺(nδ)` (MT, (RT3)). -/
noncomputable def fwdSkeleton (Z : ℕ → ℝ) (δ : ℝ) (n : ℕ) : ℝ := fwdTimeCts Z (n * δ)

/-- The backward recurrence time `δ`-skeleton `V⁻_δ(n) = V⁻(nδ)` (MT, (RT4)). -/
noncomputable def bwdSkeleton (Z : ℕ → ℝ) (δ : ℝ) (n : ℕ) : ℝ := bwdTimeCts Z (n * δ)

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

namespace MeynTweedie.PseudoAtoms

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

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Poisson counts of exponential services (MT (3.14)–(3.19))

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/PoissonCounts.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

Meyn and Tweedie, §3.3.3, pp. 56–58, cite Çinlar for the fact that the number of exponential
services completed in a time `t` is Poisson with parameter `μt`. This module proves it, and the
mixed Poisson laws of the embedded GI/M/1 and M/G/1 chains that follow.

* `countEvent j t`: exactly `j` of the services `S₁, S₂, …` are completed by `t`.
* `eq_3_18`: **(3.18)**, `P(S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}) = e^{−μt}(μt)ʲ/j!`, by induction
  on `j`, conditioning on the first service (`pi_finSucc_eq_lintegral`, `cons_mem_countEvent`)
  and integrating against the exponential density (`lintegral_poissonCount`). No Erlang law is
  needed.
* `eq_3_14`: **(3.14)/(3.17)**, `p₀ = P(S > T) = ∫ e^{−μt} G(dt)`.
* `eq_3_15`: **(3.15)**, `pⱼ = P(exactly j services in T) = ∫ e^{−μt}(μt)ʲ/j! G(dt)`.
* `eq_3_19`: **(3.19)**, the M/G/1 arrival counts `qⱼ = ∫ e^{−rt}(rt)ʲ/j! H(dt)`.
* The memoryless property (3.17) is `expMeasure_memoryless` in `ModelQueues`.

**Correction.** (3.18) as printed, `P(S₀ + ⋯ + S_{j+1} > t > S₀ + ⋯ + Sⱼ) = e^{−μt}(μt)ʲ/j!`,
counts `j + 1` completed services `S₀, …, Sⱼ`, so the index is off by one: the probability of
exactly one completion by `t` is `μt e^{−μt}`, not `e^{−μt}` (`eq_3_18_counterexample`). The
correct form is `eq_3_18`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

/-- The event that exactly `j` of the i.i.d. service times `S₁, …, S_{j+1}` are completed by
time `t`: `S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}` (coordinates `u₀, …, uⱼ`). -/
def countEvent (j : ℕ) (t : ℝ) : Set (Fin (j + 1) → ℝ) :=
  {u | ∑ i : Fin j, u (Fin.castSucc i) ≤ t ∧ t < ∑ i, u i}

/-- The count event is measurable. -/
theorem measurableSet_countEvent (j : ℕ) (t : ℝ) : MeasurableSet (countEvent j t) := by
  have h1 : Measurable fun u : Fin (j + 1) → ℝ => ∑ i : Fin j, u (Fin.castSucc i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply _
  have h2 : Measurable fun u : Fin (j + 1) → ℝ => ∑ i, u i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply _
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_lt measurable_const h2)

/-- Conditioning on the first service time `s`: exactly `j + 1` completions by `t` means
exactly `j` completions of the remaining services by `t − s`. -/
theorem cons_mem_countEvent (j : ℕ) (t s : ℝ) (v : Fin (j + 1) → ℝ) :
    (Fin.cons s v : Fin (j + 2) → ℝ) ∈ countEvent (j + 1) t ↔ v ∈ countEvent j (t - s) := by
  simp only [countEvent, mem_ofPred_eq]
  rw [Fin.sum_univ_succ, Fin.sum_cons]
  simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- Splitting off the first coordinate of `ν^{⊗(j+1)}`:
`ν^{⊗(j+1)}(E) = ∫ ν^{⊗j}{v : (s, v) ∈ E} ν(ds)`. -/
theorem pi_finSucc_eq_lintegral (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : ℕ)
    {E : Set (Fin (j + 1) → ℝ)} (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin (j + 1) => ν) E =
      ∫⁻ s, (Measure.pi fun _ : Fin j => ν) {v | (Fin.cons s v : Fin (j + 1) → ℝ) ∈ E} ∂ν := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => ν) 0
  rw [← hmp.symm.measure_preimage_equiv, Measure.prod_apply
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => ℝ) 0).symm.measurable hE)]
  refine lintegral_congr fun s => ?_
  congr 1
  ext v
  simp only [mem_preimage, mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero']

/-- The Poisson probability `e^{−μt}(μt)ʲ/j!` for `t ≥ 0`, and `0` for `t < 0`. -/
noncomputable def poissonCount (μ : ℝ) (j : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ici (0 : ℝ)).indicator
    (fun t => exp (-(μ * t)) * (μ * t) ^ j / j.factorial) t)

/-- `t ↦ e^{−μt}(μt)ʲ/j!` (cut off at `0`) is measurable. -/
theorem measurable_poissonCount (μ : ℝ) (j : ℕ) : Measurable (poissonCount μ j) :=
  ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ =>
    exp (-(μ * t)) * (μ * t) ^ j / j.factorial).indicator measurableSet_Ici)

/-- For `t ≥ 0` the cut-off Poisson weight is `e^{−μt}(μt)ʲ/j!`. -/
theorem poissonCount_of_nonneg (μ : ℝ) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    poissonCount μ j t = ENNReal.ofReal (exp (-(μ * t)) * (μ * t) ^ j / j.factorial) := by
  rw [poissonCount, indicator_of_mem (mem_Ici.2 ht)]

/-- For `t < 0` the cut-off Poisson weight is `0`. -/
theorem poissonCount_of_neg (μ : ℝ) (j : ℕ) {t : ℝ} (ht : t < 0) : poissonCount μ j t = 0 := by
  rw [poissonCount, indicator_of_notMem (by simpa using ht), ENNReal.ofReal_zero]

/-- The convolution step behind (3.18): integrating the `j`-count probability at `t − s`
against an exponential first service time gives the `(j + 1)`-count probability,
`∫ e^{−μ(t−s)}(μ(t−s))ʲ/j! μe^{−μs} ds = e^{−μt}(μt)^{j+1}/(j+1)!` over `0 ≤ s ≤ t`. -/
theorem lintegral_poissonCount {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (t : ℝ) :
    ∫⁻ s, poissonCount μ j (t - s) ∂expMeasure μ = poissonCount μ (j + 1) t := by
  have hexp : expMeasure μ = volume.withDensity (exponentialPDF μ) := rfl
  have hpdf : Measurable (exponentialPDF μ) := (measurable_exponentialPDFReal μ).ennreal_ofReal
  rw [hexp, lintegral_withDensity_eq_lintegral_mul _ hpdf
    (g := fun s => poissonCount μ j (t - s))
    ((measurable_poissonCount μ j).comp (measurable_const.sub measurable_id))]
  rcases lt_or_ge t 0 with ht | ht
  · rw [poissonCount_of_neg μ _ ht]
    refine (lintegral_congr fun s => ?_).trans lintegral_zero
    simp only [Pi.mul_apply]
    rcases lt_or_ge s 0 with hs | hs
    · rw [exponentialPDF_of_neg hs, zero_mul]
    · rw [poissonCount_of_neg μ j (by linarith), mul_zero]
  · set F : ℝ → ℝ := fun s => μ ^ (j + 1) * exp (-(μ * t)) * (t - s) ^ j / j.factorial
      with hF
    have hpt : ∀ s, (exponentialPDF μ * fun s => poissonCount μ j (t - s)) s =
        (Icc 0 t).indicator (fun s => ENNReal.ofReal (F s)) s := by
      intro s
      simp only [Pi.mul_apply]
      rcases lt_or_ge s 0 with hs | hs
      · rw [exponentialPDF_of_neg hs, zero_mul, indicator_of_notMem (by simp [hs])]
      · rcases le_or_gt s t with hst | hst
        · rw [exponentialPDF_of_nonneg hs, poissonCount_of_nonneg μ j (by linarith),
            indicator_of_mem (mem_Icc.2 ⟨hs, hst⟩),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have he : exp (-(μ * s)) * exp (-(μ * (t - s))) = exp (-(μ * t)) := by
            rw [← exp_add]
            ring_nf
          rw [hF]
          simp only
          rw [mul_pow, ← he]
          ring
        · rw [poissonCount_of_neg μ j (by linarith), mul_zero,
            indicator_of_notMem (by simp only [mem_Icc, not_and, not_le]; intro; exact hst)]
    have hcont : Continuous F := by
      rw [hF]
      fun_prop
    have hint : IntegrableOn F (Icc 0 t) := hcont.integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 t)] F := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
      have : 0 ≤ t - s := by linarith [hs.2]
      simp only [Pi.zero_apply, hF]
      positivity
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht, poissonCount_of_nonneg μ _ ht]
    congr 1
    have hI : ∫ s in (0 : ℝ)..t, F s =
        μ ^ (j + 1) * exp (-(μ * t)) / j.factorial * ∫ s in (0 : ℝ)..t, (t - s) ^ j := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext s
      rw [hF]
      ring
    rw [hI, intervalIntegral.integral_comp_sub_left (fun x => x ^ j) t, sub_self, sub_zero,
      integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **(3.18)**, MT p. 57 (Çinlar's elementary property of exponential sums). For i.i.d.
exponential services of rate `μ > 0`, the number completed in `[0, t]` is Poisson with parameter
`μt`: `P(S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}) = e^{−μt}(μt)ʲ/j!` (and `0` for `t < 0`). -/
theorem eq_3_18 {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin (j + 1) => expMeasure μ) (countEvent j t) = poissonCount μ j t := by
  have := isProbabilityMeasure_expMeasure hμ
  induction j generalizing t with
  | zero =>
    have hms : MeasurableSet {s : ℝ | 0 ≤ t ∧ t < s} :=
      (MeasurableSet.const (0 ≤ t)).inter (measurableSet_lt measurable_const measurable_id)
    rw [pi_finSucc_eq_lintegral _ 0 (measurableSet_countEvent _ _)]
    have h1 : ∀ s, (Measure.pi fun _ : Fin 0 => expMeasure μ)
        {v | (Fin.cons s v : Fin 1 → ℝ) ∈ countEvent 0 t} =
          {s : ℝ | 0 ≤ t ∧ t < s}.indicator 1 s := by
      intro s
      have hv : ∀ v : Fin 0 → ℝ, (Fin.cons s v : Fin 1 → ℝ) ∈ countEvent 0 t ↔ 0 ≤ t ∧ t < s := by
        intro v
        simp [countEvent]
      by_cases h : 0 ≤ t ∧ t < s
      · rw [indicator_of_mem (show s ∈ {s : ℝ | 0 ≤ t ∧ t < s} from h)]
        convert measure_univ (μ := Measure.pi fun _ : Fin 0 => expMeasure μ)
        ext v
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (hv v).2 h
      · rw [indicator_of_notMem (show s ∉ {s : ℝ | 0 ≤ t ∧ t < s} from h)]
        convert measure_empty (μ := Measure.pi fun _ : Fin 0 => expMeasure μ)
        ext v
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hc => h ((hv v).1 hc)
    simp_rw [h1]
    rw [lintegral_indicator_one hms]
    rcases lt_or_ge t 0 with ht | ht
    · rw [poissonCount_of_neg μ 0 ht]
      convert measure_empty (μ := expMeasure μ)
      ext s
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      linarith
    · rw [poissonCount_of_nonneg μ 0 ht]
      have : {s : ℝ | 0 ≤ t ∧ t < s} = Ioi t := by
        ext s
        simp [ht]
      rw [this, expMeasure_Ioi hμ ht]
      simp
  | succ j ih =>
    rw [pi_finSucc_eq_lintegral _ (j + 1) (measurableSet_countEvent _ _),
      ← lintegral_poissonCount hμ]
    refine lintegral_congr fun s => ?_
    rw [← ih]
    congr 1
    ext v
    exact cons_mem_countEvent j t s v

/-- **(3.15)**, MT p. 56. With interarrival time `T ∼ G` independent of the exponential
services, the probability that exactly `j` services are completed during `T` is
`pⱼ = ∫ e^{−μt}(μt)ʲ/j! G(dt)` (`poissonWeight`). -/
theorem eq_3_15 (G : Measure ℝ≥0) [SFinite G] {μ : ℝ≥0} (hμ : 0 < μ) (j : ℕ) :
    (G.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure μ))
        {p | p.2 ∈ countEvent j p.1} = poissonWeight G μ j := by
  have hm : MeasurableSet {p : ℝ≥0 × (Fin (j + 1) → ℝ) | p.2 ∈ countEvent j p.1} := by
    have h1 : Measurable fun p : ℝ≥0 × (Fin (j + 1) → ℝ) =>
        ∑ i : Fin j, p.2 (Fin.castSucc i) :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).comp measurable_snd
    have h2 : Measurable fun p : ℝ≥0 × (Fin (j + 1) → ℝ) => ∑ i, p.2 i :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).comp measurable_snd
    have h3 : Measurable fun p : ℝ≥0 × (Fin (j + 1) → ℝ) => ((p.1 : ℝ≥0) : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_fst
    exact (measurableSet_le h1 h3).inter (measurableSet_lt h3 h2)
  have := isProbabilityMeasure_expMeasure (by exact_mod_cast hμ : (0 : ℝ) < μ)
  rw [Measure.prod_apply hm, poissonWeight_eq]
  refine lintegral_congr fun t => ?_
  have : Prod.mk t ⁻¹' {p : ℝ≥0 × (Fin (j + 1) → ℝ) | p.2 ∈ countEvent j p.1} =
      countEvent j t := rfl
  rw [this, eq_3_18 (by exact_mod_cast hμ), poissonCount_of_nonneg _ _ t.coe_nonneg, NNReal.coe_mul]

/-- **Correction to (3.18)** (MT p. 57). As printed, the event has `j + 1` completed services
`S₀, …, Sⱼ` but the Poisson weight of `j`. With `j = 0`, `μ = 1`, `t = 2`: the probability that
exactly one service is completed by `t` is `2e^{−2}`, not `e^{−2}`. The correct statement is
`eq_3_18` (sums `S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}`). -/
theorem eq_3_18_counterexample :
    (Measure.pi fun _ : Fin 2 => expMeasure 1) (countEvent 1 2) ≠
      ENNReal.ofReal (exp (-(1 * 2)) * (1 * 2) ^ 0 / (Nat.factorial 0)) := by
  rw [eq_3_18 one_pos, poissonCount_of_nonneg _ _ (by norm_num)]
  have hpos : 0 < exp (-(1 * 2 : ℝ)) := exp_pos _
  rw [Ne, ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  norm_num

/-- **(3.14)** and **(3.17)**, MT pp. 56–57: the probability that the exponential service in
progress outlasts an independent interarrival time `T ∼ G` is
`p₀ = P(S > T) = ∫ e^{−μt} G(dt)`. -/
theorem eq_3_14 (G : Measure ℝ≥0) [SFinite G] {μ : ℝ≥0} (hμ : 0 < μ) :
    (G.prod (expMeasure μ)) {p | (p.1 : ℝ) < p.2} = poissonWeight G μ 0 := by
  have := isProbabilityMeasure_expMeasure (by exact_mod_cast hμ : (0 : ℝ) < μ)
  have hm : MeasurableSet {p : ℝ≥0 × ℝ | (p.1 : ℝ) < p.2} :=
    measurableSet_lt (measurable_coe_nnreal_real.comp measurable_fst) measurable_snd
  rw [Measure.prod_apply hm, poissonWeight_eq]
  refine lintegral_congr fun t => ?_
  have : Prod.mk t ⁻¹' {p : ℝ≥0 × ℝ | (p.1 : ℝ) < p.2} = Ioi (t : ℝ) := rfl
  rw [this, expMeasure_Ioi (by exact_mod_cast hμ) t.coe_nonneg, NNReal.coe_mul]
  simp

/-- **(3.19)**, MT p. 58: in the M/G/1 queue the number of Poisson(`r`) arrivals during a
service time `T ∼ H` is `j` with probability `qⱼ = ∫ e^{−rt}(rt)ʲ/j! H(dt)`. -/
theorem eq_3_19 (H : Measure ℝ≥0) [SFinite H] {r : ℝ≥0} (hr : 0 < r) (j : ℕ) :
    (H.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure r))
        {p | p.2 ∈ countEvent j p.1} = poissonWeight H r j :=
  eq_3_15 H hr j

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Kernels of the specific models (MT §§3.3 and 3.5.1–3.5.3)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/SpecificKernels.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`.

Meyn and Tweedie, §3.5, pp. 67–70, and the derivations left open in §§3.2–3.3. Every model is a
recursion `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)`, so `isMarkovChain_of_iid` (`ModelKernels`) shows it is a Markov
chain with the kernel of `ModelRecursion`; here each kernel is connected to the book's formula.

**§§3.2–3.3 from the recursions** (i.i.d. noise ⇒ Markov):
* `matKernel_rwMatrix`, `randomWalkInt_isMarkovChain`: (3.11), random walk on `ℤ`.
* `matKernel_rwhlMatrix`, `rwhl_isMarkovChain`: (3.12)–(3.14), random walk on `ℤ₊`.
* `matKernel_giM1Matrix`, `proposition_3_3_1_of_recursion`, `proposition_3_3_1_derived`:
  Proposition 3.3.1 (GI/M/1); the `_derived` form takes the service counts from their primitive
  description, using (3.15) from `PoissonCounts`.
* `matKernel_mG1Matrix`, `proposition_3_3_2_of_recursion`, `proposition_3_3_2_derived`:
  Proposition 3.3.2 (M/G/1), with (3.19).
* `matKernel_arMatrix`, `proposition_3_3_3_of_recursion`: Proposition 3.3.3 (AR(1) on `ℚ`);
  `ar1_isMarkovChain`: AR(1) on `ℝ`; `lssMatrix_isMarkovChain`: the linear state space model;
  `waitingTime_isMarkovChain`: the GI/G/1 waiting time (Lindley) chain.

**§3.5.1** Random walk on a half line: `eq_3_35` (3.35), `eq_3_36` (3.36),
`halfLineWalk_isMarkovChain`; on `ℝ`, `randomWalkKernel_apply_image` and
`randomWalkReal_isMarkovChain`.

**§3.5.2** Storage models: `eq_3_37` and `eq_3_37_div` (3.37, corrected), `storage_isMarkovChain`.

**§3.5.3** Renewal processes: `renewalReal_isMarkovChain` (`Zₙ` is a random walk),
`renewalReal_map_eq` (`P(Zₙ ∈ ·) = Γ₀ ∗ Γ^{n∗}`), `eq_3_38` (3.38), `renewalMeasure` and
`renewal_expected_count`, `renewal_expected_count_undelayed` (`U[0, t]` and `Γ₀ ∗ U[0, t]` are
expected numbers of renewals). For the recurrence time processes (RT3)–(RT4), the pathwise
transitions: `fwdTimeCts_add_of_lt` and `fwdSkeleton_succ_of_lt` (`P^δ(x, {x − δ}) = 1` for
`x > δ`), and `bwdTimeCts_add_of_no_renewal` (the backward chain ages by `δ` when no renewal
occurs).

**Corrections.**
* (3.37) has the wrong sign: `∫ G(A/r + y/r) H(dy)` is the law of `J − S`. The increment law is
  `∫ G{t : y − rt ∈ A} H(dy)` (`eq_3_37`); counterexample `eq_3_37_counterexample` (`S = 0`,
  `T = 1`, `r = 1`). This repeats the sign error of the integer storage model on p. 56 (see
  `storage_increment_counterexample`).
* (3.39) has the wrong sign on `δ − x`: `P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)`.
  `eq_3_39_counterexample` uses deterministic renewals of length `1` from `x = 1/4`, `δ = 1/2`,
  where the chain moves surely to `3/4` but the printed formula gives `P^δ(1/4, {3/4}) = 0`.

**See also.** The Markov property of the `δ`-skeletons `V⁺_δ`, `V⁻_δ` for a general increment
law, the kernel (3.39) (`eq_3_39`, which proves `eq_3_39_corrected` is the kernel) and the
backward-chain probabilities of p. 70, with the corrected normalisation, are in
`RenewalSkeletons`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Matrix

/-- (3.11): the matrix `P(x, y) = Γ(y − x)` of §3.3.2 is the kernel of the recursion
`Φₙ₊₁ = Φₙ + Wₙ₊₁` on `ℤ` (`randomWalkKernel`). -/
theorem matKernel_rwMatrix (ν : Measure ℤ) [SFinite ν] :
    matKernel (rwMatrix fun k => ν {k}) = randomWalkKernel ν := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton, randomWalkKernel_apply' ν x (measurableSet_singleton y), rwMatrix]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff]
  omega

/-- (3.12)–(3.14): the matrix of random walk on the half line `ℤ₊` is the kernel of the
recursion `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` (`reflectedWalkKernel`). -/
theorem matKernel_rwhlMatrix (p : Measure ℤ) [SFinite p] :
    matKernel (rwhlMatrix fun k => p {k}) = reflectedWalkKernel p := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [reflectedWalkKernel_apply_zero, ← Measure.tsum_indicator_apply_singleton p _
      measurableSet_Iic]
    simp only [rwhlMatrix, ite_true]
    refine tsum_congr fun k => ?_
    by_cases hk : k ≤ -(x : ℤ) <;> simp [hk]
  · rw [reflectedWalkKernel_apply_pos p x y hy]
    simp [rwhlMatrix, Nat.pos_iff_ne_zero.1 hy]

/-- `q[j + 1, ∞) = Σᵢ q{i + j + 1}` for a measure on `ℕ`. -/
theorem measure_Ici_succ_eq_tsum (q : Measure ℕ) (j : ℕ) :
    q (Ici (j + 1)) = ∑' i, q {i + j + 1} := by
  have h : Ici (j + 1) = ⋃ i : ℕ, ({i + j + 1} : Set ℕ) := by
    ext m
    simp only [mem_Ici, mem_iUnion, mem_singleton_iff]
    constructor
    · intro hm
      exact ⟨m - j - 1, by omega⟩
    · rintro ⟨i, rfl⟩
      omega
  rw [h, measure_iUnion (fun a b hab => Set.disjoint_singleton.2 (by omega))
    (fun _ => measurableSet_singleton _)]

/-- The GI/M/1 matrix of Proposition 3.3.1 with `pⱼ = q{j}` is the kernel of the recursion
`Nₙ₊₁ = [Nₙ + 1 − Dₙ₊₁]⁺` (`giM1Kernel q`), `D` the number of possible service completions
in an interarrival time. -/
theorem matKernel_giM1Matrix (q : Measure ℕ) [SFinite q] :
    matKernel (giM1Matrix fun j => q {j}) = giM1Kernel q := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [giM1Kernel_apply_zero, measure_Ici_succ_eq_tsum]
    simp [giM1Matrix]
  · rw [giM1Kernel_apply' q x]
    by_cases hyx : y ≤ x + 1
    · simp only [giM1Matrix, Nat.pos_iff_ne_zero.1 hy, hyx, ite_true, ite_false]
      congr 1
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff]
      omega
    · simp only [giM1Matrix, Nat.pos_iff_ne_zero.1 hy, hyx, ite_false]
      symm
      convert measure_empty (μ := q)
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
      omega

/-- The M/G/1 matrix of Proposition 3.3.2 with `qⱼ = a{j}` is the kernel of the recursion
`N*ₙ₊₁ = [N*ₙ − 1]⁺ + Aₙ₊₁` (`mG1Kernel a`), `A` the number of arrivals in a service time. -/
theorem matKernel_mG1Matrix (a : Measure ℕ) [SFinite a] :
    matKernel (mG1Matrix fun j => a {j}) = mG1Kernel a := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton, mG1Kernel, recursionKernel_apply' a (measurable_of_countable _) x
    (measurableSet_singleton y)]
  by_cases hx : x = 0
  · subst hx
    simp only [mG1Matrix, ite_true]
    congr 1
    ext d
    simp only [mem_ofPred_eq, mem_singleton_iff, mG1Step]
    omega
  · by_cases hxy : x ≤ y + 1
    · simp only [mG1Matrix, hx, hxy, ite_true, ite_false]
      congr 1
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff, mG1Step]
      omega
    · simp only [mG1Matrix, hx, hxy, ite_false]
      symm
      convert measure_empty (μ := a)
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, mG1Step]
      omega

/-- Proposition 3.3.3: the matrix `P(r, q) = Γ(q − αr)` is the kernel of the AR(1)
recursion `Xₙ₊₁ = αXₙ + Wₙ₊₁` on `ℚ`. -/
theorem matKernel_arMatrix (α : ℚ) (ν : Measure ℚ) [SFinite ν] :
    matKernel (arMatrix α fun q => ν {q}) = recursionKernel ν fun p : ℚ × ℚ => α * p.1 + p.2 := by
  ext1 r
  refine Measure.ext_of_singleton fun q => ?_
  rw [matKernel_singleton, recursionKernel_apply' ν (measurable_of_countable _) r
    (measurableSet_singleton q), arMatrix]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor <;> intro h <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- (3.11) derived from the recursion: if `Φₙ₊₁ = Φₙ + Wₙ₊₁` on `ℤ` with i.i.d. increments
`W ∼ Γ` independent of `Φ₀`, then `Φ` is a Markov chain with matrix `P(x, y) = Γ(y − x)`. -/
theorem randomWalkInt_isMarkovChain (ν μ : Measure ℤ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ W : ℕ → Ω → ℤ}
    (hΦ0 : Measurable (Φ 0)) (hrec : ∀ n ω, Φ (n + 1) ω = Φ n ω + W (n + 1) ω)
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W ν) :
    IsMarkovChain (matKernel (rwMatrix fun k => ν {k})) μ pr Φ := by
  rw [matKernel_rwMatrix]
  exact isMarkovChain_of_iid μ ν measurable_add_step hΦ0 hrec hinit hW

/-- Random walk on the half line `ℤ₊` (3.12)–(3.14) derived from the recursion
`Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` with i.i.d. increments independent of `Φ₀`. -/
theorem rwhl_isMarkovChain (p : Measure ℤ) [IsProbabilityMeasure p] (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ : ℕ → Ω → ℕ}
    {W : ℕ → Ω → ℤ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = ((Φ n ω : ℤ) + W (n + 1) ω).toNat)
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W p) :
    IsMarkovChain (matKernel (rwhlMatrix fun k => p {k})) μ pr Φ := by
  rw [matKernel_rwhlMatrix]
  exact isMarkovChain_of_iid μ p (measurable_of_countable reflectStep) hΦ0 hrec hinit hW

/-- **Proposition 3.3.1** (MT p. 56) derived from the recursion. If the queue length at
arrivals satisfies `Nₙ₊₁ = [Nₙ + 1 − Dₙ₊₁]⁺` where the numbers `Dₙ` of possible service
completions in successive interarrival times are i.i.d. with the mixed Poisson law
`pⱼ = ∫ e^{−rt}(rt)ʲ/j! G(dt)` and independent of `N₀`, then `N` is a Markov chain with the
GI/M/1 matrix. -/
theorem proposition_3_3_1_of_recursion (G : Measure ℝ≥0) (r : ℝ≥0) (q : Measure ℕ)
    [IsProbabilityMeasure q] (hq : ∀ j, q {j} = poissonWeight G r j) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {N D : ℕ → Ω → ℕ}
    (hN0 : Measurable (N 0)) (hrec : ∀ n ω, N (n + 1) ω = N n ω + 1 - D (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hD : IsIIDNoise pr (N 0) D q) :
    IsMarkovChain (matKernel (giM1Matrix (poissonWeight G r))) μ pr N := by
  have h : poissonWeight G r = fun j => q {j} := funext fun j => (hq j).symm
  rw [h, matKernel_giM1Matrix]
  exact isMarkovChain_of_iid μ q (measurable_of_countable giM1Step) hN0 hrec hinit hD

/-- **Proposition 3.3.2** (MT p. 57) derived from the recursion `N*ₙ₊₁ = [N*ₙ − 1]⁺ + Aₙ₊₁`
with i.i.d. arrival counts `A` of mixed Poisson law `qⱼ` (3.19), independent of `N*₀`. -/
theorem proposition_3_3_2_of_recursion (H : Measure ℝ≥0) (r : ℝ≥0) (a : Measure ℕ)
    [IsProbabilityMeasure a] (ha : ∀ j, a {j} = poissonWeight H r j) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {N A : ℕ → Ω → ℕ}
    (hN0 : Measurable (N 0)) (hrec : ∀ n ω, N (n + 1) ω = N n ω - 1 + A (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hA : IsIIDNoise pr (N 0) A a) :
    IsMarkovChain (matKernel (mG1Matrix (poissonWeight H r))) μ pr N := by
  have h : poissonWeight H r = fun j => a {j} := funext fun j => (ha j).symm
  rw [h, matKernel_mG1Matrix]
  exact isMarkovChain_of_iid μ a (measurable_of_countable mG1Step) hN0 hrec hinit hA

/-- **Proposition 3.3.1** from the primitives of the GI/M/1 queue: if `Dₙ` counts the rate-`r`
exponential services completed in an independent interarrival time `T ∼ G` (so its law is
given by `countEvent`), the queue length at arrivals is a Markov chain with the GI/M/1 matrix
with weights (3.15). -/
theorem proposition_3_3_1_derived (G : Measure ℝ≥0) [SFinite G] {r : ℝ≥0} (hr : 0 < r)
    (q : Measure ℕ) [IsProbabilityMeasure q]
    (hq : ∀ j, q {j} = (G.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure r))
      {p | p.2 ∈ countEvent j p.1})
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {N D : ℕ → Ω → ℕ} (hN0 : Measurable (N 0))
    (hrec : ∀ n ω, N (n + 1) ω = N n ω + 1 - D (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hD : IsIIDNoise pr (N 0) D q) :
    IsMarkovChain (matKernel (giM1Matrix (poissonWeight G r))) μ pr N :=
  proposition_3_3_1_of_recursion G r q (fun j => (hq j).trans (eq_3_15 G hr j)) μ hN0 hrec
    hinit hD

/-- **Proposition 3.3.2** from the primitives of the M/G/1 queue: if `Aₙ` counts the
Poisson(`r`) arrivals in an independent service time `∼ H`, the queue length after departures
is a Markov chain with the M/G/1 matrix with weights (3.19). -/
theorem proposition_3_3_2_derived (H : Measure ℝ≥0) [SFinite H] {r : ℝ≥0} (hr : 0 < r)
    (a : Measure ℕ) [IsProbabilityMeasure a]
    (ha : ∀ j, a {j} = (H.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure r))
      {p | p.2 ∈ countEvent j p.1})
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {N A : ℕ → Ω → ℕ} (hN0 : Measurable (N 0))
    (hrec : ∀ n ω, N (n + 1) ω = N n ω - 1 + A (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hA : IsIIDNoise pr (N 0) A a) :
    IsMarkovChain (matKernel (mG1Matrix (poissonWeight H r))) μ pr N :=
  proposition_3_3_2_of_recursion H r a (fun j => (ha j).trans (eq_3_19 H hr j)) μ hN0 hrec
    hinit hA

/-- **Proposition 3.3.3** (MT p. 58) derived from the recursion: if `Xₙ₊₁ = αXₙ + Wₙ₊₁` on
`ℚ` with i.i.d. noise independent of `X₀`, then `X` is a Markov chain with matrix
`P(r, q) = Γ(q − αr)`. -/
theorem proposition_3_3_3_of_recursion (α : ℚ) (ν μ : Measure ℚ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {X W : ℕ → Ω → ℚ}
    (hX0 : Measurable (X 0)) (hrec : ∀ n ω, X (n + 1) ω = α * X n ω + W (n + 1) ω)
    (hinit : pr.map (X 0) = μ) (hW : IsIIDNoise pr (X 0) W ν) :
    IsMarkovChain (matKernel (arMatrix α fun q => ν {q})) μ pr X := by
  rw [matKernel_arMatrix]
  exact isMarkovChain_of_iid μ ν (measurable_of_countable _) hX0 hrec hinit hW

/-- The AR(1) model on `ℝ` (SLM1)–(SLM2): with i.i.d. noise independent of `X₀` it is a Markov
chain with kernel `ar1Kernel` (MT p. 58, "the Markovian nature of the process is immediate"). -/
theorem ar1_isMarkovChain (α : ℝ) (Γ μ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {X W : ℕ → Ω → ℝ}
    (hX0 : Measurable (X 0)) (hrec : ∀ n ω, X (n + 1) ω = α * X n ω + W (n + 1) ω)
    (hinit : pr.map (X 0) = μ) (hW : IsIIDNoise pr (X 0) W Γ) :
    IsMarkovChain (ar1Kernel Γ α) μ pr X :=
  isMarkovChain_of_iid μ Γ (measurable_ar1Step α) hX0 hrec hinit hW

/-- The linear state space model LSS(F, G) on `ℝⁿ` (MT (LSS1)–(LSS2)): `Xₙ₊₁ = FXₙ + GWₙ₊₁`
with i.i.d. noise independent of `X₀` is a Markov chain with kernel `lssMatrixKernel`. -/
theorem lssMatrix_isMarkovChain {n p : ℕ} (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {X : ℕ → Ω → Fin n → ℝ} {W : ℕ → Ω → Fin p → ℝ} (hX0 : Measurable (X 0))
    (hrec : ∀ k ω, X (k + 1) ω = F *ᵥ X k ω + G *ᵥ W (k + 1) ω)
    (hinit : pr.map (X 0) = μ) (hW : IsIIDNoise pr (X 0) W Γ) :
    IsMarkovChain (lssMatrixKernel Γ F G) μ pr X :=
  isMarkovChain_of_iid μ Γ (measurable_lssMatrixStep F G) hX0 hrec hinit hW

/-- The GI/G/1 waiting time chain (Lindley's recursion `Wₙ₊₁ = [Wₙ + Sₙ − Tₙ₊₁]⁺`, the residual
service model of §3.5.2 with `r = 1`): with i.i.d. pairs `(Sₙ, Tₙ₊₁) ∼ H ⊗ G` independent of
`W₀` it is a Markov chain with kernel `waitingTimeKernel`. -/
theorem waitingTime_isMarkovChain (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {pr : Measure Ω}
    [IsProbabilityMeasure pr] {Φ : ℕ → Ω → ℝ≥0} {V : ℕ → Ω → ℝ × ℝ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = Real.toNNReal (Φ n ω + (V (n + 1) ω).1 - (V (n + 1) ω).2))
    (hinit : pr.map (Φ 0) = μ) (hV : IsIIDNoise pr (Φ 0) V (H.prod G)) :
    IsMarkovChain (waitingTimeKernel H G) μ pr Φ :=
  isMarkovChain_of_iid μ (H.prod G) measurable_lindleyStep hΦ0 hrec hinit hV

/-- Random walk on `ℝ`: with i.i.d. increments independent of `Φ₀` it is a Markov chain
with kernel `P(x, A) = Γ(A − x)`. -/
theorem randomWalkReal_isMarkovChain (Γ μ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ W : ℕ → Ω → ℝ}
    (hΦ0 : Measurable (Φ 0)) (hrec : ∀ n ω, Φ (n + 1) ω = Φ n ω + W (n + 1) ω)
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W Γ) :
    IsMarkovChain (randomWalkKernel Γ) μ pr Φ :=
  isMarkovChain_of_iid μ Γ measurable_add_step hΦ0 hrec hinit hW

/-- `P(x, A) = Γ(A − x)` for random walk on `ℝ` (MT pp. 67, 69). -/
theorem randomWalkKernel_apply_image (Γ : Measure ℝ) [SFinite Γ] (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : randomWalkKernel Γ x A = Γ ((fun a => a - x) '' A) := by
  rw [randomWalkKernel_apply' Γ x hA]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨x + w, h, by ring⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

/-- **(3.35)**, MT p. 67: for random walk on the half line `[0, ∞)` and `A ⊆ (0, ∞)`,
`P(x, A) = Γ(A − x)`. -/
theorem eq_3_35 (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) {A : Set ℝ≥0} (hA : MeasurableSet A)
    (h0 : (0 : ℝ≥0) ∉ A) :
    halfLineWalkKernel Γ x A = Γ ((fun a : ℝ≥0 => (a : ℝ) - x) '' A) := by
  rw [halfLineWalkKernel_apply' Γ x hA]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h
    refine ⟨Real.toNNReal (x + w), h, ?_⟩
    have hpos : 0 < (x : ℝ) + w := by
      by_contra hn
      rw [Real.toNNReal_eq_zero.2 (not_lt.1 hn)] at h
      exact h0 h
    rw [Real.coe_toNNReal _ hpos.le]
    ring
  · rintro ⟨a, ha, rfl⟩
    have : (x : ℝ) + ((a : ℝ) - x) = a := by ring
    rwa [this, Real.toNNReal_coe]

/-- **(3.36)**, MT p. 67: `P(x, {0}) = Γ(−∞, −x]`. -/
theorem eq_3_36 (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) :
    halfLineWalkKernel Γ x {0} = Γ (Iic (-(x : ℝ))) :=
  halfLineWalkKernel_apply_zero Γ x

/-- Random walk on the half line `[0, ∞)` (§3.5.1): `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` with i.i.d.
increments independent of `Φ₀` is a Markov chain with kernel (3.35)–(3.36). -/
theorem halfLineWalk_isMarkovChain (Γ : Measure ℝ) (μ : Measure ℝ≥0) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ : ℕ → Ω → ℝ≥0}
    {W : ℕ → Ω → ℝ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = Real.toNNReal (Φ n ω + W (n + 1) ω))
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W Γ) :
    IsMarkovChain (halfLineWalkKernel Γ) μ pr Φ :=
  isMarkovChain_of_iid μ Γ measurable_halfLineStep hΦ0 hrec hinit hW

/-- **(3.37)** corrected, MT p. 68: the increment `S − J = S − rT` of the storage model has
law `Γ(A) = ∫ G{t : y − rt ∈ A} H(dy)`. -/
theorem eq_3_37 (H G : Measure ℝ) [SFinite H] [SFinite G] (r : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ((H.prod G).map fun p => p.1 - r * p.2) A = ∫⁻ y, G {t | y - r * t ∈ A} ∂H := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - r * p.2 :=
    measurable_fst.sub (measurable_const.mul measurable_snd)
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA)]
  rfl

/-- (3.37) corrected, with `r > 0`: `Γ(A) = ∫ G((y − A)/r) H(dy)`. -/
theorem eq_3_37_div (H G : Measure ℝ) [SFinite H] [SFinite G] {r : ℝ} (hr : 0 < r)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ((H.prod G).map fun p => p.1 - r * p.2) A =
      ∫⁻ y, G ((fun a => (y - a) / r) '' A) ∂H := by
  rw [eq_3_37 H G r hA]
  refine lintegral_congr fun y => ?_
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨y - r * t, h, by field_simp; ring⟩
  · rintro ⟨a, ha, rfl⟩
    have : y - r * ((y - a) / r) = a := by field_simp; ring
    rwa [this]

/-- **Correction to (3.37)** (MT p. 68). The printed `Γ(A) = ∫ G(A/r + y/r) H(dy)` is the law
of `J − S`, not `S − J`. With `S = 0`, `T = 1` surely and `r = 1`, `S − J = −1` surely, but the
printed formula gives mass `0` to `{−1}`. -/
theorem eq_3_37_counterexample :
    ((Measure.dirac (0 : ℝ)).prod (Measure.dirac (1 : ℝ))).map (fun p => p.1 - 1 * p.2)
        {-1} ≠
      ∫⁻ y, Measure.dirac (1 : ℝ) {t | 1 * t - y ∈ ({-1} : Set ℝ)} ∂Measure.dirac (0 : ℝ) := by
  rw [eq_3_37 _ _ 1 (measurableSet_singleton _), lintegral_dirac, lintegral_dirac]
  have h1 : {t : ℝ | 0 - 1 * t ∈ ({-1} : Set ℝ)} = {1} := by
    ext t
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  have h2 : {t : ℝ | 1 * t - 0 ∈ ({-1} : Set ℝ)} = {-1} := by
    ext t
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [h1, h2, Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  norm_num

/-- The storage model (§3.5.2): the content `Φₙ₊₁ = [Φₙ + Sₙ − rTₙ₊₁]⁺` with i.i.d. pairs
`(Sₙ, Tₙ₊₁) ∼ H ⊗ G` independent of `Φ₀` is a Markov chain with kernel `storageKernel`, which
is random walk on the half line with increment law (3.37) (`storageKernel_eq_halfLineWalk`). -/
theorem storage_isMarkovChain (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (r : ℝ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {Φ : ℕ → Ω → ℝ≥0} {W : ℕ → Ω → ℝ × ℝ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = Real.toNNReal (Φ n ω + (W (n + 1) ω).1 - r * (W (n + 1) ω).2))
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W (H.prod G)) :
    IsMarkovChain (storageKernel H G r) μ pr Φ :=
  isMarkovChain_of_iid μ (H.prod G) (measurable_storageStep r) hΦ0 hrec hinit hW

/-- The renewal measure `U = Σₙ Γ^{n∗}` (MT p. 69). -/
noncomputable def renewalMeasure (Γ : Measure ℝ) : Measure ℝ := Measure.sum fun n => convPow Γ n

/-- `Γ^{n∗}` is a probability measure. -/
theorem isProbabilityMeasure_convPow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (n : ℕ) :
    IsProbabilityMeasure (convPow Γ n) := by
  unfold convPow
  infer_instance

/-- The renewal measure is s-finite. -/
theorem sFinite_renewalMeasure (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    SFinite (renewalMeasure Γ) := by
  have : ∀ n, SFinite (convPow Γ n) := fun n => by
    have := isProbabilityMeasure_convPow Γ n
    infer_instance
  unfold renewalMeasure
  infer_instance

/-- `(μ ∗ ν)(A) = ∫ ν{y : s + y ∈ A} μ(ds)`. -/
theorem conv_apply_eq_lintegral (μ ν : Measure ℝ) [SFinite ν] {A : Set ℝ} (hA : MeasurableSet A) :
    (μ ∗ ν) A = ∫⁻ s, ν {y | s + y ∈ A} ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add hA, Measure.prod_apply (measurable_add hA)]
  rfl

/-- `A − s = {y : s + y ∈ A}`. -/
theorem image_sub_const_eq_setOf (s : ℝ) (A : Set ℝ) : (fun a => a - s) '' A = {y | s + y ∈ A} := by
  ext y
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨s + y, h, by ring⟩

/-- **(3.38)**, MT p. 68: `Γ₀ ∗ Γ(A) = ∫ Γ(A − s) Γ₀(ds) = ∫ Γ₀(A − s) Γ(ds)`. -/
theorem eq_3_38 (Γ₀ Γ : Measure ℝ) [SFinite Γ₀] [SFinite Γ] {A : Set ℝ}
    (hA : MeasurableSet A) :
    (Γ₀ ∗ Γ) A = ∫⁻ s, Γ ((fun a => a - s) '' A) ∂Γ₀ ∧
      (Γ₀ ∗ Γ) A = ∫⁻ s, Γ₀ ((fun a => a - s) '' A) ∂Γ := by
  simp_rw [image_sub_const_eq_setOf]
  exact ⟨conv_apply_eq_lintegral Γ₀ Γ hA,
    by rw [Measure.conv_comm, conv_apply_eq_lintegral Γ Γ₀ hA]⟩

/-- §3.5.3, MT p. 69: the delayed renewal process `Zₙ = Y₀ + ⋯ + Yₙ` with `Y₀ ∼ Γ₀` and
`Y₁, Y₂, …` i.i.d. `∼ Γ` independent of `Y₀` is a Markov chain with `P(x, A) = Γ(A − x)`. -/
theorem renewalReal_isMarkovChain (Γ Γ₀ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure Γ₀] {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Γ₀) (hY : IsIIDNoise pr (Z 0) Y Γ) :
    IsMarkovChain (randomWalkKernel Γ) Γ₀ pr Z :=
  randomWalkReal_isMarkovChain Γ Γ₀ hZ0 hrec hinit hY

/-- MT p. 68: `P(Zₙ ∈ ·) = Γ₀ ∗ Γ^{n∗}`. -/
theorem renewalReal_map_eq (Γ Γ₀ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure Γ₀] {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Γ₀) (hY : IsIIDNoise pr (Z 0) Y Γ) (n : ℕ) :
    pr.map (Z n) = Γ₀ ∗ convPow Γ n := by
  have := isMarkovKernel_randomWalkKernel Γ
  have := isProbabilityMeasure_convPow Γ n
  rw [(renewalReal_isMarkovChain Γ Γ₀ hZ0 hrec hinit hY).map_eq n]
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), conv_apply_eq_lintegral _ _ hA]
  refine lintegral_congr fun x => ?_
  rw [randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add x) hA]
  rfl

/-- MT p. 69: `E_{Γ₀}[number of renewals in A] = Γ₀ ∗ U(A)`. -/
theorem renewal_expected_count (Γ Γ₀ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure Γ₀] {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Γ₀) (hY : IsIIDNoise pr (Z 0) Y Γ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ ω, ∑' n, A.indicator 1 (Z n ω) ∂pr = (Γ₀ ∗ renewalMeasure Γ) A := by
  have hM := renewalReal_isMarkovChain Γ Γ₀ hZ0 hrec hinit hY
  have hZ : ∀ n, Measurable (Z n) := hM.measurable
  have := sFinite_renewalMeasure Γ
  have : ∀ n, IsProbabilityMeasure (convPow Γ n) := isProbabilityMeasure_convPow Γ
  rw [lintegral_tsum (f := fun n ω => A.indicator 1 (Z n ω))
    fun n => ((measurable_one.indicator hA).comp (hZ n)).aemeasurable]
  have h1 : ∀ n, ∫⁻ ω, A.indicator 1 (Z n ω) ∂pr = (Γ₀ ∗ convPow Γ n) A := fun n => by
    rw [← renewalReal_map_eq Γ Γ₀ hZ0 hrec hinit hY n, Measure.map_apply (hZ n) hA,
      ← lintegral_indicator_one ((hZ n) hA)]
    rfl
  have h2 : ∀ x, renewalMeasure Γ {y | x + y ∈ A} = ∑' n, convPow Γ n {y | x + y ∈ A} :=
    fun x => Measure.sum_apply _ (measurable_const_add x hA)
  simp_rw [h1, conv_apply_eq_lintegral _ _ hA, h2]
  exact (lintegral_tsum (f := fun n s => convPow Γ n {y | s + y ∈ A}) fun n =>
    (measurable_measure_prodMk_left (ν := convPow Γ n) (measurable_add hA)).aemeasurable).symm

/-- MT p. 69: with the first renewal at `0`, `E₀[number of renewals in A] = U(A)`. -/
theorem renewal_expected_count_undelayed (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Measure.dirac 0) (hY : IsIIDNoise pr (Z 0) Y Γ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ ω, ∑' n, A.indicator 1 (Z n ω) ∂pr = renewalMeasure Γ A := by
  have := sFinite_renewalMeasure Γ
  rw [renewal_expected_count Γ _ hZ0 hrec hinit hY hA, Measure.dirac_zero_conv]

/-- The candidates for `V⁺(t + δ)` are those for `V⁺(t)` shifted down by `δ`, when
`V⁺(t) > δ ≥ 0`. -/
theorem fwdTimeCts_set_eq (Z : ℕ → ℝ) {t δ : ℝ} (hδ : 0 ≤ δ) (h : δ < fwdTimeCts Z t) :
    {d | ∃ n, 1 ≤ n ∧ t + δ < Z n ∧ d = Z n - (t + δ)} =
      (fun d => d - δ) '' {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t} := by
  have hbdd : BddBelow {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t} :=
    ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  ext d
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨n, hn, htn, rfl⟩
    exact ⟨Z n - t, ⟨n, hn, by linarith, rfl⟩, by ring⟩
  · rintro ⟨e, ⟨n, hn, htn, rfl⟩, rfl⟩
    have hle : fwdTimeCts Z t ≤ Z n - t := csInf_le hbdd ⟨n, hn, htn, rfl⟩
    exact ⟨n, hn, by linarith, by ring⟩

/-- MT p. 69: if `V⁺(t) > δ ≥ 0` then `V⁺(t + δ) = V⁺(t) − δ`. -/
theorem fwdTimeCts_add_of_lt (Z : ℕ → ℝ) {t δ : ℝ} (hδ : 0 ≤ δ) (h : δ < fwdTimeCts Z t) :
    fwdTimeCts Z (t + δ) = fwdTimeCts Z t - δ := by
  set S := {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t}
  have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hne : S.Nonempty := by
    by_contra hS
    rw [not_nonempty_iff_eq_empty] at hS
    have : fwdTimeCts Z t = 0 := by
      change sInf S = 0
      rw [hS, Real.sInf_empty]
    linarith
  change sInf _ = sInf S - δ
  rw [fwdTimeCts_set_eq Z hδ h]
  exact ((Monotone.map_csInf_of_continuousAt (f := fun d : ℝ => d - δ)
    (continuous_sub_right δ).continuousAt (fun a b hab => by linarith) hne hbdd)).symm

/-- MT p. 69: the forward recurrence `δ`-skeleton moves deterministically from `x > δ` to
`x − δ`, the pathwise content of `P^δ(x, {x − δ}) = 1`. -/
theorem fwdSkeleton_succ_of_lt (Z : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (h : δ < fwdSkeleton Z δ n) : fwdSkeleton Z δ (n + 1) = fwdSkeleton Z δ n - δ := by
  unfold fwdSkeleton at *
  rw [← fwdTimeCts_add_of_lt Z hδ h]
  congr 1
  push_cast
  ring

/-- MT p. 70: if there is no renewal in `(t, t + δ]` then `V⁻(t + δ) = V⁻(t) + δ`. -/
theorem bwdTimeCts_add_of_no_renewal (Z : ℕ → ℝ) {t δ : ℝ} (hδ : 0 ≤ δ)
    (hne : ∃ n, 1 ≤ n ∧ Z n ≤ t) (hno : ∀ n, 1 ≤ n → Z n ≤ t + δ → Z n ≤ t) :
    bwdTimeCts Z (t + δ) = bwdTimeCts Z t + δ := by
  set S := {d | ∃ n, 1 ≤ n ∧ Z n ≤ t ∧ d = t - Z n}
  have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hSne : S.Nonempty := by
    obtain ⟨n, hn, hz⟩ := hne
    exact ⟨_, n, hn, hz, rfl⟩
  have hset : {d | ∃ n, 1 ≤ n ∧ Z n ≤ t + δ ∧ d = t + δ - Z n} = (fun d => d + δ) '' S := by
    ext d
    simp only [mem_ofPred_eq, mem_image, S]
    constructor
    · rintro ⟨n, hn, hz, rfl⟩
      exact ⟨t - Z n, ⟨n, hn, hno n hn hz, rfl⟩, by ring⟩
    · rintro ⟨e, ⟨n, hn, hz, rfl⟩, rfl⟩
      exact ⟨n, hn, by linarith, by ring⟩
  change sInf _ = sInf S + δ
  rw [hset]
  exact ((Monotone.map_csInf_of_continuousAt (f := fun d : ℝ => d + δ)
    (continuous_id.add continuous_const).continuousAt (fun a b hab => by linarith) hSne hbdd)).symm


/-- The product of Dirac masses at `c` is the Dirac mass at the constant tuple. -/
theorem pi_dirac_const (n : ℕ) (c : ℝ) :
    Measure.pi (fun _ : Fin n => Measure.dirac c) = Measure.dirac fun _ => c := by
  refine Measure.pi_eq (μ := fun _ : Fin n => Measure.dirac c) fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  by_cases h : ∀ i, c ∈ s i
  · have h1 : (fun _ : Fin n => c) ∈ univ.pi s := fun i _ => h i
    rw [indicator_of_mem h1]
    exact (Finset.prod_eq_one fun i _ => by rw [indicator_of_mem (h i)]; rfl).symm
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have h1 : (fun _ : Fin n => c) ∉ univ.pi s := fun hm => hi (hm i (mem_univ i))
    rw [indicator_of_notMem h1]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [indicator_of_notMem hi])).symm

/-- `(δ_c)^{n∗} = δ_{nc}`. -/
theorem convPow_dirac (c : ℝ) (n : ℕ) : convPow (Measure.dirac c) n = Measure.dirac (n * c) := by
  rw [convPow, pi_dirac_const, Measure.map_dirac' (measurable_sum_fin (G := ℝ) n)]
  simp

/-- For deterministic renewals of length `1`, the renewal measure on `[0, b]`, `b < 1`, is
the unit mass at `0`. -/
theorem setLIntegral_renewalMeasure_dirac_one {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc 0 b, f t ∂renewalMeasure (Measure.dirac 1) = f 0 := by
  rw [← lintegral_indicator measurableSet_Icc, renewalMeasure, lintegral_sum_measure]
  simp_rw [convPow_dirac, mul_one, lintegral_dirac]
  rw [tsum_eq_single 0 fun n hn => ?_]
  · simp [hb0]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    rw [indicator_of_notMem]
    simp only [mem_Icc, not_and, not_le]
    intro _
    linarith

/-- The right side of (3.39) as printed: `∫_{[0, δ−x]} U(dt) Γ(A − [δ − x] − t)`. -/
noncomputable def eq_3_39_printed (Γ : Measure ℝ) (δ x : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc 0 (δ - x), Γ ((fun a => a - (δ - x) - t) '' A) ∂renewalMeasure Γ

/-- The corrected right side of (3.39): `∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)`. -/
noncomputable def eq_3_39_corrected (Γ : Measure ℝ) (δ x : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc 0 (δ - x), Γ ((fun a => a + (δ - x) - t) '' A) ∂renewalMeasure Γ

/-- **Correction to (3.39)** (MT p. 70). Take deterministic renewals of length `1`
(`Γ = δ₁`), `δ = 1/2` and current forward recurrence time `x = 1/4`. The epochs are
`1/4, 5/4, …`, so `V⁺` moves surely from `1/4` to `3/4`: `P^δ(1/4, {3/4}) = 1`. The printed
formula gives `0` at `{3/4}`; the corrected one gives `1`. -/
theorem eq_3_39_counterexample :
    fwdTimeCts (fun n => (n : ℝ) - 3 / 4) 0 = 1 / 4 ∧
      fwdTimeCts (fun n => (n : ℝ) - 3 / 4) (0 + 1 / 2) = 3 / 4 ∧
      eq_3_39_printed (Measure.dirac 1) (1 / 2) (1 / 4) {3 / 4} = 0 ∧
      eq_3_39_corrected (Measure.dirac 1) (1 / 2) (1 / 4) {3 / 4} = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine IsLeast.csInf_eq ⟨⟨1, le_rfl, by norm_num, by norm_num⟩, ?_⟩
    rintro d ⟨n, hn, -, rfl⟩
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · refine IsLeast.csInf_eq ⟨⟨2, by norm_num, by norm_num, by norm_num⟩, ?_⟩
    rintro d ⟨n, -, hlt, rfl⟩
    have h1 : (1 : ℝ) < n := by linarith
    have h2 : 1 < n := by exact_mod_cast h1
    have : (2 : ℝ) ≤ n := by exact_mod_cast h2
    linarith
  · rw [eq_3_39_printed, setLIntegral_renewalMeasure_dirac_one (by norm_num) (by norm_num),
      image_singleton, Measure.dirac_apply' _ (measurableSet_singleton _)]
    norm_num
  · rw [eq_3_39_corrected, setLIntegral_renewalMeasure_dirac_one (by norm_num) (by norm_num),
      image_singleton, Measure.dirac_apply' _ (measurableSet_singleton _)]
    norm_num

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ladder chains and the GI/G/1 queue (MT §3.5.4)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/LadderChains.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`. The ladder kernel `ladderKernel` is
renamed `ladderChainKernel` here, since `ladderKernel` already names the Chapter 5 counterexample
kernel in `PseudoAtoms`.

Meyn and Tweedie, §3.5.4, pp. 70–71.

* `ladderChainKernel Λ Λ*`: the ladder chain (3.40) on `ℤ₊ × ℝ`, with row `i` putting `Λ*ᵢ(x, ·)` on
  rung `0` and `Λ_{i−j+1}(x, ·)` on rungs `j = 1, …, i + 1`: `eq_3_40_zero`, `eq_3_40_mid`,
  `eq_3_40_up`. It is translation invariant above rung `0` and skip-free to the right
  (`ladderChainKernel_translate`, the matrix display of p. 71), and it is a Markov kernel when every
  row has mass one (`isMarkovKernel_ladderChainKernel`).
* The GI/G/1 kernels: `resEpoch` (the service renewal process started at residual service `x`),
  `ladderP` (3.41), `gig1Lambda` with **(3.42)** (`eq_3_42`), `gig1LambdaStar` with **(3.43)**
  (`eq_3_43`), and the ladder chain `gig1Ladder`. Its row masses are `Σₖ Λₖ(x, ℝ)`
  (`gig1Ladder_rowSum`), so it is Markov when that sum is one (`isMarkovKernel_gig1Ladder`).
  The sum is one when service and interarrival times are nonnegative and services are not
  almost surely zero (`gig1Lambda_tsum_univ`, by the strong law of large numbers applied to the
  truncated services), so `gig1Ladder` is then a Markov kernel
  (`isMarkovKernel_gig1Ladder_of_pos`).

**See also.** That the embedded GI/G/1 process `(Nₙ, Rₙ)` built from the primitives of the
queue is a Markov chain with kernel `gig1Ladder` ("it is easy to verify", p. 71) is
`gig1_isMarkovChain` in `GIG1Embedding`. The book's reference to "(3.41)" for the form of `Φ` on
p. 71 means the ladder structure (3.40).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- Row `i` of the ladder chain (3.40): mass `Λ*ᵢ(x, ·)` on rung `0` and `Λ_{i+1−j}(x, ·)` on
rung `j = 1, …, i + 1` (written with `k = i + 1 − j ∈ {0, …, i}`). -/
noncomputable def ladderRow (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) : Kernel ℝ (ℕ × ℝ) :=
  (Λs i).map (Prod.mk 0) + Kernel.sum fun k : Fin (i + 1) => (Λ k).map (Prod.mk (i + 1 - k))

/-- The ladder chain on `ℤ₊ × ℝ` (MT (3.40), p. 70) built from substochastic kernels
`Λₖ`, `Λ*ᵢ` on `ℝ`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)` for `1 ≤ j ≤ i + 1`,
`P(i, x; 0 × A) = Λ*ᵢ(x, A)` and `0` above rung `i + 1`. -/
noncomputable def ladderChainKernel (Λ Λs : ℕ → Kernel ℝ ℝ) : Kernel (ℕ × ℝ) (ℕ × ℝ) where
  toFun p := ladderRow Λ Λs p.1 p.2
  measurable' := measurable_from_prod_countable_right fun i => (ladderRow Λ Λs i).measurable

/-- The ladder kernel at `(i, x)` is row `i` at `x`. -/
theorem ladderChainKernel_apply (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) :
    ladderChainKernel Λ Λs (i, x) = ladderRow Λ Λs i x := rfl

/-- Placing a kernel on rung `m`: its mass on `{j} × A` is `κ(x, A)` if `j = m`, else `0`. -/
theorem map_prodMk_apply_prod (κ : Kernel ℝ ℝ) (m j : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    κ.map (Prod.mk m) x ({j} ×ˢ A) = if j = m then κ x A else 0 := by
  rw [Kernel.map_apply' _ measurable_prodMk_left x ((measurableSet_singleton j).prod hA)]
  by_cases h : j = m
  · subst h
    simp only [ite_true]
    congr 1
    ext y
    simp
  · simp only [h, ite_false]
    convert measure_empty (μ := κ x)
    ext y
    simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact fun h' => absurd h'.symm h

/-- The mass that row `i` puts on `{j} × A`. -/
theorem ladderRow_apply_prod (Λ Λs : ℕ → Kernel ℝ ℝ) (i j : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ladderRow Λ Λs i x ({j} ×ˢ A) = (if j = 0 then Λs i x A else 0) +
      ∑ k : Fin (i + 1), if j = i + 1 - k then Λ k x A else 0 := by
  rw [ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
    Kernel.sum_apply' _ _ ((measurableSet_singleton j).prod hA), tsum_fintype,
    map_prodMk_apply_prod _ _ _ _ hA]
  simp_rw [map_prodMk_apply_prod _ _ _ _ hA]

/-- (3.40), rung `0`: `P(i, x; 0 × A) = Λ*ᵢ(x, A)`. -/
theorem eq_3_40_zero (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : ladderChainKernel Λ Λs (i, x) ({0} ×ˢ A) = Λs i x A := by
  rw [ladderChainKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [ite_true]
  rw [Finset.sum_eq_zero fun k _ => ?_, add_zero]
  have : (k : ℕ) ≤ i := Nat.lt_succ_iff.1 k.2
  simp only [ite_eq_right_iff]
  intro h
  omega

/-- (3.40), rungs `1, …, i + 1`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)`. -/
theorem eq_3_40_mid (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i + 1) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderChainKernel Λ Λs (i, x) ({j} ×ˢ A) = Λ (i + 1 - j) x A := by
  rw [ladderChainKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [show j ≠ 0 by omega, ite_false, zero_add]
  rw [Finset.sum_eq_single ⟨i + 1 - j, by omega⟩]
  · have h : j = i + 1 - (i + 1 - j) := by omega
    simp [← h]
  · intro k _ hk
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext (by simp only; omega)) hk
  · simp

/-- (3.40), skip-free to the right: `P(i, x; j × A) = 0` for `j > i + 1`. -/
theorem eq_3_40_up (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hji : i + 1 < j) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) : ladderChainKernel Λ Λs (i, x) ({j} ×ˢ A) = 0 := by
  rw [ladderChainKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [show j ≠ 0 by omega, ite_false, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [ite_eq_right_iff]
  intro h
  omega

/-- Translation invariance away from rung `0` (MT p. 71): `P(i + 1, x; (j + 1) × A) =
P(i, x; j × A)` for `j ≥ 1`, as in the matrix display of p. 71. -/
theorem ladderChainKernel_translate (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hj : 1 ≤ j) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderChainKernel Λ Λs (i + 1, x) ({j + 1} ×ˢ A) =
      ladderChainKernel Λ Λs (i, x) ({j} ×ˢ A) := by
  by_cases hji : j ≤ i + 1
  · rw [eq_3_40_mid Λ Λs (by omega) (by omega) x hA, eq_3_40_mid Λ Λs hj hji x hA]
    rw [show i + 1 + 1 - (j + 1) = i + 1 - j by omega]
  · rw [eq_3_40_up Λ Λs (by omega) x hA, eq_3_40_up Λ Λs (by omega) x hA]

/-- The ladder chain is a Markov kernel when each row has total mass one,
`Λ*ᵢ(x, ℝ) + Σ_{k ≤ i} Λₖ(x, ℝ) = 1`. -/
theorem isMarkovKernel_ladderChainKernel (Λ Λs : ℕ → Kernel ℝ ℝ)
    (h : ∀ i x, Λs i x univ + ∑ k ∈ Finset.range (i + 1), Λ k x univ = 1) :
    IsMarkovKernel (ladderChainKernel Λ Λs) := by
  refine ⟨fun p => ⟨?_⟩⟩
  obtain ⟨i, x⟩ := p
  rw [ladderChainKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
    Kernel.sum_apply' _ _ MeasurableSet.univ, tsum_fintype,
    Kernel.map_apply' _ measurable_prodMk_left x MeasurableSet.univ, preimage_univ]
  simp_rw [Kernel.map_apply' _ measurable_prodMk_left x MeasurableSet.univ, preimage_univ]
  rw [← h i x, Fin.sum_univ_eq_sum_range (fun k => Λ k x univ)]

/-- Renewal epochs of the service process started with residual service `x` (MT p. 71):
`Z₀ = 0`, `Z₁ = x` and `Z_{k+1} = x + S₁ + ⋯ + Sₖ`, with service times `uᵢ = S_{i+1}`. -/
def resEpoch (x : ℝ) (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => x + ∑ i ∈ Finset.range k, u i

/-- Each renewal epoch is jointly measurable in `(x, u)`. -/
theorem measurable_resEpoch (k : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch p.1 p.2 k := by
  cases k with
  | zero => exact measurable_const
  | succ k =>
    exact measurable_fst.add (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_snd)

/-- The points `(x, t, u)` at which exactly `n` services are completed in `[0, t]` and the
residual service `R_t = Z_{n+1} − t` lies in `B`. -/
def gig1Set (n : ℕ) (B : Set ℝ) : Set (ℝ × (ℝ × (ℕ → ℝ))) :=
  {q | resEpoch q.1 q.2.2 n ≤ q.2.1 ∧ q.2.1 < resEpoch q.1 q.2.2 (n + 1) ∧
    resEpoch q.1 q.2.2 (n + 1) - q.2.1 ∈ B}

/-- The set `gig1Set n B` is measurable. -/
theorem measurableSet_gig1Set (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet (gig1Set n B) := by
  have hZ : ∀ k, Measurable fun q : ℝ × (ℝ × (ℕ → ℝ)) => resEpoch q.1 q.2.2 k := fun k =>
    (measurable_resEpoch k).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have ht : Measurable fun q : ℝ × (ℝ × (ℕ → ℝ)) => q.2.1 := measurable_fst.comp measurable_snd
  exact (measurableSet_le (hZ n) ht).inter ((measurableSet_lt ht (hZ (n + 1))).inter
    (((hZ (n + 1)).sub ht) hB))

/-- (3.41), MT p. 71: `Pⁿₜ(x, y) = P(Zₙ ≤ t < Z_{n+1}, R_t ≤ y | R₀ = x)`, with i.i.d.
service times of law `H`. -/
noncomputable def ladderP (H : Measure ℝ) (n : ℕ) (t x y : ℝ) : ℝ≥0∞ :=
  Measure.infinitePi (fun _ : ℕ => H)
    {u | resEpoch x u n ≤ t ∧ t < resEpoch x u (n + 1) ∧ resEpoch x u (n + 1) - t ≤ y}

/-- The measure `Λₙ(x, ·)`: `n` service completions during an interarrival time `T ∼ G`,
with the residual service at `T` distributed over `·`. -/
noncomputable def gig1LambdaMeasure (H G : Measure ℝ) (n : ℕ) (x : ℝ) : Measure ℝ :=
  ((G.prod (Measure.infinitePi fun _ : ℕ => H)).restrict
    {p | resEpoch x p.2 n ≤ p.1 ∧ p.1 < resEpoch x p.2 (n + 1)}).map
      fun p => resEpoch x p.2 (n + 1) - p.1

/-- `Λₙ(x, B)` is the `G ⊗ H^{⊗ℕ}` measure of the section of `gig1Set n B` at `x`. -/
theorem gig1LambdaMeasure_apply (H G : Measure ℝ) [IsProbabilityMeasure H] (n : ℕ) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    gig1LambdaMeasure H G n x B =
      (G.prod (Measure.infinitePi fun _ : ℕ => H)) (Prod.mk x ⁻¹' gig1Set n B) := by
  have hZ : ∀ k, Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch x p.2 k := fun k =>
    (measurable_resEpoch k).comp (measurable_const.prodMk measurable_snd)
  have hE : MeasurableSet {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 n ≤ p.1 ∧
      p.1 < resEpoch x p.2 (n + 1)} :=
    (measurableSet_le (hZ n) measurable_fst).inter (measurableSet_lt measurable_fst (hZ (n + 1)))
  have hR : Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch x p.2 (n + 1) - p.1 :=
    (hZ (n + 1)).sub measurable_fst
  rw [gig1LambdaMeasure, Measure.map_apply hR hB, Measure.restrict_apply (hR hB)]
  congr 1
  ext p
  simp only [gig1Set, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  tauto

/-- The GI/G/1 kernel `Λₙ` on `ℝ` (MT (3.42), p. 71). -/
noncomputable def gig1Lambda (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (n : ℕ) :
    Kernel ℝ ℝ where
  toFun := gig1LambdaMeasure H G n
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    simp_rw [gig1LambdaMeasure_apply H G n _ hB]
    exact measurable_measure_prodMk_left (measurableSet_gig1Set n hB)

/-- **(3.42)**, MT p. 71: `Λₙ(x, (−∞, y]) = ∫ Pⁿₜ(x, y) G(dt)`. -/
theorem eq_3_42 (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (n : ℕ) (x y : ℝ) :
    gig1Lambda H G n x (Iic y) = ∫⁻ t, ladderP H n t x y ∂G := by
  change gig1LambdaMeasure H G n x (Iic y) = _
  rw [gig1LambdaMeasure_apply H G n x measurableSet_Iic, Measure.prod_apply
    (measurable_prodMk_left (measurableSet_gig1Set n measurableSet_Iic))]
  rfl

/-- The GI/G/1 kernel `Λ*ₙ` (MT (3.43), p. 71): if more than `n` services are completed
before the next arrival the queue empties and the next service starts afresh with law `H`. -/
noncomputable def gig1LambdaStar (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G]
    (n : ℕ) : Kernel ℝ ℝ where
  toFun x := (∑' j, gig1Lambda H G (j + n + 1) x univ) • H
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (Measurable.tsum fun j => Kernel.measurable_coe _ MeasurableSet.univ).mul_const _

/-- **(3.43)**, MT p. 71: `Λ*ₙ(x, (−∞, y]) = [Σ_{j ≥ n+1} Λⱼ(x, ℝ)] H(−∞, y]`. -/
theorem eq_3_43 (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (n : ℕ) (x y : ℝ) :
    gig1LambdaStar H G n x (Iic y) =
      (∑' j, gig1Lambda H G (j + n + 1) x univ) * H (Iic y) := rfl

/-- The GI/G/1 ladder chain `(Nₙ, Rₙ)` (MT p. 71): the ladder kernel (3.40) with the
kernels (3.42)–(3.43). -/
noncomputable def gig1Ladder (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] :
    Kernel (ℕ × ℝ) (ℕ × ℝ) :=
  ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)

/-- `Σ_{i<k} f(i) + Σᵢ f(i + k) = Σᵢ f(i)` in `ℝ≥0∞`. -/
theorem ennreal_sum_add_tsum_nat_add (f : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑ i ∈ Finset.range k, f i + ∑' i, f (i + k) = ∑' i, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc, ← ih]
    congr 1
    rw [tsum_eq_zero_add' (f := fun i => f (i + k)) ENNReal.summable]
    simp only [zero_add]
    congr 1
    refine tsum_congr fun i => ?_
    congr 1
    omega

/-- Each row of the GI/G/1 ladder chain has mass `Σₖ Λₖ(x, ℝ)`, the probability that the
number of services completed during an interarrival time is finite. -/
theorem gig1Ladder_rowSum (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (i : ℕ)
    (x : ℝ) :
    gig1LambdaStar H G i x univ + ∑ k ∈ Finset.range (i + 1), gig1Lambda H G k x univ =
      ∑' k, gig1Lambda H G k x univ := by
  change (∑' j, gig1Lambda H G (j + i + 1) x univ) • H univ + _ = _
  have h := ennreal_sum_add_tsum_nat_add (fun k => gig1Lambda H G k x univ) (i + 1)
  simp only [← add_assoc] at h
  rw [measure_univ, smul_eq_mul, mul_one, add_comm, h]

/-- The GI/G/1 ladder chain is a Markov kernel when, from every residual service `x`,
only finitely many services fit into an interarrival time almost surely. -/
theorem isMarkovKernel_gig1Ladder (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G]
    (h : ∀ x, ∑' k, gig1Lambda H G k x univ = 1) : IsMarkovKernel (gig1Ladder H G) :=
  isMarkovKernel_ladderChainKernel _ _ fun i x => by rw [gig1Ladder_rowSum, h]

/-- The truncation `w ↦ max(0, min(w, 1))`. -/
noncomputable def clamp01 (w : ℝ) : ℝ := max 0 (min w 1)

/-- The truncation is continuous. -/
theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The truncation lies below a nonnegative argument. -/
theorem clamp01_le {w : ℝ} (hw : 0 ≤ w) : clamp01 w ≤ w :=
  max_le hw (min_le_left _ _)

/-- The truncation is nonnegative. -/
theorem clamp01_nonneg (w : ℝ) : 0 ≤ clamp01 w := le_max_left _ _

/-- The truncation is bounded by `1`. -/
theorem norm_clamp01_le (w : ℝ) : ‖clamp01 w‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [clamp01_nonneg w], max_le zero_le_one (min_le_right _ _)⟩

/-- For i.i.d. service times with `H(−∞, 0) = 0` and `H(0, ∞) > 0`, almost surely all
service times are nonnegative and their partial sums tend to infinity (strong law of large numbers
for the truncations `min(Sᵢ, 1)`). -/
theorem tendsto_partialSum_atTop_ae (H : Measure ℝ) [IsProbabilityMeasure H]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) :
    ∀ᵐ u ∂(Measure.infinitePi fun _ : ℕ => H),
      Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop atTop ∧ ∀ i, 0 ≤ u i := by
  set ν := Measure.infinitePi fun _ : ℕ => H
  set X : ℕ → (ℕ → ℝ) → ℝ := fun i u => clamp01 (u i) with hX
  have hc : Measurable clamp01 := continuous_clamp01.measurable
  have hXm : ∀ i, Measurable (X i) := fun i => hc.comp (measurable_pi_apply i)
  have hind : Pairwise fun i j => IndepFun (X i) (X j) ν := fun i j hij =>
    (iIndepFun_infinitePi (P := fun _ : ℕ => H) (X := fun _ => clamp01) (fun _ => hc)).indepFun
      hij
  have hlaw : ∀ i, ν.map (X i) = H.map clamp01 := fun i => by
    rw [show X i = clamp01 ∘ fun u : ℕ → ℝ => u i from rfl,
      ← Measure.map_map hc (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hident : ∀ i, IdentDistrib (X i) (X 0) ν ν := fun i =>
    ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hint : Integrable (X 0) ν :=
    Integrable.of_bound (hXm 0).aestronglyMeasurable 1 (ae_of_all _ fun u => norm_clamp01_le _)
  have hslln := strong_law_ae X hint hind hident
  have hm : 0 < ∫ u, X 0 u ∂ν := by
    have hmap : ν.map (fun u => u 0) = H := Measure.infinitePi_map_eval _ 0
    have h1 : ∫ u, X 0 u ∂ν = ∫ w, clamp01 w ∂H := by
      rw [show ∫ w, clamp01 w ∂H = ∫ w, clamp01 w ∂(ν.map fun u => u 0) by rw [hmap],
        integral_map (measurable_pi_apply 0).aemeasurable hc.aestronglyMeasurable]
    have hnn0 : 0 ≤ clamp01 := fun w => clamp01_nonneg w
    rw [h1, integral_pos_iff_support_of_nonneg hnn0
      (Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ norm_clamp01_le))]
    refine hHpos.trans_le (measure_mono fun w hw => ?_)
    simp only [Function.mem_support, clamp01, ne_eq]
    have hw' : (0 : ℝ) < w := hw
    exact (lt_max_of_lt_right (lt_min hw' one_pos)).ne'
  have hnn : ∀ᵐ u ∂ν, ∀ i, 0 ≤ u i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {u : ℕ → ℝ | ¬ 0 ≤ u i} = (fun u : ℕ → ℝ => u i) ⁻¹' Iio 0 := by
      ext u
      simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.infinitePi_map_eval, hH0]
  filter_upwards [hslln, hnn] with u h1 h2
  refine ⟨?_, h2⟩
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i u)) atTop
      atTop := tendsto_natCast_atTop_atTop.atTop_mul_pos hm h1
  have h4 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, X i u) atTop atTop := by
    refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ this, one_mul]
  refine tendsto_atTop_mono (fun n => Finset.sum_le_sum fun i _ => clamp01_le (h2 i)) h4

/-- With nonnegative service times the renewal epochs `Z₁ ≤ Z₂ ≤ ⋯` increase. -/
theorem resEpoch_mono {x : ℝ} {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) : resEpoch x u a ≤ resEpoch x u b := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [resEpoch]
  have h : ∑ i ∈ Finset.range a, u i ≤ ∑ i ∈ Finset.range b, u i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun i _ _ => hu i
  linarith

/-- If the epochs increase to infinity, then for `t ≥ 0` exactly one `k` has
`Zₖ ≤ t < Z_{k+1}`. -/
theorem tsum_indicator_resEpoch_eq_one {x t : ℝ} {u : ℕ → ℝ} (ht : 0 ≤ t)
    (hu : ∀ i, 0 ≤ u i) (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop atTop) :
    ∑' k, {v : ℕ → ℝ | resEpoch x v k ≤ t ∧ t < resEpoch x v (k + 1)}.indicator 1 u =
      (1 : ℝ≥0∞) := by
  classical
  have hex : ∃ k, t < resEpoch x u k := by
    obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop (t - x)).exists
    exact ⟨n + 1, by simp only [resEpoch]; linarith⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀pos : k₀ ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hk₀, h] at this
    simp only [resEpoch] at this
    linarith
  have hmin : ∀ m < k₀, resEpoch x u m ≤ t := fun m hm => not_lt.1 (Nat.find_min hex hm)
  have hk₀spec : t < resEpoch x u k₀ := Nat.find_spec hex
  rw [tsum_eq_single (k₀ - 1) fun m hm => ?_]
  · rw [indicator_of_mem]
    · rfl
    · exact ⟨hmin _ (by omega), by rw [show k₀ - 1 + 1 = k₀ by omega]; exact hk₀spec⟩
  · rw [indicator_of_notMem]
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · exact absurd (hmin (m + 1) (by omega)) (not_le.2 h2)
    · have := resEpoch_mono (x := x) hu (show 1 ≤ k₀ by omega) (show k₀ ≤ m by omega)
      linarith

/-- The rows of the GI/G/1 ladder chain have mass one, `Σₖ Λₖ(x, ℝ) = 1`, when service and
interarrival times are nonnegative and services are not almost surely `0`. -/
theorem gig1Lambda_tsum_univ (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0))
    (hG0 : G (Iio 0) = 0) (x : ℝ) : ∑' k, gig1Lambda H G k x univ = 1 := by
  set ν := Measure.infinitePi fun _ : ℕ => H
  set S : ℕ → Set (ℝ × (ℕ → ℝ)) := fun k => Prod.mk x ⁻¹' gig1Set k univ with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    measurable_prodMk_left (measurableSet_gig1Set k MeasurableSet.univ)
  have hk : ∀ k, gig1Lambda H G k x univ = ∫⁻ t, ν (Prod.mk t ⁻¹' S k) ∂G := fun k => by
    change gig1LambdaMeasure H G k x univ = _
    rw [gig1LambdaMeasure_apply H G k x MeasurableSet.univ, Measure.prod_apply (hSm k)]
  simp_rw [hk]
  rw [← lintegral_tsum fun k => (measurable_measure_prodMk_left (hSm k)).aemeasurable]
  have hae : ∀ᵐ t ∂G, ∑' k, ν (Prod.mk t ⁻¹' S k) = 1 := by
    have hG : ∀ᵐ t ∂G, 0 ≤ t := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
        ext a
        simp
      rw [this, hG0]
    filter_upwards [hG] with t ht
    have hsec : ∀ k, Prod.mk t ⁻¹' S k =
        {v : ℕ → ℝ | resEpoch x v k ≤ t ∧ t < resEpoch x v (k + 1)} := fun k => by
      ext v
      simp [hS, gig1Set]
    have hmeas : ∀ k, MeasurableSet
        {v : ℕ → ℝ | resEpoch x v k ≤ t ∧ t < resEpoch x v (k + 1)} := fun k => by
      rw [← hsec]
      exact measurable_prodMk_left (hSm k)
    simp_rw [hsec, ← lintegral_indicator_one (hmeas _)]
    rw [← lintegral_tsum fun k => (measurable_one.indicator (hmeas k)).aemeasurable]
    rw [lintegral_congr_ae ((tendsto_partialSum_atTop_ae H hH0 hHpos).mono fun u hu =>
      tsum_indicator_resEpoch_eq_one ht hu.2 hu.1)]
    simp
  rw [lintegral_congr_ae hae]
  simp

/-- The GI/G/1 ladder chain `gig1Ladder H G` is a Markov kernel when service and interarrival
times are nonnegative and services are not almost surely `0`. -/
theorem isMarkovKernel_gig1Ladder_of_pos (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0))
    (hG0 : G (Iio 0) = 0) : IsMarkovKernel (gig1Ladder H G) :=
  isMarkovKernel_gig1Ladder H G (gig1Lambda_tsum_univ H G hH0 hHpos hG0)

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The forward and backward recurrence time skeletons (MT §3.5.3)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/RenewalSkeletons.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`. The ladder kernel `ladderKernel` is
renamed `ladderChainKernel` here, since `ladderKernel` already names the Chapter 5 counterexample
kernel in `PseudoAtoms`.

Meyn and Tweedie, §3.5.3, pp. 69–70: "no matter what the structure of the renewal sequence", the
`δ`-skeletons `V⁺_δ`, `V⁻_δ` of the forward and backward recurrence time processes are Markov
chains. The proofs regenerate the i.i.d. renewal sequence at the random index of the renewal in
progress at `nδ` (`isMarkovChain_of_regeneration`).

Hypotheses: the increment law `Γ` lives on `[0, ∞)` and is not concentrated at `0`
(`Γ(−∞, 0) = 0`, `Γ(0, ∞) > 0`), so the epochs increase to infinity almost surely, and
`δ ≥ 0`.

**Forward chain.** `fwdSkel δ n = V⁺(nδ)` for the renewal process with first epoch `x` and
increments `y` (law `μ ⊗ Γ^{⊗ℕ}`).
* `fwdSkeleton_isMarkovChain`: a Markov chain with kernel `fwdSkelKernel Γ δ`;
  `fwdSkeleton_isMarkovChain_delayed` (initial law `μ` on `(0, ∞)`) and
  `fwdSkeleton_isMarkovChain_undelayed` (no delay, initial law `Γ`).
* `fwdSkelKernel_of_lt`: `P^δ(x, {x − δ}) = 1` for `x > δ` (MT p. 69).
* `eq_3_39`: **(3.39), corrected**: `P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)` for
  `x ≤ δ`, `A ⊆ (0, ∞)` — `eq_3_39_corrected` of `SpecificKernels`, where
  `eq_3_39_counterexample` shows the printed sign is wrong.

**Backward chain.** `bwdSkel δ n = V⁻(nδ)` for the renewal process with no delay.
* `bwdSkeleton_isMarkovChain`: a Markov chain with kernel `bwdSkelKernel Γ δ` (from age `a`,
  the item in progress has law `Γ` conditioned on `(a, ∞)`) and initial state `0`.
* `bwdSkelKernel_apply_add`: `P(V⁻(nδ) = x + δ | V⁻((n−1)δ) = x) = Γ(x + δ, ∞)/Γ(x, ∞)`.
* `bwdSkelKernel_apply_of_subset`: the second display of p. 70, corrected: for `A ⊆ [0, δ)`,
  `P(V⁻(nδ) ∈ A | x) =
    Γ(x, ∞)⁻¹ ∫_{(x, x+δ]} Γ(du) ∫ U(ds) 1{δ − (u−x) − s ∈ A} Γ(δ − (u−x) − s, ∞)`.

**Corrections.** The backward display of p. 70 divides by `[Γ(x, ∞)]⁻¹`; the correct
normalisation is division by `Γ(x, ∞)` (`bwdSkelKernel_apply_of_subset`); counterexample
`bwd_display_counterexample` (`Γ = ½δ₁ + ½δ₂`, `δ = x = 1`: the true `P(1, {0})` is `1`, the
printed normalisation gives `1/4`). The display also writes `U(dv − (u − x) − δ)`, the
reflection of the correct `U(δ − (u − x) − dv)` (not formalised separately, since the
differential notation is informal).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- `sInf {m | P m} = k` in `ℕ`: either `k` is the least `m` with `P m`, or no `m` has `P m`
and `k = 0`. -/
theorem natSInf_eq_iff (P : ℕ → Prop) (k : ℕ) :
    sInf {m | P m} = k ↔ (P k ∧ ∀ m < k, ¬ P m) ∨ ((∀ m, ¬ P m) ∧ k = 0) := by
  by_cases h : ∃ m, P m
  · have hmem : P (sInf {m | P m}) := Nat.sInf_mem h
    have hmin : ∀ m < sInf {m | P m}, ¬ P m := fun m hm => Nat.notMem_of_lt_sInf hm
    constructor
    · rintro rfl
      exact Or.inl ⟨hmem, hmin⟩
    · rintro (⟨hk, hk'⟩ | ⟨hn, -⟩)
      · refine le_antisymm (Nat.sInf_le hk) ?_
        by_contra hlt
        exact hk' _ (not_le.1 hlt) hmem
      · obtain ⟨m, hm⟩ := h
        exact absurd hm (hn m)
  · push Not at h
    have he : {m | P m} = ∅ := by
      ext m
      simp [h m]
    rw [he, Nat.sInf_empty]
    constructor
    · rintro rfl
      exact Or.inr ⟨h, rfl⟩
    · rintro (⟨hk, -⟩ | ⟨-, rfl⟩)
      · exact absurd hk (h k)
      · rfl

/-- The first index satisfying a measurable condition is a measurable random index. -/
theorem measurableSet_natSInf_eq {Ω : Type*} [MeasurableSpace Ω] {P : Ω → ℕ → Prop}
    (hP : ∀ m, MeasurableSet {ω | P ω m}) (k : ℕ) :
    MeasurableSet {ω | sInf {m | P ω m} = k} := by
  have h : {ω | sInf {m | P ω m} = k} =
      ({ω | P ω k} ∩ ⋂ m, ⋂ (_ : m < k), {ω | P ω m}ᶜ) ∪
        ((⋂ m, {ω | P ω m}ᶜ) ∩ {_ω | k = 0}) := by
    ext ω
    simp only [mem_ofPred_eq, natSInf_eq_iff, mem_union, mem_inter_iff, mem_iInter, mem_compl_iff]
  rw [h]
  exact ((hP k).inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (hP m).compl)).union ((MeasurableSet.iInter fun m => (hP m).compl).inter
      (MeasurableSet.const _))

/-- The forward recurrence time `V⁺(t)` is measurable in the renewal epochs. -/
theorem measurable_fwdTimeCts {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → ℝ}
    (hZ : ∀ k, Measurable fun ω => Z ω k) (t : ℝ) : Measurable fun ω => fwdTimeCts (Z ω) t := by
  refine measurable_of_Iio fun c => ?_
  have h : (fun ω => fwdTimeCts (Z ω) t) ⁻¹' Iio c =
      (⋃ k, {ω | 1 ≤ k ∧ t < Z ω k ∧ Z ω k - t < c}) ∪
        ((⋂ k, {ω | 1 ≤ k → Z ω k ≤ t}) ∩ {_ω | 0 < c}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
    set S := {d | ∃ n, 1 ≤ n ∧ t < Z ω n ∧ d = Z ω n - t}
    have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
    change sInf S < c ↔ _
    by_cases hne : S.Nonempty
    · rw [csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨d, ⟨n, hn, htn, rfl⟩, hd⟩
        exact Or.inl ⟨n, hn, htn, hd⟩
      · rintro (⟨n, hn, htn, hd⟩ | ⟨hall, -⟩)
        · exact ⟨_, ⟨n, hn, htn, rfl⟩, hd⟩
        · obtain ⟨d, n, hn, htn, rfl⟩ := hne
          exact absurd (hall n hn) (not_le.2 htn)
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sInf_empty]
      constructor
      · intro hc
        refine Or.inr ⟨fun n hn => ?_, hc⟩
        by_contra hlt
        have : Z ω n - t ∈ S := ⟨n, hn, not_le.1 hlt, rfl⟩
        rw [hne] at this
        exact this
      · rintro (⟨n, hn, htn, hd⟩ | ⟨-, hc⟩)
        · have : Z ω n - t ∈ S := ⟨n, hn, htn, rfl⟩
          rw [hne] at this
          exact absurd this (notMem_empty _)
        · exact hc
  rw [h]
  refine (MeasurableSet.iUnion fun k => ?_).union ((MeasurableSet.iInter fun k => ?_).inter
    (MeasurableSet.const _))
  · exact (MeasurableSet.const _).inter ((measurableSet_lt measurable_const (hZ k)).inter
      (measurableSet_lt ((hZ k).sub measurable_const) measurable_const))
  · by_cases hk : 1 ≤ k
    · simp only [hk, true_implies]
      exact measurableSet_le (hZ k) measurable_const
    · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

/-- `Z_{m+1} = x + S₁ + ⋯ + Sₘ`. -/
theorem resEpoch_succ_eq (x : ℝ) (w : ℕ → ℝ) (m : ℕ) :
    resEpoch x w (m + 1) = x + ∑ i ∈ Finset.range m, w i := rfl

/-- The first `k + 1` epochs only use the first `k` increments. -/
theorem resEpoch_truncSeq_of_le {x : ℝ} {w : ℕ → ℝ} {k m : ℕ} (hm : m ≤ k + 1) :
    resEpoch x (truncSeq k w) m = resEpoch x w m := by
  cases m with
  | zero => rfl
  | succ m =>
    simp only [resEpoch_succ_eq]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i < k := by simp at hi; omega
    simp [truncSeq, this]

/-- With the increments truncated at `k`, the epochs stop at `Z_{k+1}`. -/
theorem resEpoch_truncSeq_of_ge {x : ℝ} {w : ℕ → ℝ} {k m : ℕ} (hm : k + 1 ≤ m) :
    resEpoch x (truncSeq k w) m = resEpoch x w (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [resEpoch_succ_eq]
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ m by omega)]
  have h0 : ∑ i ∈ Finset.Ico k m, truncSeq k w i = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [truncSeq, (Finset.mem_Ico.1 hi).1]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [truncSeq, Finset.mem_range.1 hi]

/-- If the epoch `Z_{k+1}` lies beyond `t`, then `V⁺(t)` only depends on the first `k`
increments. -/
theorem fwdTimeCts_truncSeq {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {k : ℕ}
    (ht : t < resEpoch x w (k + 1)) :
    fwdTimeCts (resEpoch x (truncSeq k w)) t = fwdTimeCts (resEpoch x w) t := by
  set S1 := {d | ∃ n, 1 ≤ n ∧ t < resEpoch x w n ∧ d = resEpoch x w n - t}
  set S2 := {d | ∃ n, 1 ≤ n ∧ t < resEpoch x (truncSeq k w) n ∧
    d = resEpoch x (truncSeq k w) n - t}
  have hb1 : BddBelow S1 := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hb2 : BddBelow S2 := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hm1 : resEpoch x w (k + 1) - t ∈ S1 := ⟨k + 1, by omega, ht, rfl⟩
  have hm2 : resEpoch x w (k + 1) - t ∈ S2 :=
    ⟨k + 1, by omega, by rwa [resEpoch_truncSeq_of_le le_rfl],
      by rw [resEpoch_truncSeq_of_le le_rfl]⟩
  change sInf S2 = sInf S1
  refine le_antisymm (le_csInf ⟨_, hm1⟩ ?_) (le_csInf ⟨_, hm2⟩ ?_)
  · rintro d ⟨n, hn, htn, rfl⟩
    by_cases hnk : n ≤ k + 1
    · exact csInf_le hb2 ⟨n, hn, by rwa [resEpoch_truncSeq_of_le hnk],
        by rw [resEpoch_truncSeq_of_le hnk]⟩
    · have := resEpoch_mono (x := x) hw (show 1 ≤ k + 1 by omega) (show k + 1 ≤ n by omega)
      exact (csInf_le hb2 hm2).trans (by linarith)
  · rintro d ⟨n, hn, htn, rfl⟩
    by_cases hnk : n ≤ k + 1
    · rw [resEpoch_truncSeq_of_le hnk] at htn ⊢
      exact csInf_le hb1 ⟨n, hn, htn, rfl⟩
    · rw [resEpoch_truncSeq_of_ge (by omega)]
      exact csInf_le hb1 hm1

/-- One step of the forward `δ`-skeleton: the forward recurrence time at `δ` for epochs
`x, x + y₀, x + y₀ + y₁, …`. -/
noncomputable def fwdSkelStep (δ : ℝ) (q : ℝ × (ℕ → ℝ)) : ℝ := fwdTimeCts (resEpoch q.1 q.2) δ

/-- The forward skeleton step is measurable. -/
theorem measurable_fwdSkelStep (δ : ℝ) : Measurable (fwdSkelStep δ) :=
  measurable_fwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2)
    (fun k => measurable_resEpoch k) δ

/-- The transition kernel `P^δ` of the forward recurrence time `δ`-skeleton:
`P^δ(x, A) = Γ^{⊗ℕ}{y : V⁺_δ starting from x, driven by y, lies in A}`. -/
noncomputable def fwdSkelKernel (Γ : Measure ℝ) (δ : ℝ) : Kernel ℝ ℝ :=
  recursionKernel (Measure.infinitePi fun _ : ℕ => Γ) (fwdSkelStep δ)

/-- The forward recurrence time `δ`-skeleton `V⁺_δ(n) = V⁺(nδ)` of the renewal process with
first epoch `x` and increments `y` (MT (RT3), p. 69), on the canonical space. -/
noncomputable def fwdSkel (δ : ℝ) (n : ℕ) (p : ℝ × (ℕ → ℝ)) : ℝ :=
  fwdTimeCts (resEpoch p.1 p.2) (n * δ)

/-- Each `V⁺_δ(n)` is measurable. -/
theorem measurable_fwdSkel (δ : ℝ) (n : ℕ) : Measurable (fwdSkel δ n) :=
  measurable_fwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2)
    (fun k => measurable_resEpoch k) _

/-- The number of increments used up to the first epoch after `nδ`. -/
noncomputable def fwdIndex (δ : ℝ) (n : ℕ) (p : ℝ × (ℕ → ℝ)) : ℕ :=
  sInf {m | (n : ℝ) * δ < resEpoch p.1 p.2 (m + 1)}

/-- The index `fwdIndex` is a measurable random index. -/
theorem measurableSet_fwdIndex_eq (δ : ℝ) (n k : ℕ) :
    MeasurableSet {p : ℝ × (ℕ → ℝ) | fwdIndex δ n p = k} :=
  measurableSet_natSInf_eq
    (P := fun (p : ℝ × (ℕ → ℝ)) m => (n : ℝ) * δ < resEpoch p.1 p.2 (m + 1))
    (fun m => measurableSet_lt measurable_const (measurable_resEpoch (m + 1))) k

/-- If the partial sums diverge, some epoch exceeds any level. -/
theorem exists_resEpoch_gt {x : ℝ} {w : ℕ → ℝ}
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (c : ℝ) :
    ∃ m, c < resEpoch x w (m + 1) := by
  obtain ⟨m, hm⟩ := (hdiv.eventually_gt_atTop (c - x)).exists
  exact ⟨m, by rw [resEpoch_succ_eq]; linarith⟩

/-- With nonnegative increments and divergent epochs, `V⁺(t)` is the first epoch after `t`
minus `t`. -/
theorem fwdTimeCts_eq_resEpoch {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    fwdTimeCts (resEpoch x w) t =
      resEpoch x w (sInf {m | t < resEpoch x w (m + 1)} + 1) - t := by
  have hex := exists_resEpoch_gt (x := x) hdiv t
  set τ := sInf {m | t < resEpoch x w (m + 1)}
  have hτ : t < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  refine IsLeast.csInf_eq ⟨⟨τ + 1, by omega, hτ, rfl⟩, ?_⟩
  rintro d ⟨m, hm, htm, rfl⟩
  have hle : τ ≤ m - 1 := Nat.sInf_le (show t < resEpoch x w (m - 1 + 1) by
    rwa [show m - 1 + 1 = m by omega])
  have := resEpoch_mono (x := x) hw (show 1 ≤ τ + 1 by omega) (show τ + 1 ≤ m by omega)
  linarith

/-- **Regeneration of the forward chain.** `V⁺_δ(n + 1)` is the skeleton step from `V⁺_δ(n)`
driven by the increments after the first epoch beyond `nδ`. -/
theorem fwdSkel_succ {δ : ℝ} (hδ : 0 ≤ δ) {p : ℝ × (ℕ → ℝ)} (hw : ∀ i, 0 ≤ p.2 i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, p.2 i) atTop atTop) (n : ℕ) :
    fwdSkel δ (n + 1) p = fwdSkelStep δ (fwdSkel δ n p, tailSeq (fwdIndex δ n p) p.2) := by
  obtain ⟨x, w⟩ := p
  simp only at hw hdiv
  set τ := fwdIndex δ n (x, w) with hτdef
  have hex := exists_resEpoch_gt (x := x) hdiv ((n : ℝ) * δ)
  have hτ : (n : ℝ) * δ < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, resEpoch x w (m + 1) ≤ (n : ℝ) * δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hW : fwdSkel δ n (x, w) = resEpoch x w (τ + 1) - n * δ :=
    fwdTimeCts_eq_resEpoch hw hdiv
  set W := fwdSkel δ n (x, w) with hWdef
  have htail : ∀ j, resEpoch W (tailSeq τ w) (j + 1) =
      resEpoch x w (τ + 1 + j) - n * δ := fun j => by
    rw [hW, resEpoch_succ_eq, show τ + 1 + j = τ + j + 1 by omega, resEpoch_succ_eq,
      resEpoch_succ_eq, Finset.sum_range_add]
    simp only [tailSeq]
    ring
  rw [show fwdSkel δ (n + 1) (x, w) = fwdTimeCts (resEpoch x w) (((n + 1 : ℕ) : ℝ) * δ)
    from rfl, show fwdSkelStep δ (W, tailSeq τ w) = fwdTimeCts (resEpoch W (tailSeq τ w)) δ
    from rfl]
  unfold fwdTimeCts
  congr 1
  ext d
  simp only [mem_ofPred_eq]
  push_cast
  constructor
  · rintro ⟨m, hm, htm, rfl⟩
    have hmτ : τ + 1 ≤ m := by
      by_contra hlt
      have := hmin (m - 1) (by omega)
      rw [show m - 1 + 1 = m by omega] at this
      nlinarith
    refine ⟨m - τ, by omega, ?_, ?_⟩
    · rw [show m - τ = (m - τ - 1) + 1 by omega, htail,
        show τ + 1 + (m - τ - 1) = m by omega]
      linarith
    · rw [show m - τ = (m - τ - 1) + 1 by omega, htail,
        show τ + 1 + (m - τ - 1) = m by omega]
      ring
  · rintro ⟨j, hj, htj, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [htail] at htj ⊢
    refine ⟨τ + 1 + j, by omega, by linarith, by ring⟩

/-- On `X₀ × ℝ^ℕ` with law `μ ⊗ Γ^{⊗ℕ}`, the pair (initial state, first `k` increments) is
independent of the increments from `k` on, which are again `Γ^{⊗ℕ}`. -/
theorem prod_map_trunc_tail {X₀ : Type*} [MeasurableSpace X₀] (μ : Measure X₀) [SFinite μ]
    (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map
        (fun p => ((p.1, truncSeq k p.2), tailSeq k p.2)) =
      ((μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fun p => (p.1, truncSeq k p.2))).prod
        (Measure.infinitePi fun _ : ℕ => Γ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hAB : Measurable fun w : ℕ → ℝ => (truncSeq k w, tailSeq k w) :=
    (measurable_truncSeq k).prodMk (measurable_tailSeq k)
  have h1 : (μ.prod ν).map (Prod.map id fun w : ℕ → ℝ => (truncSeq k w, tailSeq k w)) =
      μ.prod ((ν.map (truncSeq k)).prod ν) := by
    rw [← Measure.map_prod_map _ _ measurable_id hAB, Measure.map_id, infinitePi_map_trunc_tail]
  have hmp := (measurePreserving_prodAssoc μ (ν.map (truncSeq k)) ν).symm
  have h2 : (fun p : X₀ × (ℕ → ℝ) => ((p.1, truncSeq k p.2), tailSeq k p.2)) =
      (MeasurableEquiv.prodAssoc (α := X₀) (β := ℕ → ℝ) (γ := ℕ → ℝ)).symm ∘
        (Prod.map id fun w : ℕ → ℝ => (truncSeq k w, tailSeq k w)) := by
    funext p
    rfl
  have h3 : (μ.prod ν).map (fun p => (p.1, truncSeq k p.2)) = μ.prod (ν.map (truncSeq k)) := by
    conv_rhs => rw [← Measure.map_id (μ := μ)]
    rw [Measure.map_prod_map _ _ measurable_id (measurable_truncSeq k)]
    rfl
  rw [h2, ← Measure.map_map hmp.measurable (measurable_id.prodMap hAB), h1, hmp.map_eq, h3]

/-- Almost surely the increments are nonnegative and their partial sums diverge. -/
theorem ae_good_prod {X₀ : Type*} [MeasurableSpace X₀] (μ : Measure X₀) [IsProbabilityMeasure μ]
    (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) :
    ∀ᵐ p ∂(μ.prod (Measure.infinitePi fun _ : ℕ => Γ)),
      Tendsto (fun n => ∑ i ∈ Finset.range n, p.2 i) atTop atTop ∧ ∀ i, 0 ≤ p.2 i :=
  (measurePreserving_snd (μ := μ)
    (ν := Measure.infinitePi fun _ : ℕ => Γ)).quasiMeasurePreserving.ae
    (tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos)

/-- **The forward recurrence time `δ`-skeleton is a Markov chain** (MT p. 69), for any
increment law `Γ` on `[0, ∞)` that is not concentrated at `0`, and any delay. Its kernel is
`fwdSkelKernel` (see `eq_3_39` and `fwdSkelKernel_of_lt`). -/
theorem fwdSkeleton_isMarkovChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (fwdSkelKernel Γ δ)
      ((μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fwdSkel δ 0))
      (μ.prod (Measure.infinitePi fun _ : ℕ => Γ)) (fwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hgood := ae_good_prod μ Γ hΓ0 hΓpos
  refine isMarkovChain_of_regeneration (μ.prod ν) ν _ (fwdSkel δ) (measurable_fwdSkel δ) rfl
    (fwdIndex δ) (measurableSet_fwdIndex_eq δ) (fun _ k p => (p.1, truncSeq k p.2))
    (fun _ k => measurable_fst.prodMk ((measurable_truncSeq k).comp measurable_snd))
    (fun _ k p => tailSeq k p.2) (fun _ k => (measurable_tailSeq k).comp measurable_snd)
    (fun _ k => prod_map_trunc_tail μ Γ k) (S := univ) MeasurableSet.univ
    (fun n k => ?_) (measurable_fwdSkelStep δ) (fun n => ?_) _ (fun x => ?_)
  · refine ⟨{b | (n : ℝ) * δ < resEpoch b.1 b.2 (k + 1) ∧
        ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ}, ?_,
      fun b j => fwdTimeCts (resEpoch b.1 b.2) ((j : ℕ) * δ), ?_, ?_⟩
    · have hset : {b : ℝ × (ℕ → ℝ) | ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} =
          ⋂ m, ⋂ (_ : m < k), {b | resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} := by
        ext b
        simp
      have hT2 : MeasurableSet
          {b : ℝ × (ℕ → ℝ) | ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} := by
        rw [hset]
        exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
          measurableSet_le (measurable_resEpoch (m + 1)) measurable_const
      exact (measurableSet_lt measurable_const (measurable_resEpoch (k + 1))).inter hT2
    · exact measurable_pi_iff.2 fun j => measurable_fwdTimeCts
        (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2) (fun k => measurable_resEpoch k) _
    · filter_upwards [hgood] with p ⟨hdiv, hw⟩
      obtain ⟨x, w⟩ := p
      simp only at hdiv hw
      have hex := exists_resEpoch_gt (x := x) hdiv ((n : ℝ) * δ)
      have hiff : fwdIndex δ n (x, w) = k ↔ ((n : ℝ) * δ < resEpoch x w (k + 1) ∧
          ∀ m < k, resEpoch x w (m + 1) ≤ (n : ℝ) * δ) := by
        unfold fwdIndex
        rw [natSInf_eq_iff]
        simp only [not_lt]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · obtain ⟨m, hm⟩ := hex
            exact absurd hm (not_lt.2 (h m))
        · exact Or.inl
      refine ⟨?_, fun hk j => ?_⟩
      · rw [hiff]
        simp only [mem_univ, and_true]
        rw [resEpoch_truncSeq_of_le le_rfl]
        refine and_congr_right fun _ => forall₂_congr fun m hm => ?_
        rw [resEpoch_truncSeq_of_le (by omega)]
      · have hk' := (hiff.1 hk).1
        have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
        have hjn : ((j : ℕ) : ℝ) * δ ≤ (n : ℝ) * δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
        exact (fwdTimeCts_truncSeq hw (lt_of_le_of_lt hjn hk')).symm
  · filter_upwards [hgood] with p ⟨hdiv, hw⟩
    exact fwdSkel_succ hδ hw hdiv n
  · simp only [mem_univ, ofPred_true, cond_univ]
    exact recursionKernel_apply ν (measurable_fwdSkelStep δ) x

/-- Under `Γ^{⊗ℕ}`, the partial sum `S_j = y₀ + ⋯ + y_{j−1}` and the next increment `y_j` are
independent with laws `Γ^{j∗}` and `Γ`. -/
theorem infinitePi_map_partialSum_next (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (j : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun w => (∑ i ∈ Finset.range j, w i, w j)) =
      (convPow Γ j).prod Γ := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hg : Measurable fun u : Fin (j + 1) → ℝ => (Fin.init u, u (Fin.last j)) :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hf : Measurable fun w : ℕ → ℝ => fun i : Fin (j + 1) => w i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hν : ν.map (fun w : ℕ → ℝ => ((fun i : Fin j => w i), w j)) =
      (Measure.pi fun _ : Fin j => Γ).prod Γ := by
    have hc : (fun w : ℕ → ℝ => ((fun i : Fin j => w i), w j)) =
        (fun u : Fin (j + 1) → ℝ => (Fin.init u, u (Fin.last j))) ∘
          (fun w : ℕ → ℝ => fun i : Fin (j + 1) => w i) := by
      funext w
      rfl
    rw [hc, ← Measure.map_map hg hf, infinitePi_map_fin, pi_map_init_last]
  have hs : Measurable fun u : Fin j → ℝ => ∑ i, u i := measurable_sum_fin (G := ℝ) j
  have hc2 : (fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j)) =
      Prod.map (fun u : Fin j → ℝ => ∑ i, u i) id ∘
        (fun w : ℕ → ℝ => ((fun i : Fin j => w i), w j)) := by
    funext w
    simp [Fin.sum_univ_eq_sum_range (fun i => w i)]
  rw [hc2, ← Measure.map_map (hs.prodMap measurable_id)
    ((measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply j)), hν,
    ← Measure.map_prod_map _ _ hs measurable_id, Measure.map_id]
  rfl

/-- MT p. 69: for `x > δ`, `P^δ(x, ·) = δ_{x−δ}`. -/
theorem fwdSkelKernel_of_lt (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : δ < x) :
    fwdSkelKernel Γ δ x = Measure.dirac (x - δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  rw [fwdSkelKernel, recursionKernel_apply ν (measurable_fwdSkelStep δ) x]
  have hae : (fun w => fwdSkelStep δ (x, w)) =ᵐ[ν] fun _ => x - δ := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
    have h0 : fwdTimeCts (resEpoch x w) 0 = x := by
      rw [fwdTimeCts_eq_resEpoch hw hdiv]
      have : sInf {m | (0 : ℝ) < resEpoch x w (m + 1)} = 0 :=
        le_antisymm (Nat.sInf_le (show (0 : ℝ) < resEpoch x w (0 + 1) by
          simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero]
          linarith)) (Nat.zero_le _)
      rw [this]
      simp [resEpoch_succ_eq]
    have := fwdTimeCts_add_of_lt (resEpoch x w) hδ (h0 ▸ hx)
    rw [zero_add, h0] at this
    exact this
  rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]

/-- Decomposing `{V⁺(δ) ∈ A}` over the index `j` of the last epoch before `δ`. -/
theorem indicator_fwdTimeCts_eq_tsum {x δ : ℝ} (hxδ : x ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) {A : Set ℝ}
    (hA0 : A ⊆ Ioi 0) :
    A.indicator (1 : ℝ → ℝ≥0∞) (fwdTimeCts (resEpoch x w) δ) =
      ∑' j, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) := by
  have hex := exists_resEpoch_gt (x := x) hdiv δ
  set τ := sInf {m | δ < resEpoch x w (m + 1)} with hτdef
  have hτ : δ < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, resEpoch x w (m + 1) ≤ δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, resEpoch_succ_eq] at hτ
    simp at hτ
    linarith
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, τ = j₀ + 1 := ⟨τ - 1, by omega⟩
  rw [fwdTimeCts_eq_resEpoch hw hdiv, ← hτdef, tsum_eq_single j₀ fun j hj => ?_]
  · have e : resEpoch x w (τ + 1) - δ = x + ∑ i ∈ Finset.range j₀, w i + w j₀ - δ := by
      rw [hj₀, resEpoch_succ_eq, Finset.sum_range_succ]
      ring
    have h1 : x + ∑ i ∈ Finset.range j₀, w i ≤ δ := by
      have := hmin j₀ (by omega)
      rwa [resEpoch_succ_eq] at this
    rw [e]
    by_cases hA : x + ∑ i ∈ Finset.range j₀, w i + w j₀ - δ ∈ A
    · rw [indicator_of_mem hA, indicator_of_mem (show (∑ i ∈ Finset.range j₀, w i, w j₀) ∈
        {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} from ⟨h1, hA⟩)]
      rfl
    · rw [indicator_of_notMem hA, indicator_of_notMem (show (∑ i ∈ Finset.range j₀, w i, w j₀) ∉
        {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} from fun h => hA h.2)]
  · refine indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have h3 := hmin (j + 1) (by omega)
      rw [resEpoch_succ_eq, Finset.sum_range_succ] at h3
      have := hA0 h2
      simp only [mem_Ioi] at this
      linarith
    · have h3 := resEpoch_mono (x := x) hw (show 1 ≤ τ + 1 by omega)
        (show τ + 1 ≤ j + 1 by omega)
      simp only [resEpoch_succ_eq] at h3 hτ
      simp only at h1
      linarith

/-- `Γ^{j∗}` is concentrated on `[0, ∞)` when `Γ` is. -/
theorem convPow_Iio_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (j : ℕ) : convPow Γ j (Iio 0) = 0 := by
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hm : convPow Γ j = (Measure.infinitePi fun _ : ℕ => Γ).map
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range j, w i) := by
    have := congrArg (Measure.map Prod.fst) (infinitePi_map_partialSum_next Γ j)
    rw [Measure.map_map measurable_fst hpair, Measure.map_fst_prod, measure_univ,
      one_smul] at this
    exact this.symm
  rw [hm, Measure.map_apply (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
    measurableSet_Iio]
  refine measure_mono_null (t := ⋃ i, {w : ℕ → ℝ | w i < 0}) (fun w hw => ?_) ?_
  · by_contra hc
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hc
    simp only [mem_preimage, mem_Iio] at hw
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range j) => hc i
    linarith
  · refine measure_iUnion_null fun i => ?_
    have : {w : ℕ → ℝ | w i < 0} = (fun w : ℕ → ℝ => w i) ⁻¹' Iio 0 := rfl
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.infinitePi_map_eval, hΓ0]

/-- One term of (3.39): the contribution of the `j`-th renewal. -/
theorem lintegral_partialSum_pair (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) {δ x : ℝ} {A : Set ℝ} (hA : MeasurableSet A) (j : ℕ) :
    ∫⁻ w, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) ∂(Measure.infinitePi fun _ : ℕ => Γ) =
      ∫⁻ s in Icc 0 (δ - x), Γ ((fun a => a + (δ - x) - s) '' A) ∂(convPow Γ j) := by
  set E : Set (ℝ × ℝ) := {q | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} with hEdef
  have hE : MeasurableSet E :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_const).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hA)
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hcp := isProbabilityMeasure_convPow Γ j
  have h1 : ∫⁻ w, E.indicator (1 : ℝ × ℝ → ℝ≥0∞) (∑ i ∈ Finset.range j, w i, w j)
      ∂(Measure.infinitePi fun _ : ℕ => Γ) = ((convPow Γ j).prod Γ) E := by
    rw [← infinitePi_map_partialSum_next Γ j, Measure.map_apply hpair hE,
      ← lintegral_indicator_one (hpair hE)]
    rfl
  rw [h1, Measure.prod_apply hE, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr_ae ?_
  have hnn : ∀ᵐ s ∂(convPow Γ j), 0 ≤ s := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
      ext a
      simp
    rw [this, convPow_Iio_zero Γ hΓ0 j]
  filter_upwards [hnn] with s hs
  by_cases hsx : x + s ≤ δ
  · rw [indicator_of_mem (show s ∈ Icc 0 (δ - x) from ⟨hs, by linarith⟩)]
    congr 1
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hEdef, mem_image]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨x + s + y - δ, hy, by ring⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hsx, ?_⟩
      have : x + s + (a + (δ - x) - s) - δ = a := by ring
      rw [this]
      exact ha
  · rw [indicator_of_notMem (show s ∉ Icc 0 (δ - x) from fun h => hsx (by linarith [h.2]))]
    convert measure_empty (μ := Γ)
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hEdef, mem_empty_iff_false, iff_false]
    exact fun h => hsx h.1

/-- **(3.39), corrected** (MT p. 70). For `x ≤ δ` and `A ⊆ (0, ∞)`,
`P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)` (`eq_3_39_corrected`). -/
theorem eq_3_39 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hxδ : x ≤ δ) {A : Set ℝ} (hA : MeasurableSet A)
    (hA0 : A ⊆ Ioi 0) : fwdSkelKernel Γ δ x A = eq_3_39_corrected Γ δ x A := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hE : MeasurableSet {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_const).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hA)
  have hpair : ∀ j, Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) := fun j =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  rw [fwdSkelKernel, recursionKernel_apply' ν (measurable_fwdSkelStep δ) x hA,
    ← lintegral_indicator_one (s := {w | fwdSkelStep δ (x, w) ∈ A})
      (((measurable_fwdSkelStep δ).comp measurable_prodMk_left) hA)]
  have hae : ∀ᵐ w ∂ν, {w | fwdSkelStep δ (x, w) ∈ A}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) w =
      ∑' j, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
    rw [← indicator_fwdTimeCts_eq_tsum hxδ hw hdiv hA0]
    by_cases h : fwdSkelStep δ (x, w) ∈ A
    · rw [indicator_of_mem (show w ∈ {w | fwdSkelStep δ (x, w) ∈ A} from h),
        indicator_of_mem (show fwdTimeCts (resEpoch x w) δ ∈ A from h)]
      rfl
    · rw [indicator_of_notMem (show w ∉ {w | fwdSkelStep δ (x, w) ∈ A} from h),
        indicator_of_notMem (show fwdTimeCts (resEpoch x w) δ ∉ A from h)]
  have hmj : ∀ j, AEMeasurable (fun w : ℕ → ℝ =>
      {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j)) ν := fun j =>
    (Measurable.indicator measurable_one hE |>.comp (hpair j)).aemeasurable
  rw [lintegral_congr_ae hae, lintegral_tsum hmj]
  refine (tsum_congr fun j => lintegral_partialSum_pair Γ hΓ0 hA j).trans ?_
  rw [eq_3_39_corrected, renewalMeasure, ← lintegral_indicator measurableSet_Icc,
    lintegral_sum_measure]
  refine tsum_congr fun j => ?_
  rw [lintegral_indicator measurableSet_Icc]

/-- With a positive first epoch `x`, `V⁺(0) = x`. -/
theorem fwdTimeCts_zero_of_pos {x : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (hx : 0 < x) :
    fwdTimeCts (resEpoch x w) 0 = x := by
  rw [fwdTimeCts_eq_resEpoch hw hdiv]
  have : sInf {m | (0 : ℝ) < resEpoch x w (m + 1)} = 0 :=
    le_antisymm (Nat.sInf_le (show (0 : ℝ) < resEpoch x w (0 + 1) by
      simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero]
      exact hx)) (Nat.zero_le _)
  rw [this]
  simp [resEpoch_succ_eq]

/-- The forward skeleton of the delayed renewal process with delay law `μ` on `(0, ∞)` is a
Markov chain with kernel `P^δ` and initial law `μ`. -/
theorem fwdSkeleton_isMarkovChain_delayed (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iic 0) = 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (fwdSkelKernel Γ δ) μ (μ.prod (Measure.infinitePi fun _ : ℕ => Γ))
      (fwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have h := fwdSkeleton_isMarkovChain Γ hΓ0 hΓpos μ hδ
  have hx : ∀ᵐ p ∂(μ.prod ν), 0 < p.1 :=
    (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae (by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 < a} = Iic 0 := by
        ext a
        simp
      rw [this, hμ])
  have hae : fwdSkel δ 0 =ᵐ[μ.prod ν] Prod.fst := by
    filter_upwards [hx, ae_good_prod μ Γ hΓ0 hΓpos] with p hp ⟨hdiv, hw⟩
    change fwdTimeCts (resEpoch p.1 p.2) (((0 : ℕ) : ℝ) * δ) = p.1
    rw [Nat.cast_zero, zero_mul]
    exact fwdTimeCts_zero_of_pos hw hdiv hp
  rwa [Measure.map_congr hae, Measure.map_fst_prod, measure_univ, one_smul] at h

/-- The forward skeleton of the renewal process with no delay (a renewal at time `0`) is a
Markov chain with kernel `P^δ` and initial law `Γ` (for `Γ` concentrated on `(0, ∞)`). -/
theorem fwdSkeleton_isMarkovChain_undelayed (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iic 0) = 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (fwdSkelKernel Γ δ) Γ
      ((Measure.dirac (0 : ℝ)).prod (Measure.infinitePi fun _ : ℕ => Γ)) (fwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hΓ0' : Γ (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hΓ0
  have hΓpos : 0 < Γ (Ioi 0) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hΓ0, tsub_zero]
    exact one_pos
  have h := fwdSkeleton_isMarkovChain Γ hΓ0' hΓpos (Measure.dirac 0) hδ
  have hpos : ∀ᵐ p ∂((Measure.dirac (0 : ℝ)).prod ν), 0 < p.2 0 ∧ p.1 = 0 := by
    have h1' : ∀ᵐ w ∂ν, 0 < w 0 := by
      rw [ae_iff]
      have : {w : ℕ → ℝ | ¬ 0 < w 0} = (fun w : ℕ → ℝ => w 0) ⁻¹' Iic 0 := by
        ext w
        simp
      rw [this, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Iic,
        Measure.infinitePi_map_eval, hΓ0]
    have h1 : ∀ᵐ p ∂((Measure.dirac (0 : ℝ)).prod ν), 0 < p.2 0 :=
      (measurePreserving_snd (μ := Measure.dirac (0 : ℝ)) (ν := ν)).quasiMeasurePreserving.ae h1'
    have h2 : ∀ᵐ p ∂((Measure.dirac (0 : ℝ)).prod ν), p.1 = 0 :=
      (measurePreserving_fst (μ := Measure.dirac (0 : ℝ)) (ν := ν)).quasiMeasurePreserving.ae
        ((ae_dirac_iff (measurableSet_singleton (0 : ℝ))).2 rfl)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩
  have hae : fwdSkel δ 0 =ᵐ[(Measure.dirac (0 : ℝ)).prod ν] fun p => p.2 0 := by
    filter_upwards [hpos, ae_good_prod (Measure.dirac (0 : ℝ)) Γ hΓ0' hΓpos]
      with p ⟨hp, hp1⟩ ⟨hdiv, hw⟩
    obtain ⟨x, w⟩ := p
    simp only at hp hp1 hdiv hw
    subst hp1
    change fwdTimeCts (resEpoch 0 w) (((0 : ℕ) : ℝ) * δ) = w 0
    rw [Nat.cast_zero, zero_mul, fwdTimeCts_eq_resEpoch hw hdiv]
    have : sInf {m | (0 : ℝ) < resEpoch 0 w (m + 1)} = 1 := by
      rw [natSInf_eq_iff]
      left
      refine ⟨?_, fun m hm => ?_⟩
      · simp [resEpoch_succ_eq, hp]
      · obtain rfl : m = 0 := by omega
        simp [resEpoch_succ_eq]
    rw [this]
    simp [resEpoch_succ_eq]
  have hm : ((Measure.dirac (0 : ℝ)).prod ν).map (fun p => p.2 0) = Γ := by
    rw [show (fun p : ℝ × (ℕ → ℝ) => p.2 0) = (fun w : ℕ → ℝ => w 0) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply 0) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, Measure.infinitePi_map_eval]
  rwa [Measure.map_congr hae, hm] at h

/-- The backward recurrence time `V⁻(t)` is measurable in the renewal epochs. -/
theorem measurable_bwdTimeCts {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → ℝ}
    (hZ : ∀ k, Measurable fun ω => Z ω k) (t : ℝ) : Measurable fun ω => bwdTimeCts (Z ω) t := by
  refine measurable_of_Iio fun c => ?_
  have h : (fun ω => bwdTimeCts (Z ω) t) ⁻¹' Iio c =
      (⋃ k, {ω | 1 ≤ k ∧ Z ω k ≤ t ∧ t - Z ω k < c}) ∪
        ((⋂ k, {ω | 1 ≤ k → t < Z ω k}) ∩ {_ω | 0 < c}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
    set S := {d | ∃ n, 1 ≤ n ∧ Z ω n ≤ t ∧ d = t - Z ω n}
    have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
    change sInf S < c ↔ _
    by_cases hne : S.Nonempty
    · rw [csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨d, ⟨n, hn, htn, rfl⟩, hd⟩
        exact Or.inl ⟨n, hn, htn, hd⟩
      · rintro (⟨n, hn, htn, hd⟩ | ⟨hall, -⟩)
        · exact ⟨_, ⟨n, hn, htn, rfl⟩, hd⟩
        · obtain ⟨d, n, hn, htn, rfl⟩ := hne
          exact absurd (hall n hn) (not_lt.2 htn)
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sInf_empty]
      constructor
      · intro hc
        refine Or.inr ⟨fun n hn => ?_, hc⟩
        by_contra hlt
        have : t - Z ω n ∈ S := ⟨n, hn, not_lt.1 hlt, rfl⟩
        rw [hne] at this
        exact this
      · rintro (⟨n, hn, htn, hd⟩ | ⟨-, hc⟩)
        · have : t - Z ω n ∈ S := ⟨n, hn, htn, rfl⟩
          rw [hne] at this
          exact absurd this (notMem_empty _)
        · exact hc
  rw [h]
  refine (MeasurableSet.iUnion fun k => ?_).union ((MeasurableSet.iInter fun k => ?_).inter
    (MeasurableSet.const _))
  · exact (MeasurableSet.const _).inter ((measurableSet_le (hZ k) measurable_const).inter
      (measurableSet_lt (measurable_const.sub (hZ k)) measurable_const))
  · by_cases hk : 1 ≤ k
    · simp only [hk, true_implies]
      exact measurableSet_lt measurable_const (hZ k)
    · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

/-- If `Z_{k+2}` lies beyond `t`, then `V⁻(t)` only depends on the first `k` increments. -/
theorem bwdTimeCts_truncSeq {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {k : ℕ}
    (ht : t < resEpoch x w (k + 2)) :
    bwdTimeCts (resEpoch x (truncSeq k w)) t = bwdTimeCts (resEpoch x w) t := by
  unfold bwdTimeCts
  congr 1
  ext d
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, htm, rfl⟩
    by_cases hmk : m ≤ k + 1
    · rw [resEpoch_truncSeq_of_le hmk] at htm ⊢
      exact ⟨m, hm, htm, rfl⟩
    · rw [resEpoch_truncSeq_of_ge (by omega)] at htm ⊢
      exact ⟨k + 1, by omega, htm, rfl⟩
  · rintro ⟨m, hm, htm, rfl⟩
    have hmk : m ≤ k + 1 := by
      by_contra hlt
      have := resEpoch_mono (x := x) hw (show 1 ≤ k + 2 by omega) (show k + 2 ≤ m by omega)
      linarith
    exact ⟨m, hm, by rwa [resEpoch_truncSeq_of_le hmk], by rw [resEpoch_truncSeq_of_le hmk]⟩

/-- With nonnegative increments and divergent epochs, `V⁻(t)` is `t` minus the last epoch
before `t`. -/
theorem bwdTimeCts_eq_resEpoch {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (hxt : x ≤ t) :
    bwdTimeCts (resEpoch x w) t = t - resEpoch x w (sInf {m | t < resEpoch x w (m + 1)}) := by
  have hex := exists_resEpoch_gt (x := x) hdiv t
  set τ := sInf {m | t < resEpoch x w (m + 1)}
  have hτ : t < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hτ
    simp [resEpoch_succ_eq] at hτ
    linarith
  have hτle : resEpoch x w τ ≤ t := by
    have := Nat.notMem_of_lt_sInf (s := {m | t < resEpoch x w (m + 1)})
      (show τ - 1 < τ by omega)
    simp only [mem_ofPred_eq, not_lt] at this
    rwa [show τ - 1 + 1 = τ by omega] at this
  refine IsLeast.csInf_eq ⟨⟨τ, by omega, hτle, rfl⟩, ?_⟩
  rintro d ⟨m, hm, hmt, rfl⟩
  have hmτ : m ≤ τ := by
    by_contra hlt
    have := resEpoch_mono (x := x) hw (show 1 ≤ τ + 1 by omega) (show τ + 1 ≤ m by omega)
    linarith
  have := resEpoch_mono (x := x) hw hm hmτ
  linarith

/-- With the increments truncated at `k` and all epochs before `t`, `V⁻(t) = t − Z_{k+1}`. -/
theorem bwdTimeCts_truncSeq_of_le {t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {k : ℕ}
    (h0 : 0 ≤ t) (hle : ∀ m < k, resEpoch 0 w (m + 2) ≤ t) :
    bwdTimeCts (resEpoch 0 (truncSeq k w)) t = t - resEpoch 0 w (k + 1) := by
  have hw' : ∀ i, 0 ≤ truncSeq k w i := fun i => by
    unfold truncSeq
    split_ifs
    · exact hw i
    · exact le_rfl
  have hall : ∀ m, 1 ≤ m → resEpoch 0 (truncSeq k w) m ≤ resEpoch 0 w (k + 1) := fun m hm => by
    by_cases hmk : m ≤ k + 1
    · rw [← resEpoch_truncSeq_of_le (k := k) (le_refl (k + 1))]
      exact resEpoch_mono hw' hm hmk
    · rw [resEpoch_truncSeq_of_ge (by omega)]
  have hk1 : resEpoch 0 w (k + 1) ≤ t := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [resEpoch_succ_eq] using h0
    · have := hle (k - 1) (by omega)
      rwa [show k - 1 + 2 = k + 1 by omega] at this
  refine IsLeast.csInf_eq ⟨⟨k + 1, by omega, by rwa [resEpoch_truncSeq_of_le le_rfl],
    by rw [resEpoch_truncSeq_of_le le_rfl]⟩, ?_⟩
  rintro d ⟨m, hm, hmt, rfl⟩
  have := hall m hm
  linarith

/-- One step of the backward `δ`-skeleton: the age at `δ` when the current item started at
`−a` and has length `y₀`, followed by items `y₁, y₂, …`. -/
noncomputable def bwdSkelStep (δ : ℝ) (q : ℝ × (ℕ → ℝ)) : ℝ :=
  bwdTimeCts (resEpoch (-q.1) q.2) δ

/-- The backward skeleton step is measurable. -/
theorem measurable_bwdSkelStep (δ : ℝ) : Measurable (bwdSkelStep δ) :=
  measurable_bwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch (-q.1) q.2)
    (fun k => (measurable_resEpoch k).comp (measurable_fst.neg.prodMk measurable_snd)) δ

/-- The backward recurrence time `δ`-skeleton `V⁻_δ(n) = V⁻(nδ)` of the renewal process with no
delay (MT (RT4), p. 69), on the canonical space `ℝ^ℕ` of increments. -/
noncomputable def bwdSkel (δ : ℝ) (n : ℕ) (w : ℕ → ℝ) : ℝ :=
  bwdTimeCts (resEpoch 0 w) (n * δ)

/-- Each `V⁻_δ(n)` is measurable. -/
theorem measurable_bwdSkel (δ : ℝ) (n : ℕ) : Measurable (bwdSkel δ n) :=
  measurable_bwdTimeCts (Z := fun w : ℕ → ℝ => resEpoch 0 w)
    (fun k => (measurable_resEpoch k).comp (measurable_const.prodMk measurable_id)) _

/-- The number of complete items before the item in progress at `nδ`. -/
noncomputable def bwdIndex (δ : ℝ) (n : ℕ) (w : ℕ → ℝ) : ℕ :=
  sInf {m | (n : ℝ) * δ < resEpoch 0 w (m + 2)}

/-- The index `bwdIndex` is a measurable random index. -/
theorem measurableSet_bwdIndex_eq (δ : ℝ) (n k : ℕ) :
    MeasurableSet {w : ℕ → ℝ | bwdIndex δ n w = k} :=
  measurableSet_natSInf_eq (P := fun (w : ℕ → ℝ) m => (n : ℝ) * δ < resEpoch 0 w (m + 2))
    (fun m => measurableSet_lt measurable_const
      ((measurable_resEpoch (m + 2)).comp (measurable_const.prodMk measurable_id))) k

/-- The item in progress at `nδ` ends after `nδ`, and the earlier ones end before. -/
theorem bwdIndex_spec {δ : ℝ} (hδ : 0 ≤ δ) {w : ℕ → ℝ} (n : ℕ)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    (n : ℝ) * δ < resEpoch 0 w (bwdIndex δ n w + 2) ∧
      ∀ m < bwdIndex δ n w, resEpoch 0 w (m + 2) ≤ (n : ℝ) * δ := by
  obtain ⟨m, hm⟩ := exists_resEpoch_gt (x := 0) hdiv ((n : ℝ) * δ)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero] at hm
    have : 0 ≤ (n : ℝ) * δ := mul_nonneg n.cast_nonneg hδ
    linarith
  have hex : ∃ m', (n : ℝ) * δ < resEpoch 0 w (m' + 2) :=
    ⟨m - 1, by rwa [show m - 1 + 2 = m + 1 by omega]⟩
  exact ⟨Nat.sInf_mem hex, fun m hm => not_lt.1 (Nat.notMem_of_lt_sInf hm)⟩

/-- `V⁻_δ(n) = nδ − Z_{k+1}`, `k = bwdIndex`. -/
theorem bwdSkel_eq {δ : ℝ} (hδ : 0 ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (n : ℕ) :
    bwdSkel δ n w = (n : ℝ) * δ - resEpoch 0 w (bwdIndex δ n w + 1) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) * δ := mul_nonneg n.cast_nonneg hδ
  obtain ⟨h1, h2⟩ := bwdIndex_spec hδ n hdiv
  unfold bwdSkel
  rw [bwdTimeCts_eq_resEpoch hw hdiv h0]
  congr 2
  rw [natSInf_eq_iff]
  left
  refine ⟨h1, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simpa [resEpoch_succ_eq] using h0
  · have := h2 (m - 1) (by omega)
    rw [show m - 1 + 2 = m + 1 by omega] at this
    exact not_lt.2 this

/-- **Regeneration of the backward chain.** `V⁻_δ(n + 1)` is the skeleton step from
`V⁻_δ(n)` driven by the item in progress and the later items. -/
theorem bwdSkel_succ {δ : ℝ} (hδ : 0 ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (n : ℕ) :
    bwdSkel δ (n + 1) w = bwdSkelStep δ (bwdSkel δ n w, tailSeq (bwdIndex δ n w) w) := by
  set k := bwdIndex δ n w
  obtain ⟨h1, h2⟩ := bwdIndex_spec hδ n hdiv
  have hA := bwdSkel_eq hδ hw hdiv n
  set a := bwdSkel δ n w with hadef
  have hR : ∀ j, resEpoch (-a) (tailSeq k w) (j + 1) = resEpoch 0 w (k + 1 + j) - n * δ :=
    fun j => by
    rw [hA, resEpoch_succ_eq, show k + 1 + j = k + j + 1 by omega, resEpoch_succ_eq,
      resEpoch_succ_eq, Finset.sum_range_add]
    simp only [tailSeq]
    ring
  have hk1 : resEpoch 0 w (k + 1) ≤ (n : ℝ) * δ := by
    have := bwdIndex_spec hδ n hdiv
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h]
      simpa [resEpoch_succ_eq] using mul_nonneg n.cast_nonneg hδ
    · have := h2 (k - 1) (by omega)
      rwa [show k - 1 + 2 = k + 1 by omega] at this
  rw [show bwdSkel δ (n + 1) w = bwdTimeCts (resEpoch 0 w) (((n + 1 : ℕ) : ℝ) * δ) from rfl,
    show bwdSkelStep δ (a, tailSeq k w) = bwdTimeCts (resEpoch (-a) (tailSeq k w)) δ
      from rfl]
  unfold bwdTimeCts
  push_cast
  set SL := {d | ∃ m, 1 ≤ m ∧ resEpoch 0 w m ≤ ((n : ℝ) + 1) * δ ∧
    d = ((n : ℝ) + 1) * δ - resEpoch 0 w m}
  set SR := {d | ∃ j, 1 ≤ j ∧ resEpoch (-a) (tailSeq k w) j ≤ δ ∧
    d = δ - resEpoch (-a) (tailSeq k w) j}
  have hbL : BddBelow SL := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hbR : BddBelow SR := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hmemR : ((n : ℝ) + 1) * δ - resEpoch 0 w (k + 1) ∈ SR :=
    ⟨1, le_rfl, by rw [hR 0]; simp only [add_zero]; nlinarith,
      by rw [hR 0]; simp only [add_zero]; ring⟩
  have hsub : SR ⊆ SL := by
    rintro d ⟨j, hj, hjd, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hR] at hjd ⊢
    exact ⟨k + 1 + j, by omega, by linarith, by ring⟩
  refine le_antisymm (le_csInf ⟨_, hmemR⟩ fun d hd => csInf_le hbL (hsub hd))
    (le_csInf ⟨_, hsub hmemR⟩ ?_)
  rintro d ⟨m, hm, hmd, rfl⟩
  by_cases hmk : k + 1 ≤ m
  · refine csInf_le hbR ⟨m - k, by omega, ?_, ?_⟩
    · rw [show m - k = (m - k - 1) + 1 by omega, hR, show k + 1 + (m - k - 1) = m by omega]
      linarith
    · rw [show m - k = (m - k - 1) + 1 by omega, hR, show k + 1 + (m - k - 1) = m by omega]
      ring
  · have := resEpoch_mono (x := 0) hw hm (show m ≤ k + 1 by omega)
    exact (csInf_le hbR hmemR).trans (by linarith)

/-- The transition kernel of the backward recurrence time `δ`-skeleton: from age `a`, the
length of the item in progress has the law `Γ` conditioned on exceeding `a`. -/
noncomputable def bwdSkelKernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (δ : ℝ) :
    Kernel ℝ ℝ where
  toFun a := ((Measure.infinitePi fun _ : ℕ => Γ)[|{y | a < y 0}]).map
    fun y => bwdSkelStep δ (a, y)
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    have hS : MeasurableSet {q : ℝ × (ℕ → ℝ) | q.1 < q.2 0} :=
      measurableSet_lt measurable_fst ((measurable_pi_apply 0).comp measurable_snd)
    have e : ∀ a, (((Measure.infinitePi fun _ : ℕ => Γ)[|{y | a < y 0}]).map
        fun y => bwdSkelStep δ (a, y)) B =
        ∫⁻ y, B.indicator 1 (bwdSkelStep δ (a, y))
          ∂((Measure.infinitePi fun _ : ℕ => Γ)[|{y | (a, y) ∈
            {q : ℝ × (ℕ → ℝ) | q.1 < q.2 0}}]) := fun a => by
      have hm : Measurable fun y => bwdSkelStep δ (a, y) :=
        (measurable_bwdSkelStep δ).comp measurable_prodMk_left
      rw [Measure.map_apply hm hB, ← lintegral_indicator_one (hm hB)]
      rfl
    simp_rw [e]
    exact measurable_lintegral_cond _ hS
      (g := fun q => B.indicator 1 (bwdSkelStep δ q))
      ((measurable_one.indicator hB).comp (measurable_bwdSkelStep δ))

/-- With a renewal at time `0`, `V⁻(0) = 0` almost surely. -/
theorem bwdSkel_zero_ae (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) (δ : ℝ) :
    bwdSkel δ 0 =ᵐ[Measure.infinitePi fun _ : ℕ => Γ] fun _ => 0 := by
  filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
  unfold bwdSkel
  rw [Nat.cast_zero, zero_mul, bwdTimeCts_eq_resEpoch hw hdiv le_rfl]
  set τ := sInf {m | (0 : ℝ) < resEpoch 0 w (m + 1)}
  have hle : resEpoch 0 w τ ≤ 0 := by
    have hex := exists_resEpoch_gt (x := 0) hdiv 0
    have hτ0 : τ ≠ 0 := by
      intro h0
      have hmem : (0 : ℝ) < resEpoch 0 w (τ + 1) := Nat.sInf_mem hex
      rw [h0] at hmem
      simp [resEpoch_succ_eq] at hmem
    have := Nat.notMem_of_lt_sInf (s := {m | (0 : ℝ) < resEpoch 0 w (m + 1)})
      (show τ - 1 < τ by omega)
    simp only [mem_ofPred_eq, not_lt] at this
    rwa [show τ - 1 + 1 = τ by omega] at this
  have hge : 0 ≤ resEpoch 0 w τ := by
    rcases Nat.eq_zero_or_pos τ with h | h
    · rw [h]
      rfl
    · obtain ⟨t, ht⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
      rw [ht, resEpoch_succ_eq, zero_add]
      exact Finset.sum_nonneg fun i _ => hw i
  linarith

/-- **The backward recurrence time `δ`-skeleton is a Markov chain** (MT p. 69), for any
increment law `Γ` on `[0, ∞)` that is not concentrated at `0`, with kernel `bwdSkelKernel`
and initial state `0`. -/
theorem bwdSkeleton_isMarkovChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (bwdSkelKernel Γ δ) (Measure.dirac 0) (Measure.infinitePi fun _ : ℕ => Γ)
      (bwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hgood := tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos
  have h0 : ν.map (bwdSkel δ 0) = Measure.dirac 0 := by
    rw [Measure.map_congr (bwdSkel_zero_ae Γ hΓ0 hΓpos δ), Measure.map_const, measure_univ,
      one_smul]
  refine isMarkovChain_of_regeneration ν ν _ (bwdSkel δ) (measurable_bwdSkel δ) h0
    (bwdIndex δ) (measurableSet_bwdIndex_eq δ) (fun _ k w => truncSeq k w)
    (fun _ k => measurable_truncSeq k) (fun _ k w => tailSeq k w)
    (fun _ k => measurable_tailSeq k) (fun _ k => infinitePi_map_trunc_tail Γ k)
    (S := {q : ℝ × (ℕ → ℝ) | q.1 < q.2 0})
    (measurableSet_lt measurable_fst ((measurable_pi_apply 0).comp measurable_snd))
    (fun n k => ?_) (measurable_bwdSkelStep δ) (fun n => ?_) _ (fun x => rfl)
  · have hset : {b : ℕ → ℝ | ∀ m < k, resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ} =
        ⋂ m, ⋂ (_ : m < k), {b | resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ} := by
      ext b
      simp
    refine ⟨{b : ℕ → ℝ | ∀ m < k, resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ}, ?_,
      fun b j => bwdTimeCts (resEpoch 0 b) ((j : ℕ) * δ), ?_, ?_⟩
    · rw [hset]
      exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
        measurableSet_le ((measurable_resEpoch (m + 2)).comp
          (measurable_const.prodMk measurable_id)) measurable_const
    · exact measurable_pi_iff.2 fun j => measurable_bwdTimeCts
        (Z := fun w : ℕ → ℝ => resEpoch 0 w)
        (fun k => (measurable_resEpoch k).comp (measurable_const.prodMk measurable_id)) _
    · filter_upwards [hgood] with w ⟨hdiv, hw⟩
      have h0n : (0 : ℝ) ≤ (n : ℝ) * δ := mul_nonneg n.cast_nonneg hδ
      have hex : ∃ m, (n : ℝ) * δ < resEpoch 0 w (m + 2) :=
        ⟨bwdIndex δ n w, (bwdIndex_spec hδ n hdiv).1⟩
      have hiff : bwdIndex δ n w = k ↔ ((n : ℝ) * δ < resEpoch 0 w (k + 2) ∧
          ∀ m < k, resEpoch 0 w (m + 2) ≤ (n : ℝ) * δ) := by
        unfold bwdIndex
        rw [natSInf_eq_iff]
        simp only [not_lt]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · obtain ⟨m, hm⟩ := hex
            exact absurd hm (not_lt.2 (h m))
        · exact Or.inl
      have hT : (truncSeq k w ∈ {b : ℕ → ℝ | ∀ m < k, resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ}) ↔
          ∀ m < k, resEpoch 0 w (m + 2) ≤ (n : ℝ) * δ := by
        simp only [mem_ofPred_eq]
        exact forall₂_congr fun m hm => by rw [resEpoch_truncSeq_of_le (by omega)]
      refine ⟨?_, fun hk j => ?_⟩
      · rw [hiff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨hT.2 h2, ?_⟩
          simp only [Fin.val_last]
          rw [bwdTimeCts_truncSeq_of_le hw h0n h2]
          simp only [tailSeq, add_zero]
          rw [show k + 2 = k + 1 + 1 by omega, resEpoch_succ_eq, Finset.sum_range_succ] at h1
          rw [resEpoch_succ_eq]
          linarith
        · rintro ⟨h2', h1⟩
          have h2 := hT.1 h2'
          refine ⟨?_, h2⟩
          simp only [Fin.val_last] at h1
          rw [bwdTimeCts_truncSeq_of_le hw h0n h2] at h1
          simp only [tailSeq, add_zero] at h1
          rw [show k + 2 = k + 1 + 1 by omega, resEpoch_succ_eq, Finset.sum_range_succ]
          rw [resEpoch_succ_eq] at h1
          linarith
      · have hk' := (hiff.1 hk).1
        have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
        have hjn : ((j : ℕ) : ℝ) * δ ≤ (n : ℝ) * δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
        exact (bwdTimeCts_truncSeq hw (lt_of_le_of_lt hjn hk')).symm
  · filter_upwards [hgood] with w ⟨hdiv, hw⟩
    exact bwdSkel_succ hδ hw hdiv n

/-- If the second epoch lies beyond `t ≥ c`, then `V⁻(t) = t − c`. -/
theorem bwdTimeCts_first {c t : ℝ} {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, z i) atTop atTop) (hct : c ≤ t)
    (hnext : t < c + z 0) : bwdTimeCts (resEpoch c z) t = t - c := by
  rw [bwdTimeCts_eq_resEpoch hz hdiv hct]
  have : sInf {m | t < resEpoch c z (m + 1)} = 1 := by
    rw [natSInf_eq_iff]
    left
    refine ⟨by simpa [resEpoch_succ_eq] using hnext, fun m hm => ?_⟩
    obtain rfl : m = 0 := by omega
    simpa [resEpoch_succ_eq] using hct
  rw [this]
  simp [resEpoch_succ_eq]

/-- If the item in progress outlasts the next `δ`, the age grows by `δ`. -/
theorem bwdSkelStep_of_gt {δ x : ℝ} (hx : 0 ≤ x) {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, y i) atTop atTop) (hδ : 0 ≤ δ)
    (hxy : x + δ < y 0) : bwdSkelStep δ (x, y) = x + δ := by
  unfold bwdSkelStep
  rw [bwdTimeCts_first hy hdiv (by linarith) (by linarith)]
  ring

/-- If the item in progress ends within the next `δ`, the age is less than `x + δ`. -/
theorem bwdSkelStep_lt {δ x : ℝ} (hx : 0 ≤ x) {y : ℕ → ℝ} (hxy : x < y 0)
    (hyx : y 0 ≤ x + δ) :
    bwdSkelStep δ (x, y) < x + δ := by
  unfold bwdSkelStep
  have h2 : resEpoch (-x) y 2 ≤ δ := by
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, resEpoch_succ_eq, Finset.sum_range_one]
    linarith
  have hS : BddBelow {d | ∃ n, 1 ≤ n ∧ resEpoch (-x) y n ≤ δ ∧ d = δ - resEpoch (-x) y n} :=
    ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have := csInf_le hS ⟨2, by norm_num, h2, rfl⟩
  change bwdTimeCts (resEpoch (-x) y) δ ≤ _ at this
  refine lt_of_le_of_lt this ?_
  simp only [show (2 : ℕ) = 1 + 1 by norm_num, resEpoch_succ_eq, Finset.sum_range_one]
  linarith

/-- If the item in progress ends within the next `δ`, the age at `δ` is computed from the
renewal process started at its end. -/
theorem bwdSkelStep_split {δ x : ℝ} (hx : 0 ≤ x) {y : ℕ → ℝ} (hxy : x < y 0) (hyx : y 0 ≤ x + δ) :
    bwdSkelStep δ (x, y) = bwdTimeCts (resEpoch (y 0 - x) (tailSeq 1 y)) δ := by
  have hR : ∀ m, resEpoch (y 0 - x) (tailSeq 1 y) (m + 1) = resEpoch (-x) y (m + 2) := fun m => by
    rw [show m + 2 = m + 1 + 1 by omega, resEpoch_succ_eq, resEpoch_succ_eq,
      Finset.sum_range_succ']
    simp only [tailSeq]
    have : ∑ i ∈ Finset.range m, y (1 + i) = ∑ i ∈ Finset.range m, y (i + 1) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [this]
    ring
  unfold bwdSkelStep bwdTimeCts
  set SL := {d | ∃ n, 1 ≤ n ∧ resEpoch (-x) y n ≤ δ ∧ d = δ - resEpoch (-x) y n}
  set SR := {d | ∃ n, 1 ≤ n ∧ resEpoch (y 0 - x) (tailSeq 1 y) n ≤ δ ∧
    d = δ - resEpoch (y 0 - x) (tailSeq 1 y) n}
  have hbL : BddBelow SL := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hbR : BddBelow SR := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hR0 : resEpoch (y 0 - x) (tailSeq 1 y) 1 = y 0 - x := by simp [resEpoch_succ_eq]
  have hmemR : δ - (y 0 - x) ∈ SR := ⟨1, le_rfl, by rw [hR0]; linarith, by rw [hR0]⟩
  have hsub : SR ⊆ SL := by
    rintro d ⟨j, hj, hjd, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hR] at hjd ⊢
    exact ⟨j + 2, by omega, hjd, rfl⟩
  refine le_antisymm (le_csInf ⟨_, hmemR⟩ fun d hd => csInf_le hbL (hsub hd))
    (le_csInf ⟨_, hsub hmemR⟩ ?_)
  rintro d ⟨m, hm, hmd, rfl⟩
  by_cases hm2 : 2 ≤ m
  · refine csInf_le hbR ⟨m - 1, by omega, ?_, ?_⟩
    · rw [show m - 1 = (m - 2) + 1 by omega, hR, show m - 2 + 2 = m by omega]
      exact hmd
    · rw [show m - 1 = (m - 2) + 1 by omega, hR, show m - 2 + 2 = m by omega]
  · obtain rfl : m = 1 := by omega
    refine (csInf_le hbR hmemR).trans ?_
    simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero]
    linarith

/-- `Γ^{⊗ℕ}{y : y₀ ∈ B} = Γ(B)`. -/
theorem infinitePi_measure_head (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {B : Set ℝ}
    (hB : MeasurableSet B) :
    (Measure.infinitePi fun _ : ℕ => Γ) {y | y 0 ∈ B} = Γ B := by
  have : {y : ℕ → ℝ | y 0 ∈ B} = (fun y : ℕ → ℝ => y 0) ⁻¹' B := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply 0) hB, Measure.infinitePi_map_eval]

/-- MT p. 70: `P(V⁻(nδ) = x + δ | V⁻((n − 1)δ) = x) = Γ(x + δ, ∞)/Γ(x, ∞)`. -/
theorem bwdSkelKernel_apply_add (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    bwdSkelKernel Γ δ x {x + δ} = Γ (Ioi (x + δ)) / Γ (Ioi x) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hm : Measurable fun y => bwdSkelStep δ (x, y) :=
    (measurable_bwdSkelStep δ).comp measurable_prodMk_left
  have hD : MeasurableSet {y : ℕ → ℝ | x < y 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  change ((ν[|{y | x < y 0}]).map fun y => bwdSkelStep δ (x, y)) {x + δ} = _
  have hνD : ν {y | x < y 0} = Γ (Ioi x) := infinitePi_measure_head Γ measurableSet_Ioi
  rw [Measure.map_apply hm (measurableSet_singleton _), cond_apply hD, hνD]
  have hset : ({y : ℕ → ℝ | x < y 0} ∩ (fun y => bwdSkelStep δ (x, y)) ⁻¹' {x + δ} : Set _)
      =ᵐ[ν] {y | y 0 ∈ Ioi (x + δ)} := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with y ⟨hdiv, hy⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_Ioi,
      eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hle
      exact absurd h2 (bwdSkelStep_lt hx h1 (not_lt.1 hle)).ne
    · intro h
      exact ⟨by linarith, bwdSkelStep_of_gt hx hy hdiv hδ h⟩
  rw [measure_congr hset, infinitePi_measure_head Γ measurableSet_Ioi, ENNReal.div_eq_inv_mul]

/-- `∫ U(ds) 1{δ − c − s ∈ A} Γ(δ − c − s, ∞)`: the law of the age at `δ` after a renewal
at `c`. -/
noncomputable def bwdInner (Γ : Measure ℝ) (δ c : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ s, A.indicator (fun v => Γ (Ioi v)) (δ - c - s) ∂renewalMeasure Γ

/-- Decomposing `{V⁻(δ) ∈ A}` over the index `j` of the last epoch before `δ`. -/
theorem indicator_bwdTimeCts_eq_tsum {c δ : ℝ} (hcδ : c ≤ δ) {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, z i) atTop atTop) {A : Set ℝ}
    (hA0 : A ⊆ Ico 0 δ) :
    A.indicator (1 : ℝ → ℝ≥0∞) (bwdTimeCts (resEpoch c z) δ) =
      ∑' j, {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, z i, z j) := by
  have hex := exists_resEpoch_gt (x := c) hdiv δ
  set τ := sInf {m | δ < resEpoch c z (m + 1)} with hτdef
  have hτ : δ < resEpoch c z (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, resEpoch c z (m + 1) ≤ δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, resEpoch_succ_eq] at hτ
    simp at hτ
    linarith
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, τ = j₀ + 1 := ⟨τ - 1, by omega⟩
  rw [bwdTimeCts_eq_resEpoch hz hdiv hcδ, ← hτdef, tsum_eq_single j₀ fun j hj => ?_]
  · have hnext : δ < c + ∑ i ∈ Finset.range j₀, z i + z j₀ := by
      rw [hj₀, resEpoch_succ_eq, Finset.sum_range_succ] at hτ
      linarith
    have e : δ - resEpoch c z τ = δ - c - ∑ i ∈ Finset.range j₀, z i := by
      rw [hj₀, resEpoch_succ_eq]
      ring
    rw [e]
    by_cases hA : δ - c - ∑ i ∈ Finset.range j₀, z i ∈ A
    · rw [indicator_of_mem hA, indicator_of_mem (show (∑ i ∈ Finset.range j₀, z i, z j₀) ∈
        {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} from ⟨hA, hnext⟩)]
      rfl
    · rw [indicator_of_notMem hA, indicator_of_notMem (show (∑ i ∈ Finset.range j₀, z i, z j₀) ∉
        {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} from fun h => hA h.1)]
  · refine indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have h3 := hmin (j + 1) (by omega)
      rw [resEpoch_succ_eq, Finset.sum_range_succ] at h3
      linarith
    · have h3 := resEpoch_mono (x := c) hz (show 1 ≤ τ + 1 by omega)
        (show τ + 1 ≤ j + 1 by omega)
      simp only [resEpoch_succ_eq] at h3 hτ
      have := (hA0 h1).1
      linarith

/-- One term of the backward-chain display: the contribution of the `j`-th renewal. -/
theorem lintegral_partialSum_pair_bwd (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {δ c : ℝ}
    {A : Set ℝ} (hA : MeasurableSet A) (j : ℕ) :
    ∫⁻ w, {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) ∂(Measure.infinitePi fun _ : ℕ => Γ) =
      ∫⁻ s, A.indicator (fun v => Γ (Ioi v)) (δ - c - s) ∂(convPow Γ j) := by
  set E : Set (ℝ × ℝ) := {q | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} with hEdef
  have hE : MeasurableSet E :=
    ((measurable_const.sub measurable_fst) hA).inter
      (measurableSet_lt measurable_const ((measurable_const.add measurable_fst).add
        measurable_snd))
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hcp := isProbabilityMeasure_convPow Γ j
  have h1 : ∫⁻ w, E.indicator (1 : ℝ × ℝ → ℝ≥0∞) (∑ i ∈ Finset.range j, w i, w j)
      ∂(Measure.infinitePi fun _ : ℕ => Γ) = ((convPow Γ j).prod Γ) E := by
    rw [← infinitePi_map_partialSum_next Γ j, Measure.map_apply hpair hE,
      ← lintegral_indicator_one (hpair hE)]
    rfl
  rw [h1, Measure.prod_apply hE]
  refine lintegral_congr fun s => ?_
  by_cases hs : δ - c - s ∈ A
  · rw [indicator_of_mem hs]
    congr 1
    ext t
    simp only [mem_preimage, hEdef, mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨-, h⟩
      linarith
    · intro h
      exact ⟨hs, by linarith⟩
  · rw [indicator_of_notMem hs]
    convert measure_empty (μ := Γ)
    ext t
    simp only [mem_preimage, hEdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun h => hs h.1

/-- After a renewal at `c ≤ δ`, the age at `δ` lies in `A ⊆ [0, δ)` with probability
`∫ U(ds) 1{δ − c − s ∈ A} Γ(δ − c − s, ∞)`. -/
theorem bwd_inner (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ c : ℝ} (hcδ : c ≤ δ) {A : Set ℝ} (hA : MeasurableSet A)
    (hA0 : A ⊆ Ico 0 δ) :
    (Measure.infinitePi fun _ : ℕ => Γ) {z | bwdTimeCts (resEpoch c z) δ ∈ A} =
      bwdInner Γ δ c A := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hE : MeasurableSet {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} :=
    ((measurable_const.sub measurable_fst) hA).inter
      (measurableSet_lt measurable_const ((measurable_const.add measurable_fst).add
        measurable_snd))
  have hpair : ∀ j, Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) := fun j =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hbm : Measurable fun z : ℕ → ℝ => bwdTimeCts (resEpoch c z) δ :=
    measurable_bwdTimeCts (Z := fun z : ℕ → ℝ => resEpoch c z)
      (fun k => (measurable_resEpoch k).comp (measurable_const.prodMk measurable_id)) δ
  rw [← lintegral_indicator_one (s := {z | bwdTimeCts (resEpoch c z) δ ∈ A}) (hbm hA)]
  have hae : ∀ᵐ z ∂ν, {z | bwdTimeCts (resEpoch c z) δ ∈ A}.indicator
      (1 : (ℕ → ℝ) → ℝ≥0∞) z =
      ∑' j, {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, z i, z j) := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with z ⟨hdiv, hz⟩
    rw [← indicator_bwdTimeCts_eq_tsum hcδ hz hdiv hA0]
    by_cases h : bwdTimeCts (resEpoch c z) δ ∈ A
    · rw [indicator_of_mem (show z ∈ {z | bwdTimeCts (resEpoch c z) δ ∈ A} from h),
        indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (show z ∉ {z | bwdTimeCts (resEpoch c z) δ ∈ A} from h),
        indicator_of_notMem h]
  have hmj : ∀ j, AEMeasurable (fun w : ℕ → ℝ =>
      {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j)) ν := fun j =>
    (Measurable.indicator measurable_one hE |>.comp (hpair j)).aemeasurable
  rw [lintegral_congr_ae hae, lintegral_tsum hmj]
  refine (tsum_congr fun j => lintegral_partialSum_pair_bwd Γ hA j).trans ?_
  rw [bwdInner, renewalMeasure, lintegral_sum_measure]

/-- Under `Γ^{⊗ℕ}`, the first increment and the rest are independent with laws `Γ` and
`Γ^{⊗ℕ}`. -/
theorem infinitePi_map_head_tail (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun y => (y 0, tailSeq 1 y)) =
      Γ.prod (Measure.infinitePi fun _ : ℕ => Γ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hc : (fun y : ℕ → ℝ => (y 0, tailSeq 1 y)) =
      Prod.map (fun b : ℕ → ℝ => b 0) id ∘ fun y => (truncSeq 1 y, tailSeq 1 y) := by
    funext y
    simp [truncSeq]
  have h0 : (ν.map (truncSeq 1)).map (fun b : ℕ → ℝ => b 0) = Γ := by
    rw [Measure.map_map (measurable_pi_apply 0) (measurable_truncSeq 1)]
    have : ((fun b : ℕ → ℝ => b 0) ∘ truncSeq 1) = fun y : ℕ → ℝ => y 0 := by
      funext y
      simp [truncSeq]
    rw [this, Measure.infinitePi_map_eval]
  rw [hc, ← Measure.map_map ((measurable_pi_apply 0).prodMap measurable_id)
    ((measurable_truncSeq 1).prodMk (measurable_tailSeq 1)), infinitePi_map_trunc_tail,
    ← Measure.map_prod_map _ _ (measurable_pi_apply 0) measurable_id, Measure.map_id, h0]

/-- **The backward-chain display of MT p. 70, corrected.** For `A ⊆ [0, δ)`,
`P(V⁻(nδ) ∈ A | V⁻((n−1)δ) = x) =
  Γ(x, ∞)⁻¹ ∫_{(x, x+δ]} Γ(du) ∫ U(ds) 1{δ − (u − x) − s ∈ A} Γ(δ − (u − x) − s, ∞)`:
the normalisation is a division by `Γ(x, ∞)`, not by `[Γ(x, ∞)]⁻¹`. -/
theorem bwdSkelKernel_apply_of_subset (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ico 0 δ) :
    bwdSkelKernel Γ δ x A =
      (Γ (Ioi x))⁻¹ * ∫⁻ u in Ioc x (x + δ), bwdInner Γ δ (u - x) A ∂Γ := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hm : Measurable fun y => bwdSkelStep δ (x, y) :=
    (measurable_bwdSkelStep δ).comp measurable_prodMk_left
  have hD : MeasurableSet {y : ℕ → ℝ | x < y 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  have hνD : ν {y | x < y 0} = Γ (Ioi x) := infinitePi_measure_head Γ measurableSet_Ioi
  change ((ν[|{y | x < y 0}]).map fun y => bwdSkelStep δ (x, y)) A = _
  rw [Measure.map_apply hm hA, cond_apply hD, hνD]
  congr 1
  set G : Set (ℝ × (ℕ → ℝ)) :=
    {q | q.1 ∈ Ioc x (x + δ) ∧ bwdTimeCts (resEpoch (q.1 - x) q.2) δ ∈ A} with hGdef
  have hbm : Measurable fun q : ℝ × (ℕ → ℝ) => bwdTimeCts (resEpoch (q.1 - x) q.2) δ :=
    measurable_bwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch (q.1 - x) q.2)
      (fun k => (measurable_resEpoch k).comp
        ((measurable_fst.sub measurable_const).prodMk measurable_snd)) δ
  have hG : MeasurableSet G := (measurable_fst measurableSet_Ioc).inter (hbm hA)
  have hht : Measurable fun y : ℕ → ℝ => (y 0, tailSeq 1 y) :=
    (measurable_pi_apply 0).prodMk (measurable_tailSeq 1)
  have hset : ({y : ℕ → ℝ | x < y 0} ∩ (fun y => bwdSkelStep δ (x, y)) ⁻¹' A : Set _)
      =ᵐ[ν] (fun y : ℕ → ℝ => (y 0, tailSeq 1 y)) ⁻¹' G := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with y ⟨hdiv, hy⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hGdef, mem_Ioc, eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hle : y 0 ≤ x + δ := by
        by_contra hlt
        rw [bwdSkelStep_of_gt hx hy hdiv hδ (not_le.1 hlt)] at h2
        have := (hA0 h2).2
        linarith
      refine ⟨⟨h1, hle⟩, ?_⟩
      rwa [← bwdSkelStep_split hx h1 hle]
    · rintro ⟨⟨h1, hle⟩, h2⟩
      exact ⟨h1, by rwa [bwdSkelStep_split hx h1 hle]⟩
  rw [measure_congr hset, ← Measure.map_apply hht hG, infinitePi_map_head_tail,
    Measure.prod_apply hG, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ Ioc x (x + δ)
  · rw [indicator_of_mem hu, ← bwd_inner Γ hΓ0 hΓpos (by linarith [hu.2]) hA hA0]
    congr 1
    ext z
    simp only [mem_preimage, hGdef, mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
  · rw [indicator_of_notMem hu]
    convert measure_empty (μ := ν)
    ext z
    simp only [mem_preimage, hGdef, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd h hu

/-- The increment law `Γ = ½δ₁ + ½δ₂` of the counterexample to the backward display. -/
noncomputable def halfOneTwo : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 1 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 2

/-- `Γ(A) = ½·1_A(1) + ½·1_A(2)`. -/
theorem halfOneTwo_apply {A : Set ℝ} (hA : MeasurableSet A) :
    halfOneTwo A = 2⁻¹ * A.indicator 1 1 + 2⁻¹ * A.indicator 1 2 := by
  simp [halfOneTwo, Measure.dirac_apply' _ hA]

/-- `½δ₁ + ½δ₂` is a probability measure. -/
theorem isProbabilityMeasure_halfOneTwo : IsProbabilityMeasure halfOneTwo :=
  ⟨by
    rw [halfOneTwo_apply MeasurableSet.univ]
    simp only [indicator_univ, Pi.one_apply, mul_one]
    exact ENNReal.inv_two_add_inv_two⟩

/-- `∫ f dΓ = ½f(1) + ½f(2)`. -/
theorem lintegral_halfOneTwo (f : ℝ → ℝ≥0∞) :
    ∫⁻ u, f u ∂halfOneTwo = 2⁻¹ * f 1 + 2⁻¹ * f 2 := by
  rw [halfOneTwo, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  rfl

/-- `Γ^{j∗}` is the law of `y₀ + ⋯ + y_{j−1}` under `Γ^{⊗ℕ}`. -/
theorem convPow_eq_map (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (j : ℕ) :
    convPow Γ j = (Measure.infinitePi fun _ : ℕ => Γ).map
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range j, w i) := by
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have := congrArg (Measure.map Prod.fst) (infinitePi_map_partialSum_next Γ j)
  rw [Measure.map_map measurable_fst hpair, Measure.map_fst_prod, measure_univ,
    one_smul] at this
  exact this.symm

/-- **Correction to the backward display of MT p. 70.** With `Γ = ½δ₁ + ½δ₂`, `δ = 1` and
age `x = 1`, the item in progress has length `2` and ends exactly one time unit later, so the
age moves surely to `0`: `P(1, {0}) = 1`. The printed normalisation, dividing by
`[Γ(x, ∞)]⁻¹`, i.e. multiplying by `Γ(x, ∞) = ½`, gives `1/4 ≠ 1`. -/
theorem bwd_display_counterexample :
    (@bwdSkelKernel halfOneTwo isProbabilityMeasure_halfOneTwo 1) 1 {0} = 1 ∧
      halfOneTwo (Ioi 1) * ∫⁻ u in Ioc 1 (1 + 1), bwdInner halfOneTwo 1 (u - 1) {0}
        ∂halfOneTwo ≠ 1 := by
  have := isProbabilityMeasure_halfOneTwo
  have hI0 : halfOneTwo (Iio 0) = 0 := by
    rw [halfOneTwo_apply measurableSet_Iio]
    norm_num [indicator]
  have hI1 : halfOneTwo (Iio 1) = 0 := by
    rw [halfOneTwo_apply measurableSet_Iio]
    norm_num [indicator]
  have hO0 : halfOneTwo (Ioi 0) = 1 := by
    rw [halfOneTwo_apply measurableSet_Ioi]
    norm_num [indicator]
    exact ENNReal.inv_two_add_inv_two
  have hO1 : halfOneTwo (Ioi 1) = 2⁻¹ := by
    rw [halfOneTwo_apply measurableSet_Ioi]
    norm_num [indicator]
  have hpos : 0 < halfOneTwo (Ioi 0) := by rw [hO0]; exact one_pos
  have hU : renewalMeasure halfOneTwo {0} = 1 := by
    rw [renewalMeasure, Measure.sum_apply _ (measurableSet_singleton 0),
      tsum_eq_single 0 fun j hj => ?_]
    · rw [convPow_eq_map, Measure.map_apply (Finset.measurable_sum _ fun i _ =>
        measurable_pi_apply i) (measurableSet_singleton 0)]
      simp
    · rw [convPow_eq_map, Measure.map_apply (Finset.measurable_sum _ fun i _ =>
        measurable_pi_apply i) (measurableSet_singleton 0)]
      refine measure_mono_null (t := ⋃ i, {w : ℕ → ℝ | w i < 1}) (fun w hw => ?_) ?_
      · by_contra hc
        simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hc
        simp only [mem_preimage, mem_singleton_iff] at hw
        have h1 : ∑ i ∈ Finset.range j, w i ≥ ∑ i ∈ Finset.range j, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hc i
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
        have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
        linarith
      · refine measure_iUnion_null fun i => ?_
        have : {w : ℕ → ℝ | w i < 1} = (fun w : ℕ → ℝ => w i) ⁻¹' Iio 1 := rfl
        rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
          Measure.infinitePi_map_eval, hI1]
  have hinner : bwdInner halfOneTwo 1 (2 - 1) {0} = 1 := by
    rw [bwdInner]
    have : (fun s : ℝ => ({0} : Set ℝ).indicator (fun v => halfOneTwo (Ioi v)) (1 - (2 - 1) - s))
        = ({0} : Set ℝ).indicator 1 := by
      funext s
      by_cases hs : s = 0
      · subst hs
        norm_num [hO0]
      · have : (1 : ℝ) - (2 - 1) - s ≠ 0 := by
          intro h
          apply hs
          linarith
        simp [hs, this]
    rw [this, lintegral_indicator_one (measurableSet_singleton 0), hU]
  have hint : ∫⁻ u in Ioc 1 (1 + 1), bwdInner halfOneTwo 1 (u - 1) {0} ∂halfOneTwo = 2⁻¹ := by
    rw [← lintegral_indicator measurableSet_Ioc, lintegral_halfOneTwo]
    rw [indicator_of_notMem (show (1 : ℝ) ∉ Ioc 1 (1 + 1) by simp),
      indicator_of_mem (show (2 : ℝ) ∈ Ioc 1 (1 + 1) by norm_num), hinner]
    simp
  refine ⟨?_, ?_⟩
  · rw [bwdSkelKernel_apply_of_subset halfOneTwo hI0 hpos zero_le_one zero_le_one
      (measurableSet_singleton 0) (by simp), hint, hO1, inv_inv]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  · rw [hint, hO1]
    intro h
    have h2 : (2⁻¹ : ℝ≥0∞) * 2⁻¹ < 1 := by
      calc (2⁻¹ : ℝ≥0∞) * 2⁻¹ ≤ 2⁻¹ * 1 := by gcongr; exact ENNReal.inv_le_one.2 (by norm_num)
        _ < 1 := by rw [mul_one]; exact ENNReal.inv_lt_one.2 (by norm_num)
    exact absurd h h2.ne

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GI/G/1 queue as a ladder chain (MT §3.5.4)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/GIG1Embedding.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`. The ladder kernel `ladderKernel` is
renamed `ladderChainKernel` here, since `ladderKernel` already names the Chapter 5 counterexample
kernel in `PseudoAtoms`.

Meyn and Tweedie, §3.5.4, p. 71: with `Nₙ` the number of customers just before the `n`-th
arrival and `Rₙ` the residual service time just after it, `Φₙ = (Nₙ, Rₙ)` is a Markov chain with
the ladder kernel (3.40), (3.42)–(3.43) ("it is easy to verify").

The queue is built from its primitives on the canonical space `ℝ^ℕ × ℝ^ℕ` with law
`G^{⊗ℕ} ⊗ H^{⊗ℕ}`: interarrival times (`arrT`), service times and first-come-first-served
departures (`depT`), the customer in service (`inService`), `Nₙ = queueN`, `Rₙ = queueR`.

* `gig1_step_eq`: pathwise, `(N_{n+1}, R_{n+1})` is the ladder step `gig1Step` from
  `(Nₙ, Rₙ)` driven by the next interarrival time and the services of the customers after the one
  in service.
* `gig1_law_past_future`: that future is independent of the past at the `n`-th arrival and is
  again `G^{⊗ℕ} ⊗ H^{⊗ℕ}`.
* `gig1Ladder_eq_map`: the law of one step from `(i, x)` is `gig1Ladder H G (i, x)`.
* `gig1_isMarkovChain`: `Φ` is a Markov chain with kernel `gig1Ladder H G` and initial law
  `δ₀ ⊗ H` (the first customer finds the system empty), via `isMarkovChain_of_regeneration` at
  the index of the customer in service.

Hypotheses: interarrival times are nonnegative (`G(−∞, 0) = 0`) and service times are positive
(`H(−∞, 0] = 0`).

**Correction.** MT call `Rₙ` the "total residual service time in the system at `Tₙ+`", but
(3.41)–(3.43) use the residual service of the customer in service (the forward recurrence time
of the service renewal process); with the total workload the transition law is not (3.42)–(3.43).
Here `Rₙ` is the residual service of the customer in service.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- Rearranging a product of four independent factors: `(μa ⊗ μb) ⊗ (μc ⊗ μd)` pushed by
`((a, b), (c, d)) ↦ ((a, c), (b, d))` is `(μa ⊗ μc) ⊗ (μb ⊗ μd)`. -/
theorem map_prod_prod_rearrange {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μa : Measure A) (μb : Measure B) (μc : Measure C)
    (μd : Measure D) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    ((μa.prod μb).prod (μc.prod μd)).map (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) =
      (μa.prod μc).prod (μb.prod μd) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have e3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have e4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have e5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  have h := e5.comp (e4.comp (e3.comp (e2.comp e1)))
  convert h.map_eq using 2
  funext q
  rfl

/-- The arrival epochs `T₀ = 0`, `Tₙ = a₀ + ⋯ + a_{n−1}` of customers `0, 1, 2, …`, with
interarrival times `aᵢ` (MT (Q1), p. 40). -/
def arrT (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

/-- The departure epochs of a single-server first-come-first-served queue with service times
`sₘ` (MT (Q2)–(Q3)): `D₀ = s₀` and `D_{m+1} = max(Dₘ, T_{m+1}) + s_{m+1}`. -/
noncomputable def depT (a s : ℕ → ℝ) : ℕ → ℝ
  | 0 => s 0
  | m + 1 => max (depT a s m) (arrT a (m + 1)) + s (m + 1)

/-- The customer in service just after the `n`-th arrival: the first customer still present
at `Tₙ`. -/
noncomputable def inService (a s : ℕ → ℝ) (n : ℕ) : ℕ := sInf {m | arrT a n < depT a s m}

/-- `Nₙ`, the number of customers in the system just before the `n`-th arrival, `Tₙ−`
(MT p. 71). -/
noncomputable def queueN (a s : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun m => arrT a n < depT a s m).card

/-- `Rₙ`, the residual service time at `Tₙ+` of the customer then in service (MT p. 71). -/
noncomputable def queueR (a s : ℕ → ℝ) (n : ℕ) : ℝ := depT a s (inService a s n) - arrT a n

/-- `T_{n+1} = Tₙ + aₙ`. -/
theorem arrT_succ (a : ℕ → ℝ) (n : ℕ) : arrT a (n + 1) = arrT a n + a n :=
  Finset.sum_range_succ _ _

/-- Arrival epochs increase. -/
theorem arrT_mono {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) {m n : ℕ} (h : m ≤ n) : arrT a m ≤ arrT a n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => ha i

/-- Every customer leaves after arriving. -/
theorem arrT_lt_depT {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (m : ℕ) : arrT a m < depT a s m := by
  cases m with
  | zero => simpa [arrT, depT] using hs 0
  | succ m =>
    simp only [depT]
    have := hs (m + 1)
    have := le_max_right (depT a s m) (arrT a (m + 1))
    linarith

/-- Customers leave in order. -/
theorem depT_lt_succ {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (m : ℕ) :
    depT a s m < depT a s (m + 1) := by
  simp only [depT]
  have := hs (m + 1)
  have := le_max_left (depT a s m) (arrT a (m + 1))
  linarith

/-- Departure epochs increase. -/
theorem depT_mono {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) : Monotone (depT a s) :=
  monotone_nat_of_le_succ fun m => (depT_lt_succ hs m).le

/-- The customer in service at `Tₙ+` is present, has arrived, and all earlier customers have
left. -/
theorem inService_spec {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (n : ℕ) :
    arrT a n < depT a s (inService a s n) ∧ inService a s n ≤ n ∧
      ∀ m < inService a s n, depT a s m ≤ arrT a n := by
  have hex : ∃ m, arrT a n < depT a s m := ⟨n, arrT_lt_depT hs n⟩
  exact ⟨Nat.sInf_mem hex, Nat.sInf_le (arrT_lt_depT hs n),
    fun m hm => not_lt.1 (Nat.notMem_of_lt_sInf hm)⟩

/-- `Nₙ = n − cₙ`, where `cₙ` is the customer in service at `Tₙ+`. -/
theorem queueN_eq {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (n : ℕ) :
    queueN a s n = n - inService a s n := by
  obtain ⟨h1, h2, h3⟩ := inService_spec hs n
  have : (Finset.range n).filter (fun m => arrT a n < depT a s m) =
      Finset.Ico (inService a s n) n := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hm, hlt⟩
      refine ⟨?_, hm⟩
      by_contra hc
      exact absurd (h3 m (not_le.1 hc)) (not_le.2 hlt)
    · rintro ⟨hm1, hm2⟩
      exact ⟨hm2, lt_of_lt_of_le h1 (depT_mono hs hm1)⟩
  rw [queueN, this, Nat.card_Ico]

/-- The customer in service at successive arrivals does not decrease. -/
theorem inService_mono {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) {m n : ℕ}
    (h : m ≤ n) : inService a s m ≤ inService a s n := by
  obtain ⟨h1, -, -⟩ := inService_spec (a := a) hs n
  exact Nat.sInf_le (lt_of_le_of_lt (arrT_mono ha h) h1)

/-- After `Tₙ` the customers present leave at the renewal epochs started from the residual
service `Rₙ`, driven by the services of the customers waiting behind. -/
theorem depT_chain {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) {n : ℕ} :
    ∀ j, inService a s n + j ≤ n →
      depT a s (inService a s n + j) =
        arrT a n + resEpoch (queueR a s n) (tailSeq (inService a s n + 1) s) (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [queueR, resEpoch_succ_eq]
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    obtain ⟨h1, -, -⟩ := inService_spec (a := a) hs n
    have hle : arrT a (inService a s n + j + 1) ≤ depT a s (inService a s n + j) :=
      (arrT_mono ha (by omega)).trans (h1.le.trans (depT_mono hs (by omega)))
    rw [show inService a s n + (j + 1) = inService a s n + j + 1 by omega, depT,
      max_eq_left hle, ih', resEpoch_succ_eq, resEpoch_succ_eq, Finset.sum_range_succ]
    simp only [tailSeq]
    rw [show inService a s n + 1 + j = inService a s n + j + 1 by omega]
    ring

/-- The number of service completions within time `t` in the renewal process started with
residual service `x`. -/
noncomputable def numDone (x : ℝ) (σ : ℕ → ℝ) (t : ℝ) : ℕ := sInf {j | t < resEpoch x σ (j + 1)}

/-- One step of the GI/G/1 ladder chain: from `(i, x)` with interarrival time `α₀` and the
services `σ` of the following customers. -/
noncomputable def gig1Step (q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))) : ℕ × ℝ :=
  if resEpoch q.1.2 q.2.2 (q.1.1 + 1) ≤ q.2.1 0 then (0, q.2.2 q.1.1)
  else (q.1.1 + 1 - numDone q.1.2 q.2.2 (q.2.1 0),
    resEpoch q.1.2 q.2.2 (numDone q.1.2 q.2.2 (q.2.1 0) + 1) - q.2.1 0)

/-- **The GI/G/1 recursion.** `(N_{n+1}, R_{n+1})` is the ladder step from `(Nₙ, Rₙ)` driven by
the next interarrival time and the services of the customers after the one in service. -/
theorem gig1_step_eq {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) (n : ℕ) :
    (queueN a s (n + 1), queueR a s (n + 1)) =
      gig1Step ((queueN a s n, queueR a s n), (tailSeq n a, tailSeq (inService a s n + 1) s)) := by
  set k := inService a s n with hkdef
  obtain ⟨h1, hkn, h3⟩ := inService_spec (a := a) hs n
  set x := queueR a s n
  set σ := tailSeq (k + 1) s
  have hN : queueN a s n = n - k := queueN_eq hs n
  have hchain := depT_chain (a := a) ha hs (n := n)
  have hT : arrT a (n + 1) = arrT a n + a n := arrT_succ a n
  have hdepn : depT a s n = arrT a n + resEpoch x σ (n - k + 1) := by
    have := hchain (n - k) (by omega)
    rwa [show k + (n - k) = n by omega] at this
  unfold gig1Step
  simp only [hN, tailSeq, add_zero]
  change _ = if resEpoch x σ (n - k + 1) ≤ a n then (0, σ (n - k)) else
    (n - k + 1 - numDone x σ (a n), resEpoch x σ (numDone x σ (a n) + 1) - a n)
  have hNe : queueN a s (n + 1) = n + 1 - inService a s (n + 1) := queueN_eq hs (n + 1)
  split_ifs with hcase
  · have hc : inService a s (n + 1) = n + 1 := by
      unfold inService
      rw [natSInf_eq_iff]
      left
      refine ⟨arrT_lt_depT hs (n + 1), fun m hm => not_lt.2 ?_⟩
      have := depT_mono (a := a) hs (show m ≤ n by omega)
      linarith
    rw [hNe, hc, queueR, hc, depT, hT, max_eq_right (by linarith)]
    simp only [Nat.sub_self, σ, tailSeq]
    congr 1
    rw [show k + 1 + (n - k) = n + 1 by omega]
    ring
  · have hℓ : numDone x σ (a n) ≤ n - k := Nat.sInf_le (not_le.1 hcase)
    have hℓspec : a n < resEpoch x σ (numDone x σ (a n) + 1) :=
      Nat.sInf_mem (s := {j | a n < resEpoch x σ (j + 1)})
        ⟨n - k, show a n < resEpoch x σ (n - k + 1) from not_le.1 hcase⟩
    have hℓmin : ∀ j < numDone x σ (a n), resEpoch x σ (j + 1) ≤ a n := fun j hj =>
      not_lt.1 (Nat.notMem_of_lt_sInf hj)
    have hc : inService a s (n + 1) = k + numDone x σ (a n) := by
      unfold inService
      rw [natSInf_eq_iff]
      left
      refine ⟨?_, fun m hm => not_lt.2 ?_⟩
      · rw [hchain _ (by omega), hT]
        linarith
      · by_cases hmk : m < k
        · have := h3 m hmk
          have := ha n
          linarith
        · obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
          rw [hchain j (by omega), hT]
          have := hℓmin j (by omega)
          linarith
    rw [hNe, hc, queueR, hc, hchain _ (by omega), hT]
    congr 1
    · omega
    · ring

/-- Evaluating a sequence of measurable maps at a measurable random index is measurable. -/
theorem measurable_comp_index {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {L : Ω → ℕ} (hL : Measurable L) {f : ℕ → Ω → X} (hf : ∀ n, Measurable (f n)) :
    Measurable fun ω => f (L ω) ω :=
  (measurable_from_prod_countable_right (f := fun p : ℕ × Ω => f p.1 p.2) hf).comp
    (hL.prodMk measurable_id)

/-- Arrival epochs are measurable. -/
theorem measurable_arrT (n : ℕ) : Measurable fun a : ℕ → ℝ => arrT a n :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- Departure epochs are measurable. -/
theorem measurable_depT (m : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => depT ω.1 ω.2 m := by
  induction m with
  | zero => exact (measurable_pi_apply 0).comp measurable_snd
  | succ m ih =>
    exact (ih.max ((measurable_arrT (m + 1)).comp measurable_fst)).add
      ((measurable_pi_apply (m + 1)).comp measurable_snd)

/-- The customer in service is a measurable random index. -/
theorem measurableSet_inService_eq (n k : ℕ) :
    MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) | inService ω.1 ω.2 n = k} :=
  measurableSet_natSInf_eq
    (P := fun (ω : (ℕ → ℝ) × (ℕ → ℝ)) m => arrT ω.1 n < depT ω.1 ω.2 m)
    (fun m => measurableSet_lt ((measurable_arrT n).comp measurable_fst) (measurable_depT m)) k

/-- The customer in service is measurable. -/
theorem measurable_inService (n : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => inService ω.1 ω.2 n :=
  measurable_to_countable' fun k => measurableSet_inService_eq n k

/-- `Nₙ` is measurable. -/
theorem measurable_queueN (n : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => queueN ω.1 ω.2 n := by
  have h : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => queueN ω.1 ω.2 n) = fun ω =>
      ∑ m ∈ Finset.range n, if arrT ω.1 n < depT ω.1 ω.2 m then 1 else 0 := by
    funext ω
    rw [queueN, Finset.card_filter]
  rw [h]
  exact Finset.measurable_sum _ fun m _ => Measurable.ite
    (measurableSet_lt ((measurable_arrT n).comp measurable_fst) (measurable_depT m))
    measurable_const measurable_const

/-- `Rₙ` is measurable. -/
theorem measurable_queueR (n : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => queueR ω.1 ω.2 n :=
  (measurable_comp_index (measurable_inService n) (f := fun m ω => depT ω.1 ω.2 m)
    measurable_depT).sub ((measurable_arrT n).comp measurable_fst)

/-- The number of completions is measurable. -/
theorem measurable_numDone :
    Measurable fun q : ℝ × (ℝ × (ℕ → ℝ)) => numDone q.1 q.2.2 q.2.1 :=
  measurable_to_countable' fun k => measurableSet_natSInf_eq
    (P := fun (q : ℝ × (ℝ × (ℕ → ℝ))) j => q.2.1 < resEpoch q.1 q.2.2 (j + 1))
    (fun j => measurableSet_lt (measurable_fst.comp measurable_snd)
      ((measurable_resEpoch (j + 1)).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))) k

/-- The ladder step is measurable. -/
theorem measurable_gig1Step : Measurable gig1Step := by
  have hL : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.1.1 :=
    measurable_fst.comp measurable_fst
  have hx : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.1.2 :=
    measurable_snd.comp measurable_fst
  have ht : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.2.1 0 :=
    (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
  have hσ : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.2.2 :=
    measurable_snd.comp measurable_snd
  have hZ : ∀ j, Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => resEpoch q.1.2 q.2.2 j :=
    fun j => (measurable_resEpoch j).comp (hx.prodMk hσ)
  have hℓ : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
      numDone q.1.2 q.2.2 (q.2.1 0) :=
    measurable_numDone.comp (hx.prodMk (ht.prodMk hσ))
  refine measurable_comp_index hL (f := fun i q =>
    if resEpoch q.1.2 q.2.2 (i + 1) ≤ q.2.1 0 then ((0 : ℕ), q.2.2 i)
    else (i + 1 - numDone q.1.2 q.2.2 (q.2.1 0),
      resEpoch q.1.2 q.2.2 (numDone q.1.2 q.2.2 (q.2.1 0) + 1) - q.2.1 0)) fun i => ?_
  refine Measurable.ite (measurableSet_le (hZ (i + 1)) ht)
    (measurable_const.prodMk ((measurable_pi_apply i).comp hσ))
    ((measurable_of_countable (fun l : ℕ => i + 1 - l) |>.comp hℓ).prodMk
      ((measurable_comp_index hℓ (f := fun l q => resEpoch q.1.2 q.2.2 (l + 1))
        fun l => hZ (l + 1)).sub ht))

/-- The first `n + 1` arrival epochs only use the first `n` interarrival times. -/
theorem arrT_truncSeq {a : ℕ → ℝ} {n j : ℕ} (hj : j ≤ n) : arrT (truncSeq n a) j = arrT a j :=
  Finset.sum_congr rfl fun i hi => by
    have : i < n := by simp at hi; omega
    simp [truncSeq, this]

/-- The departures of the first `k + 1` customers only use their own services and the first
`n` interarrival times. -/
theorem depT_truncSeq {a s : ℕ → ℝ} {n k : ℕ} :
    ∀ m, m ≤ n → m ≤ k → depT (truncSeq n a) (truncSeq (k + 1) s) m = depT a s m := by
  intro m
  induction m with
  | zero =>
    intro _ _
    simp [depT, truncSeq]
  | succ m ih =>
    intro hmn hmk
    simp only [depT]
    rw [ih (by omega) (by omega), arrT_truncSeq hmn]
    simp [truncSeq, show m + 1 < k + 1 by omega]

/-- The customers in service at the first `n` arrivals are determined by the past at the
`n`-th arrival. -/
theorem inService_truncSeq {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) {n j : ℕ}
    (hj : j ≤ n) :
    inService (truncSeq n a) (truncSeq (inService a s n + 1) s) j = inService a s j := by
  set k := inService a s n
  obtain ⟨h1, h2, h3⟩ := inService_spec (a := a) hs j
  have hjk : inService a s j ≤ k := inService_mono ha hs hj
  have hkn : k ≤ n := (inService_spec (a := a) hs n).2.1
  change sInf {m | arrT (truncSeq n a) j < depT (truncSeq n a) (truncSeq (k + 1) s) m} =
    inService a s j
  rw [natSInf_eq_iff]
  left
  refine ⟨?_, fun m hm => ?_⟩
  · rw [arrT_truncSeq hj, depT_truncSeq _ (by omega) hjk]
    exact h1
  · rw [arrT_truncSeq hj, depT_truncSeq _ (by omega) (by omega)]
    exact not_lt.2 (h3 m hm)

/-- The event `{cₙ = k}` is determined by the first `n` interarrival times and the first
`k + 1` services. -/
theorem inService_eq_iff_truncSeq {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (n k : ℕ) :
    inService a s n = k ↔
      (arrT (truncSeq n a) n < depT (truncSeq n a) (truncSeq (k + 1) s) k ∧
        ∀ m < k, depT (truncSeq n a) (truncSeq (k + 1) s) m ≤ arrT (truncSeq n a) n) := by
  rw [arrT_truncSeq le_rfl]
  by_cases hkn : k ≤ n
  · rw [depT_truncSeq _ hkn le_rfl]
    have e : (∀ m < k, depT (truncSeq n a) (truncSeq (k + 1) s) m ≤ arrT a n) ↔
        ∀ m < k, depT a s m ≤ arrT a n :=
      forall₂_congr fun m hm => by rw [depT_truncSeq _ (by omega) (by omega)]
    rw [e]
    unfold inService
    rw [natSInf_eq_iff]
    simp only [not_lt]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd (h n) (not_le.2 (arrT_lt_depT hs n))
    · exact Or.inl
  · constructor
    · intro h
      exact absurd (h ▸ (inService_spec (a := a) hs n).2.1) hkn
    · rintro ⟨-, h⟩
      have := h n (by omega)
      rw [depT_truncSeq _ le_rfl (by omega)] at this
      exact absurd this (not_le.2 (arrT_lt_depT hs n))

/-- Two measures on `ℕ × ℝ` agree if they agree on all sets `{j} × A`. -/
theorem measure_ext_nat_prod {μ ν : Measure (ℕ × ℝ)}
    (h : ∀ j (A : Set ℝ), MeasurableSet A → μ ({j} ×ˢ A) = ν ({j} ×ˢ A)) : μ = ν := by
  ext E hE
  have hE' : E = ⋃ j, ({j} : Set ℕ) ×ˢ (Prod.mk j ⁻¹' E) := by
    ext ⟨j, y⟩
    simp
  have hd : Pairwise fun a b =>
      Disjoint (({a} : Set ℕ) ×ˢ (Prod.mk a ⁻¹' E)) (({b} : Set ℕ) ×ˢ (Prod.mk b ⁻¹' E)) :=
    fun a b hab => Set.disjoint_left.2 fun p ha hb => hab (ha.1.symm.trans hb.1)
  have hm : ∀ j, MeasurableSet (({j} : Set ℕ) ×ˢ (Prod.mk j ⁻¹' E)) := fun j =>
    (measurableSet_singleton j).prod (measurable_prodMk_left hE)
  rw [hE', measure_iUnion hd hm, measure_iUnion hd hm]
  exact tsum_congr fun j => h j _ (measurable_prodMk_left hE)

/-- The ladder step as a function of the interarrival time and the services alone. -/
noncomputable def gig1Step0 (i : ℕ) (x : ℝ) (q : ℝ × (ℕ → ℝ)) : ℕ × ℝ :=
  gig1Step ((i, x), ((fun _ => q.1), q.2))

/-- If the `(i+1)`-th epoch is after `t`, at most `i` services are completed by `t`. -/
theorem numDone_le_of_lt {x t : ℝ} {σ : ℕ → ℝ} {i : ℕ} (h : t < resEpoch x σ (i + 1)) :
    numDone x σ t ≤ i := Nat.sInf_le h

/-- Exactly `m` services are completed by `t ≥ 0` iff `Zₘ ≤ t < Z_{m+1}`. -/
theorem numDone_eq_iff {x t : ℝ} {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, σ i) atTop atTop) (ht : 0 ≤ t) (m : ℕ) :
    numDone x σ t = m ↔ resEpoch x σ m ≤ t ∧ t < resEpoch x σ (m + 1) := by
  have h0 : resEpoch x σ 0 = 0 := rfl
  unfold numDone
  rw [natSInf_eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h, rfl⟩)
    · refine ⟨?_, h1⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [h0]
        exact ht
      · have := h2 (m - 1) (by omega)
        rw [show m - 1 + 1 = m by omega] at this
        exact not_lt.1 this
    · obtain ⟨m, hm⟩ := exists_resEpoch_gt (x := x) hdiv t
      exact absurd hm (h m)
  · rintro ⟨h1, h2⟩
    refine Or.inl ⟨h2, fun j hj => not_lt.2 ?_⟩
    exact (resEpoch_mono hσ (by omega) (show j + 1 ≤ m by omega)).trans h1

/-- At least `i + 1` services are completed by `t` iff exactly `j + i + 1` are, for one `j`. -/
theorem tsum_indicator_tail_eq {x t : ℝ} {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, σ i) atTop atTop) (i : ℕ) :
    ∑' j, (if resEpoch x σ (j + i + 1) ≤ t ∧ t < resEpoch x σ (j + i + 1 + 1) then
      (1 : ℝ≥0∞) else 0) = if resEpoch x σ (i + 1) ≤ t then 1 else 0 := by
  by_cases hti : resEpoch x σ (i + 1) ≤ t
  · simp only [hti, ite_true]
    have hex := exists_resEpoch_gt (x := x) hdiv t
    set ℓ := numDone x σ t
    have hℓ : t < resEpoch x σ (ℓ + 1) := Nat.sInf_mem hex
    have hℓmin : ∀ j < ℓ, resEpoch x σ (j + 1) ≤ t := fun j hj =>
      not_lt.1 (Nat.notMem_of_lt_sInf hj)
    have hiℓ : i + 1 ≤ ℓ := by
      by_contra hc
      have := resEpoch_mono (x := x) hσ (show 1 ≤ ℓ + 1 by omega) (show ℓ + 1 ≤ i + 1 by omega)
      linarith
    have hA : resEpoch x σ (ℓ - (i + 1) + i + 1) ≤ t := by
      have := hℓmin (ℓ - 1) (by omega)
      rwa [show ℓ - 1 + 1 = ℓ by omega, show ℓ = ℓ - (i + 1) + i + 1 by omega] at this
    have hB : t < resEpoch x σ (ℓ - (i + 1) + i + 1 + 1) := by
      rwa [show ℓ - (i + 1) + i + 1 + 1 = ℓ + 1 by omega]
    rw [tsum_eq_single (ℓ - (i + 1)) fun j hj => ?_]
    · simp [hA, hB]
    · have hne : ¬ (resEpoch x σ (j + i + 1) ≤ t ∧ t < resEpoch x σ (j + i + 1 + 1)) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hj with hlt | hgt
        · have := hℓmin (j + i + 1) (by omega)
          linarith
        · have := resEpoch_mono (x := x) hσ (show 1 ≤ ℓ + 1 by omega)
            (show ℓ + 1 ≤ j + i + 1 by omega)
          linarith
      simp only [hne, ite_false]
  · simp only [hti, ite_false]
    refine ENNReal.tsum_eq_zero.2 fun j => ?_
    have hne : ¬ (resEpoch x σ (j + i + 1) ≤ t ∧ t < resEpoch x σ (j + i + 1 + 1)) := by
      rintro ⟨h1, -⟩
      have := resEpoch_mono (x := x) hσ (show 1 ≤ i + 1 by omega)
        (show i + 1 ≤ j + i + 1 by omega)
      exact hti (this.trans h1)
    simp only [hne, ite_false]

/-- `gig1Step0` is measurable. -/
theorem measurable_gig1Step0 (i : ℕ) (x : ℝ) : Measurable (gig1Step0 i x) :=
  measurable_gig1Step.comp (measurable_const.prodMk
    ((measurable_pi_iff.2 fun _ => measurable_fst).prodMk measurable_snd))

/-- The queue length rises by at most one between arrivals. -/
theorem gig1Step0_fst_le (i : ℕ) (x : ℝ) (q : ℝ × (ℕ → ℝ)) : (gig1Step0 i x q).1 ≤ i + 1 := by
  unfold gig1Step0 gig1Step
  split_ifs <;> simp

/-- The queue is empty just before the next arrival iff all `i + 1` customers are served, and
then the new service is the next one. -/
theorem gig1Step0_mem_zero_iff (i : ℕ) (x : ℝ) (q : ℝ × (ℕ → ℝ)) (A : Set ℝ) :
    gig1Step0 i x q ∈ ({0} : Set ℕ) ×ˢ A ↔ resEpoch x q.2 (i + 1) ≤ q.1 ∧ q.2 i ∈ A := by
  unfold gig1Step0 gig1Step
  simp only
  split_ifs with h
  · simp [h]
  · simp only [mem_prod, mem_singleton_iff, h, false_and, iff_false, not_and]
    intro h1
    have := numDone_le_of_lt (x := x) (σ := q.2) (t := q.1) (not_le.1 h)
    omega

/-- The queue holds `j ≥ 1` customers before the next arrival iff exactly `i + 1 − j` services
are completed. -/
theorem gig1Step0_mem_iff {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i + 1) {x : ℝ}
    {q : ℝ × (ℕ → ℝ)} (ht : 0 ≤ q.1) (hσ : ∀ i, 0 ≤ q.2 i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, q.2 i) atTop atTop) (A : Set ℝ) :
    gig1Step0 i x q ∈ ({j} : Set ℕ) ×ˢ A ↔
      q ∈ Prod.mk x ⁻¹' gig1Set (i + 1 - j) A := by
  unfold gig1Step0 gig1Step
  simp only [gig1Set, mem_preimage, mem_ofPred_eq, mem_prod, mem_singleton_iff]
  split_ifs with h
  · simp only [show (0 : ℕ) ≠ j by omega, false_and, false_iff, not_and]
    intro h1 h2
    have := resEpoch_mono (x := x) hσ (show 1 ≤ i + 1 - j + 1 by omega)
      (show i + 1 - j + 1 ≤ i + 1 by omega)
    linarith
  · have hℓ := numDone_le_of_lt (x := x) (σ := q.2) (t := q.1) (not_le.1 h)
    constructor
    · rintro ⟨h1, h2⟩
      have hm : numDone x q.2 q.1 = i + 1 - j := by omega
      rw [hm] at h2
      exact ⟨((numDone_eq_iff hσ hdiv ht _).1 hm).1, ((numDone_eq_iff hσ hdiv ht _).1 hm).2, h2⟩
    · rintro ⟨h1, h2, h3⟩
      have hm := (numDone_eq_iff hσ hdiv ht (i + 1 - j)).2 ⟨h1, h2⟩
      rw [hm]
      exact ⟨by omega, h3⟩

/-- Almost surely the interarrival time is nonnegative and the service epochs increase to
infinity. -/
theorem ae_good_gig1 (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) :
    ∀ᵐ q ∂(G.prod (Measure.infinitePi fun _ : ℕ => H)),
      0 ≤ q.1 ∧ Tendsto (fun n => ∑ i ∈ Finset.range n, q.2 i) atTop atTop ∧
        ∀ i, 0 ≤ q.2 i := by
  have h1 : ∀ᵐ t ∂G, 0 ≤ t := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
      ext a
      simp
    rw [this, hG0]
  have h1' := (measurePreserving_fst (μ := G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae h1
  have h2' := (measurePreserving_snd (μ := G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae
      (tendsto_partialSum_atTop_ae H hH0 hHpos)
  filter_upwards [h1', h2'] with q hq1 hq2
  exact ⟨hq1, hq2.1, hq2.2⟩

/-- **The GI/G/1 kernel is the law of one queue step**: `gig1Ladder H G (i, x)` (MT (3.40),
(3.42)–(3.43)) is the law of the ladder step from `(i, x)` with `T ∼ G` and i.i.d. services
`∼ H`. -/
theorem gig1Ladder_eq_map (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (i : ℕ) (x : ℝ) :
    gig1Ladder H G (i, x) = (G.prod (Measure.infinitePi fun _ : ℕ => H)).map (gig1Step0 i x) := by
  set ν := Measure.infinitePi fun _ : ℕ => H
  set ρ := G.prod ν
  have hgood := ae_good_gig1 H G hH0 hHpos hG0
  refine measure_ext_nat_prod fun j A hA => ?_
  rw [Measure.map_apply (measurable_gig1Step0 i x) ((measurableSet_singleton j).prod hA)]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [gig1Ladder, eq_3_40_zero _ _ i x hA]
    change (∑' k, gig1Lambda H G (k + i + 1) x univ) * H A = _
    have hset : gig1Step0 i x ⁻¹' (({0} : Set ℕ) ×ˢ A) =
        (fun q : ℝ × (ℕ → ℝ) => ((q.1, truncSeq i q.2), tailSeq i q.2)) ⁻¹'
          ({p : ℝ × (ℕ → ℝ) | resEpoch x p.2 (i + 1) ≤ p.1} ×ˢ {y | y 0 ∈ A}) := by
      ext q
      rw [mem_preimage, gig1Step0_mem_zero_iff]
      simp only [mem_preimage, mem_prod, mem_ofPred_eq, tailSeq, add_zero]
      rw [resEpoch_truncSeq_of_le le_rfl]
    have hΦ : Measurable fun q : ℝ × (ℕ → ℝ) => ((q.1, truncSeq i q.2), tailSeq i q.2) :=
      (measurable_fst.prodMk ((measurable_truncSeq i).comp measurable_snd)).prodMk
        ((measurable_tailSeq i).comp measurable_snd)
    have hS1 : MeasurableSet {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 (i + 1) ≤ p.1} :=
      measurableSet_le ((measurable_resEpoch (i + 1)).comp
        (measurable_const.prodMk measurable_snd)) measurable_fst
    have hS2 : MeasurableSet {y : ℕ → ℝ | y 0 ∈ A} := (measurable_pi_apply 0) hA
    have hT : Measurable fun q : ℝ × (ℕ → ℝ) => (q.1, truncSeq i q.2) :=
      measurable_fst.prodMk ((measurable_truncSeq i).comp measurable_snd)
    rw [hset, ← Measure.map_apply hΦ (hS1.prod hS2), prod_map_trunc_tail G H i,
      Measure.prod_prod, infinitePi_measure_head H hA, Measure.map_apply hT hS1]
    congr 1
    have hpre : (fun q : ℝ × (ℕ → ℝ) => (q.1, truncSeq i q.2)) ⁻¹'
        {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 (i + 1) ≤ p.1} =
          {q : ℝ × (ℕ → ℝ) | resEpoch x q.2 (i + 1) ≤ q.1} := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq]
      rw [resEpoch_truncSeq_of_le le_rfl]
    rw [hpre]
    have hk : ∀ k, gig1Lambda H G (k + i + 1) x univ =
        ∫⁻ q, (if resEpoch x q.2 (k + i + 1) ≤ q.1 ∧ q.1 < resEpoch x q.2 (k + i + 1 + 1)
          then (1 : ℝ≥0∞) else 0) ∂ρ := fun k => by
      change gig1LambdaMeasure H G (k + i + 1) x univ = _
      rw [gig1LambdaMeasure_apply H G _ x MeasurableSet.univ,
        ← lintegral_indicator_one (measurable_prodMk_left
          (measurableSet_gig1Set (k + i + 1) MeasurableSet.univ))]
      refine lintegral_congr fun q => ?_
      by_cases hq : resEpoch x q.2 (k + i + 1) ≤ q.1 ∧ q.1 < resEpoch x q.2 (k + i + 1 + 1)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hq),
          indicator_of_mem (show q ∈ Prod.mk x ⁻¹' gig1Set (k + i + 1) univ from
          ⟨hq.1, hq.2, mem_univ _⟩)]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hq),
          indicator_of_notMem (show q ∉ Prod.mk x ⁻¹' gig1Set (k + i + 1) univ from
          fun h => hq ⟨h.1, h.2.1⟩)]
    have hmk : ∀ k, AEMeasurable (fun q : ℝ × (ℕ → ℝ) =>
        if resEpoch x q.2 (k + i + 1) ≤ q.1 ∧ q.1 < resEpoch x q.2 (k + i + 1 + 1)
          then (1 : ℝ≥0∞) else 0) ρ := fun k => by
      have hZk : ∀ m, Measurable fun q : ℝ × (ℕ → ℝ) => resEpoch x q.2 m := fun m =>
        (measurable_resEpoch m).comp (measurable_const.prodMk measurable_snd)
      have hset : MeasurableSet {q : ℝ × (ℕ → ℝ) | resEpoch x q.2 (k + i + 1) ≤ q.1 ∧
          q.1 < resEpoch x q.2 (k + i + 1 + 1)} :=
        (measurableSet_le (hZk _) measurable_fst).inter (measurableSet_lt measurable_fst (hZk _))
      exact (Measurable.ite hset measurable_const measurable_const).aemeasurable
    rw [tsum_congr hk, ← lintegral_tsum hmk]
    have hS1' : MeasurableSet {q : ℝ × (ℕ → ℝ) | resEpoch x q.2 (i + 1) ≤ q.1} := hS1
    rw [← lintegral_indicator_one hS1']
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with q ⟨_, hdiv, hσ⟩
    rw [tsum_indicator_tail_eq hσ hdiv i]
    by_cases hq : resEpoch x q.2 (i + 1) ≤ q.1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hq), indicator_of_mem (show q ∈ {q : ℝ × (ℕ → ℝ) |
        resEpoch x q.2 (i + 1) ≤ q.1} from hq)]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hq),
        indicator_of_notMem (show q ∉ {q : ℝ × (ℕ → ℝ) |
        resEpoch x q.2 (i + 1) ≤ q.1} from hq)]
  · by_cases hji : j ≤ i + 1
    · rw [gig1Ladder, eq_3_40_mid _ _ hj hji x hA]
      change gig1LambdaMeasure H G (i + 1 - j) x A = _
      rw [gig1LambdaMeasure_apply H G _ x hA]
      refine measure_congr ?_
      filter_upwards [hgood] with q ⟨ht, hdiv, hσ⟩
      exact propext (gig1Step0_mem_iff hj hji ht hσ hdiv A).symm
    · rw [gig1Ladder, eq_3_40_up _ _ (by omega) x hA]
      symm
      convert measure_empty (μ := ρ)
      ext q
      simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro h
      have := gig1Step0_fst_le i x q
      omega

/-- The past at the `n`-th arrival (`n` interarrival times, `k + 1` services) is independent
of the future, which is again `G^{⊗ℕ} ⊗ H^{⊗ℕ}`. -/
theorem gig1_law_past_future (G H : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (n k : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)).map
        (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ((truncSeq n ω.1, truncSeq (k + 1) ω.2),
          (tailSeq n ω.1, tailSeq (k + 1) ω.2))) =
      (((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)).map
        (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => (truncSeq n ω.1, truncSeq (k + 1) ω.2))).prod
        ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)) := by
  set μG := Measure.infinitePi fun _ : ℕ => G
  set μH := Measure.infinitePi fun _ : ℕ => H
  have hf : Measurable fun a : ℕ → ℝ => (truncSeq n a, tailSeq n a) :=
    (measurable_truncSeq n).prodMk (measurable_tailSeq n)
  have hg : Measurable fun s : ℕ → ℝ => (truncSeq (k + 1) s, tailSeq (k + 1) s) :=
    (measurable_truncSeq (k + 1)).prodMk (measurable_tailSeq (k + 1))
  have hr : Measurable fun q : ((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
      ((q.1.1, q.2.1), (q.1.2, q.2.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  have hc : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ((truncSeq n ω.1, truncSeq (k + 1) ω.2),
      (tailSeq n ω.1, tailSeq (k + 1) ω.2))) =
      (fun q : ((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
        ((q.1.1, q.2.1), (q.1.2, q.2.2))) ∘
        Prod.map (fun a : ℕ → ℝ => (truncSeq n a, tailSeq n a))
          (fun s : ℕ → ℝ => (truncSeq (k + 1) s, tailSeq (k + 1) s)) := by
    funext ω
    rfl
  have hB : (μG.prod μH).map (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      (truncSeq n ω.1, truncSeq (k + 1) ω.2)) =
      (μG.map (truncSeq n)).prod (μH.map (truncSeq (k + 1))) := by
    rw [Measure.map_prod_map _ _ (measurable_truncSeq n) (measurable_truncSeq (k + 1))]
    rfl
  rw [hc, ← Measure.map_map hr (hf.prodMap hg), ← Measure.map_prod_map _ _ hf hg,
    infinitePi_map_trunc_tail, infinitePi_map_trunc_tail, map_prod_prod_rearrange, hB]

/-- Almost surely interarrival times are nonnegative and services are positive. -/
theorem ae_good_queue (G H : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure H]
    (hG0 : G (Iio 0) = 0) (hH0 : H (Iic 0) = 0) :
    ∀ᵐ ω ∂((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)),
      (∀ i, 0 ≤ ω.1 i) ∧ ∀ i, 0 < ω.2 i := by
  have h1 : ∀ᵐ a ∂(Measure.infinitePi fun _ : ℕ => G), ∀ i, 0 ≤ a i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {a : ℕ → ℝ | ¬ 0 ≤ a i} = (fun a : ℕ → ℝ => a i) ⁻¹' Iio 0 := by
      ext a
      simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.infinitePi_map_eval, hG0]
  have h2 : ∀ᵐ s ∂(Measure.infinitePi fun _ : ℕ => H), ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {s : ℕ → ℝ | ¬ 0 < s i} = (fun s : ℕ → ℝ => s i) ⁻¹' Iic 0 := by
      ext s
      simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iic,
      Measure.infinitePi_map_eval, hH0]
  have h1' := (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae h1
  have h2' := (measurePreserving_snd (μ := Measure.infinitePi fun _ : ℕ => G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae h2
  filter_upwards [h1', h2'] with ω hω1 hω2
  exact ⟨hω1, hω2⟩

/-- **The GI/G/1 queue embedded at arrivals is a Markov chain** (MT §3.5.4, p. 71). For
i.i.d. interarrival times `∼ G` on `[0, ∞)` and independent i.i.d. service times `∼ H` on
`(0, ∞)`, the process `Φₙ = (Nₙ, Rₙ)` is a Markov chain on `ℤ₊ × ℝ` with the ladder kernel
`gig1Ladder H G` and initial law `δ₀ ⊗ H`. -/
theorem gig1_isMarkovChain (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iic 0) = 0) (hG0 : G (Iio 0) = 0) :
    IsMarkovChain (gig1Ladder H G) ((Measure.dirac 0).prod H)
      ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H))
      (fun n ω => (queueN ω.1 ω.2 n, queueR ω.1 ω.2 n)) := by
  set P := (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)
  have hH0' : H (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hH0
  have hHpos : 0 < H (Ioi 0) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hH0, tsub_zero]
    exact one_pos
  have hgood := ae_good_queue G H hG0 hH0
  have hΨ : ∀ n, Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      (queueN ω.1 ω.2 n, queueR ω.1 ω.2 n) := fun n =>
    (measurable_queueN n).prodMk (measurable_queueR n)
  have h0 : P.map (fun ω => (queueN ω.1 ω.2 0, queueR ω.1 ω.2 0)) =
      (Measure.dirac 0).prod H := by
    have hae : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => (queueN ω.1 ω.2 0, queueR ω.1 ω.2 0)) =ᵐ[P]
        Prod.map (fun _ : ℕ → ℝ => (0 : ℕ)) (fun s : ℕ → ℝ => s 0) := by
      filter_upwards [hgood] with ω ⟨_, hs⟩
      have hc : inService ω.1 ω.2 0 = 0 := Nat.le_zero.1 (inService_spec hs 0).2.1
      rw [queueN_eq hs, queueR, hc]
      simp [depT, arrT, Prod.map]
    rw [Measure.map_congr hae, ← Measure.map_prod_map _ _ measurable_const
      (measurable_pi_apply 0), Measure.map_const, measure_univ, one_smul,
      Measure.infinitePi_map_eval]
  refine isMarkovChain_of_regeneration P P _ _ hΨ h0
    (fun n ω => inService ω.1 ω.2 n) (fun n k => measurableSet_inService_eq n k)
    (fun n k ω => (truncSeq n ω.1, truncSeq (k + 1) ω.2))
    (fun n k => ((measurable_truncSeq n).comp measurable_fst).prodMk
      ((measurable_truncSeq (k + 1)).comp measurable_snd))
    (fun n k ω => (tailSeq n ω.1, tailSeq (k + 1) ω.2))
    (fun n k => ((measurable_tailSeq n).comp measurable_fst).prodMk
      ((measurable_tailSeq (k + 1)).comp measurable_snd))
    (fun n k => gig1_law_past_future G H n k) (S := univ) MeasurableSet.univ
    (fun n k => ?_) measurable_gig1Step (fun n => ?_) _ (fun ix => ?_)
  · refine ⟨{b : (ℕ → ℝ) × (ℕ → ℝ) | arrT b.1 n < depT b.1 b.2 k ∧
        ∀ m < k, depT b.1 b.2 m ≤ arrT b.1 n}, ?_,
      fun b j => ((j : ℕ) - inService b.1 b.2 j,
        depT b.1 b.2 (inService b.1 b.2 j) - arrT b.1 j), ?_, ?_⟩
    · have hset : {b : (ℕ → ℝ) × (ℕ → ℝ) | ∀ m < k, depT b.1 b.2 m ≤ arrT b.1 n} =
          ⋂ m, ⋂ (_ : m < k), {b | depT b.1 b.2 m ≤ arrT b.1 n} := by
        ext b
        simp
      have hT2 : MeasurableSet {b : (ℕ → ℝ) × (ℕ → ℝ) | ∀ m < k,
          depT b.1 b.2 m ≤ arrT b.1 n} := by
        rw [hset]
        exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
          measurableSet_le (measurable_depT m) ((measurable_arrT n).comp measurable_fst)
      exact (measurableSet_lt ((measurable_arrT n).comp measurable_fst) (measurable_depT k)).inter
        hT2
    · refine measurable_pi_iff.2 fun j => ?_
      exact ((measurable_of_countable (fun l : ℕ => (j : ℕ) - l)).comp
        (measurable_inService j)).prodMk ((measurable_comp_index (measurable_inService j)
          (f := fun m ω => depT ω.1 ω.2 m) measurable_depT).sub
            ((measurable_arrT j).comp measurable_fst))
    · filter_upwards [hgood] with ω ⟨ha, hs⟩
      obtain ⟨a, s⟩ := ω
      simp only at ha hs
      refine ⟨?_, fun hk j => ?_⟩
      · rw [inService_eq_iff_truncSeq hs n k]
        simp only [mem_univ, and_true]
      · have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
        subst hk
        simp only
        rw [inService_truncSeq ha hs hj, queueN_eq hs, arrT_truncSeq hj,
          depT_truncSeq _ ((inService_spec hs (j : ℕ)).2.1.trans hj)
            (inService_mono ha hs hj)]
        rfl
  · filter_upwards [hgood] with ω ⟨ha, hs⟩
    exact gig1_step_eq ha hs n
  · obtain ⟨i, x⟩ := ix
    simp only [mem_univ, ofPred_true, cond_univ]
    rw [gig1Ladder_eq_map H G hH0' hHpos hG0 i x]
    have hm : Measurable fun y : (ℕ → ℝ) × (ℕ → ℝ) => (y.1 0, y.2) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
    have hlaw : P.map (fun y : (ℕ → ℝ) × (ℕ → ℝ) => (y.1 0, y.2)) =
        G.prod (Measure.infinitePi fun _ : ℕ => H) := by
      rw [show (fun y : (ℕ → ℝ) × (ℕ → ℝ) => (y.1 0, y.2)) =
          Prod.map (fun a : ℕ → ℝ => a 0) id from rfl,
        ← Measure.map_prod_map _ _ (measurable_pi_apply 0) measurable_id,
        Measure.infinitePi_map_eval, Measure.map_id]
    rw [← hlaw, Measure.map_map (measurable_gig1Step0 i x) hm]
    rfl

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Small sets for the GI/G/1 queue (MT Proposition 5.3.2, from the queue)

Meyn and Tweedie, §5.3.3, p. 108. Here `gig1Ladder H G` is the ladder kernel (3.40), (3.42)–(3.43)
of the embedded GI/G/1 process `Φₙ = (Nₙ, Rₙ)`. By `gig1_isMarkovChain` (copied from the
`TransitionProbabilities` project), it is the transition kernel of the queue built from its
primitives.

* `gig1Lambda_zero_univ`: `Λ₀(x, ℝ) = G(−∞, x)`, the probability that the next arrival comes
  before the service in progress ends.
* `gig1Lambda_tail_univ`: `Σ_{j ≥ 1} Λⱼ(x, ℝ) = G[x, ∞)`.
* `gig1Ladder_bottom`: the bottom rung, `P(0, x; {0} × A) = Λ₀*(x, A) = G[x, ∞) H(A)`, derived
  from (3.42)–(3.43).
* **Proposition 5.3.2** (`proposition_5_3_2_gig1`, p. 108): if `G(β, ∞) > 0`, then
  `{0} × (−∞, β]` is `ν₁`-small for the GI/G/1 ladder chain, with `ν₁ = G(β, ∞) H` on the bottom
  rung. `proposition_5_3_2_queue` combines this with `gig1_isMarkovChain`.
* `gig1Lambda_zero_counterexample`, `gig1Ladder_bottom_counterexample`: the book's
  `Λ₀(x, [0, ∞)) = G(−∞, x]` and `Λ₀*(x, ·) = H(·) G(x, ∞)` fail at atoms of `G`. With
  `G = H = δ₁` and `x = 1`: `Λ₀(1, ℝ) = 0 ≠ 1 = G(−∞, 1]` and `Λ₀*(1, ℝ) = 1 ≠ 0 = G(1, ∞)`.

**Corrections.** On p. 108, `G(−∞, x]` should be `G(−∞, x)` and `G(x, ∞)` should be `G[x, ∞)`. A
service ending exactly at the next arrival empties the queue. The conclusion of
Proposition 5.3.2 is unaffected, since `G[x, ∞) ≥ G(β, ∞)` for `x ≤ β`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable (H G : Measure ℝ) [IsProbabilityMeasure H]

/-- `Λ₀(x, ℝ) = G(−∞, x)` when interarrival times are nonnegative. -/
theorem gig1Lambda_zero_univ [IsProbabilityMeasure G] (hG0 : G (Iio 0) = 0) (x : ℝ) :
    gig1Lambda H G 0 x univ = G (Iio x) := by
  change gig1LambdaMeasure H G 0 x univ = _
  rw [gig1LambdaMeasure_apply H G 0 x MeasurableSet.univ]
  have hset : Prod.mk x ⁻¹' gig1Set 0 univ = Ico 0 x ×ˢ (univ : Set (ℕ → ℝ)) := by
    ext p
    simp [gig1Set, resEpoch]
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  refine le_antisymm (measure_mono Ico_subset_Iio_self) ?_
  calc G (Iio x) ≤ G (Ico 0 x ∪ Iio 0) := measure_mono fun t ht => by
        by_cases h : 0 ≤ t
        · exact Or.inl ⟨h, ht⟩
        · exact Or.inr (not_le.1 h)
    _ ≤ G (Ico 0 x) + G (Iio 0) := measure_union_le _ _
    _ = G (Ico 0 x) := by rw [hG0, add_zero]

/-- `Σ_{j ≥ 1} Λⱼ(x, ℝ) = G[x, ∞)`. -/
theorem gig1Lambda_tail_univ [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0)
    (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (x : ℝ) :
    ∑' j, gig1Lambda H G (j + 1) x univ = G (Ici x) := by
  have h := ennreal_sum_add_tsum_nat_add (fun k => gig1Lambda H G k x univ) 1
  rw [gig1Lambda_tsum_univ H G hH0 hHpos hG0 x, Finset.sum_range_one,
    gig1Lambda_zero_univ H G hG0 x] at h
  rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ← h,
    ENNReal.add_sub_cancel_left (measure_ne_top _ _)]

/-- **The bottom rung of the GI/G/1 ladder chain** (MT p. 108):
`P(0, x; {0} × A) = Λ₀*(x, A) = G[x, ∞) H(A)`. -/
theorem gig1Ladder_bottom [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0)
    (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    gig1Ladder H G (0, x) ({0} ×ˢ A) = G (Ici x) * H A := by
  rw [gig1Ladder, eq_3_40_zero _ _ 0 x hA]
  change ((∑' j, gig1Lambda H G (j + 0 + 1) x univ) • H) A = _
  rw [Measure.smul_apply, smul_eq_mul]
  simp only [add_zero]
  rw [gig1Lambda_tail_univ H G hH0 hHpos hG0 x]

/-- **Proposition 5.3.2** (MT p. 108), for the GI/G/1 ladder chain. If `G(β, ∞) > 0`, then
`{0} × (−∞, β]` is `ν₁`-small with `ν₁ = G(β, ∞) H` placed on the bottom rung. -/
theorem proposition_5_3_2_gig1 [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0)
    (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) {β : ℝ} (hG : 0 < G (Ioi β)) :
    IsSmallSet (gig1Ladder H G) 1 (G (Ioi β) • H.map (fun y => ((0 : ℕ), y)))
      ({0} ×ˢ Iic β) := by
  have hmk : Measurable fun y : ℝ => ((0 : ℕ), y) := measurable_const.prodMk measurable_id
  refine ⟨(measurableSet_singleton 0).prod measurableSet_Iic, one_pos, smul_measure_ne_zero ?_
    hG.ne', fun z hz => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (ℕ × ℝ) => μ univ) h0
    simp [Measure.map_apply hmk MeasurableSet.univ] at this
  obtain ⟨z1, z2⟩ := z
  obtain ⟨hz1, hz2⟩ := hz
  have hz1' : z1 = 0 := hz1
  subst hz1'
  rw [pow_one]
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmk hB]
  have hsec : MeasurableSet ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B) := hmk hB
  calc G (Ioi β) * H ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B)
      ≤ G (Ici z2) * H ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B) := by
        gcongr
        exact fun t ht => mem_Ici.2 (le_of_lt (lt_of_le_of_lt (mem_Iic.1 hz2) (mem_Ioi.1 ht)))
    _ = gig1Ladder H G (0, z2) ({0} ×ˢ ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B)) :=
        (gig1Ladder_bottom H G hH0 hHpos hG0 z2 hsec).symm
    _ ≤ gig1Ladder H G (0, z2) B := by
        refine measure_mono ?_
        rintro ⟨q1, q2⟩ ⟨hq1, hq2⟩
        have hq1' : q1 = 0 := hq1
        subst hq1'
        exact hq2

/-- **Proposition 5.3.2 for the queue** (MT p. 108). Suppose interarrival times are nonnegative,
service times positive, and `G(β, ∞) > 0`. Then the embedded GI/G/1 process `Φₙ = (Nₙ, Rₙ)`, built
from the primitives of the queue, is a Markov chain with kernel `gig1Ladder H G`, and
`{0} × (−∞, β]` is `G(β, ∞) H`-small for it. -/
theorem proposition_5_3_2_queue [IsProbabilityMeasure G] (hH0 : H (Iic 0) = 0)
    (hG0 : G (Iio 0) = 0) {β : ℝ} (hG : 0 < G (Ioi β)) :
    IsMarkovChain (gig1Ladder H G) ((Measure.dirac 0).prod H)
        ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H))
        (fun n ω => (queueN ω.1 ω.2 n, queueR ω.1 ω.2 n)) ∧
      IsSmallSet (gig1Ladder H G) 1 (G (Ioi β) • H.map (fun y => ((0 : ℕ), y)))
        ({0} ×ˢ Iic β) := by
  have hH0' : H (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hH0
  have hHpos : 0 < H (Ioi 0) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hH0, tsub_zero]
    exact one_pos
  exact ⟨gig1_isMarkovChain H G hH0 hG0, proposition_5_3_2_gig1 H G hH0' hHpos hG0 hG⟩

/-- **Correction to p. 108**: `Λ₀(x, [0, ∞)) = G(−∞, x]` fails at an atom of `G`. With
`G = H = δ₁` and `x = 1`, `Λ₀(1, ℝ) = 0` but `G(−∞, 1] = 1`. -/
theorem gig1Lambda_zero_counterexample :
    gig1Lambda (Measure.dirac 1) (Measure.dirac 1) 0 1 univ = 0 ∧
      (Measure.dirac (1 : ℝ)) (Iic 1) = 1 := by
  refine ⟨?_, by simp⟩
  rw [gig1Lambda_zero_univ _ _ (by simp) 1]
  simp

/-- **Correction to p. 108**: `Λ₀*(x, ·) = H(·) G(x, ∞)` fails at an atom of `G`. With
`G = H = δ₁` and `x = 1`, `P(0, 1; {0} × ℝ) = Λ₀*(1, ℝ) = 1`, but `G(1, ∞) H(ℝ) = 0`. -/
theorem gig1Ladder_bottom_counterexample :
    gig1Ladder (Measure.dirac 1) (Measure.dirac 1) (0, 1) ({0} ×ˢ univ) = 1 ∧
      (Measure.dirac (1 : ℝ)) (Ioi 1) * (Measure.dirac (1 : ℝ)) univ = 0 := by
  refine ⟨?_, by simp⟩
  rw [gig1Ladder_bottom _ _ (by simp) (by simp) (by simp) 1 MeasurableSet.univ]
  simp

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Controllability of the linear control model (MT §4.4.2)

Meyn and Tweedie, §4.4.2, pp. 90–91, and the linear algebra of §4.4.3, pp. 92–93, for the linear
control model LCM(F, G), `xₖ₊₁ = F xₖ + G uₖ₊₁`, with `F` an `n × n` and `G` an `n × p` matrix.

* `ctrbMap F G k`: the linear map `(u₁, …, uₖ) ↦ Σᵢ F^{k−1−i} G uᵢ₊₁`, and `ctrbMatrix F G k`
  the controllability matrix `C_k = [F^{k−1}G | ⋯ | FG | G]` (4.13), with
  `range_ctrbMatrix` (same range) and `rank_ctrbMatrix_eq_iff` (`rank C_k = n` iff the map is
  onto).
* `lcmTrajectory_eq_ctrbMap` (4.14): `x_k = F^k x₀ + C_k (u₁, …, u_k)`.
* `IsCtrbRank F G` (LCM3): `rank C_n = n`.
* **Proposition 4.4.1** (`proposition_4_4_1`, p. 91): the rank condition implies
  controllability, with every state reached from every initial condition in `n` steps.
* Cayley–Hamilton (p. 90): `range_ctrbMap_le_n`, the range of `C_k` is contained in that of
  `C_n` for every `k`; `isControllable_iff_rank` and `isControllable_iff_exists_rank`: `(F, G)`
  is controllable iff `rank C_n = n` iff `rank C_k = n` for some `k`.
* **Proposition 4.4.2** (`proposition_4_4_2`, p. 91): the state space form of AR(k) is
  controllable; `companion_pow_firstUnit_triangular` is the triangular structure of its
  controllability matrix, and `companion_eta_rec` the recursion `η_j = Σᵢ αᵢ η_{j−i}`.
* `gramian F G k = Σ_{i<k} F^i G Gᵀ (F^i)ᵀ` (the variance (4.16)), `gramian_eq` (`Σ_k = C_k C_kᵀ`),
  `rank_gramian` (`rank Σ_k = rank C_k`) and `isControllable_iff_gramian` (p. 93): `Σ_k` has full
  rank for some `k` iff `(F, G)` is controllable, and then for `k = n`.
* `ctrbSubspace_absorbing_step` (p. 93): the range `X₀` of `C_n` is invariant under every step
  `x ↦ F x + G w`.

**Corrections.** The controllability Gramian (4.17), `Σ_{i ≥ 0} F^i G Gᵀ (F^i)ᵀ`, need not
converge: for `F = G = 1` on `ℝ¹` every term is `1` (`gramian_series_counterexample`). Its role
is played by the finite sums `Σ_k`, which have full rank for some `k` iff `(F, G)` is
controllable (`isControllable_iff_gramian`).
-/

namespace MeynTweedie.PseudoAtoms

open Matrix
open scoped Matrix

variable {n p : ℕ}

/-- The linear map `(u₁, …, u_k) ↦ Σᵢ F^{k−1−i} G uᵢ₊₁` of (4.14). -/
noncomputable def ctrbMap (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    (Fin k → Fin p → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  ∑ i : Fin k, (F ^ (k - 1 - (i : ℕ)) * G).mulVecLin ∘ₗ LinearMap.proj i

/-- `C_k u = Σᵢ F^{k−1−i} G uᵢ`. -/
theorem ctrbMap_apply (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (u : Fin k → Fin p → ℝ) :
    ctrbMap F G k u = ∑ i : Fin k, (F ^ (k - 1 - (i : ℕ)) * G) *ᵥ u i := by
  simp [ctrbMap]

/-- The controllability matrix `C_k = [F^{k−1}G | ⋯ | FG | G]` (4.13), MT p. 90: column `(i, j)`
is column `j` of `F^{k−1−i} G`. -/
def ctrbMatrix (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin k × Fin p) ℝ :=
  Matrix.of fun r ij => (F ^ (k - 1 - (ij.1 : ℕ)) * G) r ij.2

/-- `C_k v` is `ctrbMap` applied to the blocks of `v`. -/
theorem ctrbMatrix_mulVec (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (v : Fin k × Fin p → ℝ) : ctrbMatrix F G k *ᵥ v = ctrbMap F G k fun i j => v (i, j) := by
  ext r
  rw [ctrbMap_apply, Finset.sum_apply]
  simp only [mulVec, dotProduct, ctrbMatrix, of_apply, Fintype.sum_prod_type]

/-- The controllability matrix and `ctrbMap` have the same range. -/
theorem range_ctrbMatrix (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    LinearMap.range (ctrbMatrix F G k).mulVecLin = LinearMap.range (ctrbMap F G k) := by
  ext x
  simp only [LinearMap.mem_range, mulVecLin_apply]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, (ctrbMatrix_mulVec F G k v).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨fun ij => u ij.1 ij.2, ctrbMatrix_mulVec F G k _⟩

/-- `rank C_k = n` iff every state is of the form `C_k u`. -/
theorem rank_ctrbMatrix_eq_iff (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : (ctrbMatrix F G k).rank = n ↔ LinearMap.range (ctrbMap F G k) = ⊤ := by
  rw [Matrix.rank, range_ctrbMatrix]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
  · intro h
    rw [h, finrank_top, Module.finrank_fin_fun]

/-- (4.14), MT p. 91: `x_k = F^k x₀ + C_k (u₁, …, u_k)`. -/
theorem lcmTrajectory_eq_ctrbMap (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x₀ : Fin n → ℝ) (u : Fin k → Fin p → ℝ) :
    lcmTrajectory F G k x₀ u = (F ^ k) *ᵥ x₀ + ctrbMap F G k u := by
  rw [lcmTrajectory_eq, ctrbMap_apply]

/-- The rank condition (LCM3), MT p. 90: the controllability matrix `C_n` has rank `n`. -/
def IsCtrbRank (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  (ctrbMatrix F G n).rank = n

/-- If `C_k` is onto, every state is reached from every initial condition in `k` steps. -/
theorem reach_of_range_eq_top {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    {k : ℕ} (h : LinearMap.range (ctrbMap F G k) = ⊤) (x₀ x : Fin n → ℝ) :
    ∃ u : Fin k → Fin p → ℝ, lcmTrajectory F G k x₀ u = x := by
  obtain ⟨u, hu⟩ := LinearMap.range_eq_top.1 h (x - (F ^ k) *ᵥ x₀)
  exact ⟨u, by rw [lcmTrajectory_eq_ctrbMap, hu, add_sub_cancel]⟩

/-- **Proposition 4.4.1** (MT p. 91): if `(F, G)` satisfies the rank condition (LCM3), LCM(F, G)
is controllable; indeed every state is reached from every initial condition in `n` steps. -/
theorem proposition_4_4_1 {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    (h : IsCtrbRank F G) :
    IsControllable F G ∧ ∀ x₀ x, ∃ u : Fin n → Fin p → ℝ, lcmTrajectory F G n x₀ u = x := by
  have h' := (rank_ctrbMatrix_eq_iff F G n).1 h
  exact ⟨fun x₀ x => ⟨n, reach_of_range_eq_top h' x₀ x⟩, reach_of_range_eq_top h'⟩

/-! ### Cayley–Hamilton -/

/-- `F^j G v` lies in the range of `C_k` for `j < k`. -/
theorem pow_mul_mulVec_mem_range (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {j k : ℕ} (hj : j < k) (v : Fin p → ℝ) :
    (F ^ j * G) *ᵥ v ∈ LinearMap.range (ctrbMap F G k) := by
  refine ⟨Pi.single (⟨k - 1 - j, by omega⟩ : Fin k) v, ?_⟩
  rw [ctrbMap_apply, Finset.sum_eq_single (⟨k - 1 - j, by omega⟩ : Fin k)]
  · have hj' : k - 1 - (k - 1 - j) = j := by omega
    rw [Pi.single_eq_same, Fin.val_mk, hj']
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mulVec_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Cayley–Hamilton: `F^n = −Σ_{i<n} cᵢ Fⁱ`, with `cᵢ` the coefficients of the characteristic
polynomial. -/
theorem pow_dim_eq_sum (F : Matrix (Fin n) (Fin n) ℝ) :
    F ^ n = -∑ i ∈ Finset.range n, F.charpoly.coeff i • F ^ i := by
  have h := Matrix.aeval_self_charpoly F
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ] at h
  have hc : F.charpoly.coeff n = 1 := by
    have := (Matrix.charpoly_monic F).coeff_natDegree
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [hc, one_smul] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Cayley–Hamilton (MT p. 90): `F^j G v` lies in the range of `C_n` for every `j`. -/
theorem pow_mul_mulVec_mem_range_n (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (j : ℕ) (v : Fin p → ℝ) : (F ^ j * G) *ᵥ v ∈ LinearMap.range (ctrbMap F G n) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact pow_mul_mulVec_mem_range F G hj v
    · have hFj : F ^ j = -∑ i ∈ Finset.range n, F.charpoly.coeff i • F ^ (j - n + i) := by
        rw [show j = (j - n) + n by omega, pow_add, pow_dim_eq_sum, mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, ← pow_add]
        congr 2
        omega
      rw [hFj, Matrix.neg_mul, neg_mulVec, Matrix.sum_mul, sum_mulVec]
      refine neg_mem (Submodule.sum_mem _ fun i hi => ?_)
      rw [smul_mul, smul_mulVec]
      exact Submodule.smul_mem _ _ (ih (j - n + i) (by rw [Finset.mem_range] at hi; omega))

/-- Cayley–Hamilton (MT p. 90): the range of `C_k` is contained in the range of `C_n`. -/
theorem range_ctrbMap_le_n (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : LinearMap.range (ctrbMap F G k) ≤ LinearMap.range (ctrbMap F G n) := by
  rintro x ⟨u, rfl⟩
  rw [ctrbMap_apply]
  exact Submodule.sum_mem _ fun i _ => pow_mul_mulVec_mem_range_n F G _ _

/-- The ranges of the `C_k` increase with `k`. -/
theorem range_ctrbMap_mono (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {k m : ℕ} (hkm : k ≤ m) :
    LinearMap.range (ctrbMap F G k) ≤ LinearMap.range (ctrbMap F G m) := by
  rintro x ⟨u, rfl⟩
  rw [ctrbMap_apply]
  exact Submodule.sum_mem _ fun i _ => pow_mul_mulVec_mem_range F G (by omega) _

/-- MT p. 90: `(F, G)` is controllable iff it satisfies the rank condition (LCM3). -/
theorem isControllable_iff_rank (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    IsControllable F G ↔ IsCtrbRank F G := by
  refine ⟨fun h => (rank_ctrbMatrix_eq_iff F G n).2 ?_, fun h => (proposition_4_4_1 h).1⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨m, u, hu⟩ := h 0 x
  rw [lcmTrajectory_eq_ctrbMap, mulVec_zero, zero_add] at hu
  exact range_ctrbMap_le_n F G m ⟨u, hu⟩

/-- MT pp. 90–91: `(F, G)` is controllable iff `rank C_k = n` for some `k`. -/
theorem isControllable_iff_exists_rank (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) :
    IsControllable F G ↔ ∃ k, (ctrbMatrix F G k).rank = n := by
  rw [isControllable_iff_rank]
  refine ⟨fun h => ⟨n, h⟩, fun ⟨k, hk⟩ => ?_⟩
  rw [IsCtrbRank, rank_ctrbMatrix_eq_iff]
  rw [rank_ctrbMatrix_eq_iff] at hk
  exact eq_top_iff.2 (hk.symm.le.trans (range_ctrbMap_le_n F G k))

/-- For a controllable pair, `C_k` is onto for every `k ≥ n`. -/
theorem range_ctrbMap_eq_top {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    (h : IsControllable F G) {k : ℕ} (hk : n ≤ k) : LinearMap.range (ctrbMap F G k) = ⊤ := by
  have h' := (rank_ctrbMatrix_eq_iff F G n).1 ((isControllable_iff_rank F G).1 h)
  exact eq_top_iff.2 (h'.symm.le.trans (range_ctrbMap_mono F G hk))

/-! ### The autoregression AR(k) (Proposition 4.4.2) -/

/-- The input `G = (1, 0, …, 0)ᵀ` maps `v` to `v₀ e₀`. -/
theorem firstUnit_mulVec {k : ℕ} (v : Fin 1 → ℝ) (i : Fin k) :
    (firstUnit k *ᵥ v) i = if (i : ℕ) = 0 then v 0 else 0 := by
  simp [firstUnit, mulVec, dotProduct]

/-- Below the first row the companion matrix shifts down: `(F w)ᵢ = wᵢ₋₁` for `i ≥ 1`. -/
theorem companion_mulVec_of_ne_zero {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ) (i : Fin k)
    (hi : (i : ℕ) ≠ 0) :
    (companion α *ᵥ w) i = w ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := by
  simp only [mulVec, dotProduct, companion, of_apply, hi, ite_false]
  rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin k)]
  · rw [ite_eq_left (by simp only; omega), one_mul]
  · intro j _ hj
    rw [ite_eq_right (fun hij => hj (Fin.ext (by simp only; omega))), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The first row of the companion matrix: `(F w)₀ = Σⱼ αⱼ wⱼ`. -/
theorem companion_mulVec_zero {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ) (i : Fin k)
    (hi : (i : ℕ) = 0) : (companion α *ᵥ w) i = ∑ j, α j * w j := by
  simp [mulVec, dotProduct, companion, hi]

/-- The vector `e₀ = G 1`. -/
def firstVec (k : ℕ) : Fin k → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- **The triangular structure** of the controllability matrix of AR(k) (MT p. 91):
`(Fʲ e₀)ᵢ = 0` for `i > j` and `(Fʲ e₀)ⱼ = 1`. -/
theorem companion_pow_firstUnit_triangular {k : ℕ} (α : Fin k → ℝ) (j : ℕ) (i : Fin k) :
    (j < i → (companion α ^ j *ᵥ firstVec k) i = 0) ∧
      ((i : ℕ) = j → (companion α ^ j *ᵥ firstVec k) i = 1) := by
  induction j generalizing i with
  | zero =>
    simp only [pow_zero, one_mulVec, firstVec]
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
    simp only [ite_eq_right_iff]
    intro h'
    omega
  | succ j ih =>
    have hi0 : ∀ hi : (i : ℕ) ≠ 0, (companion α ^ (j + 1) *ᵥ firstVec k) i =
        (companion α ^ j *ᵥ firstVec k) ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := fun hi => by
      rw [pow_succ', ← mulVec_mulVec, companion_mulVec_of_ne_zero α _ i hi]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hi0 (by omega)]
      exact (ih _).1 (by simp only; omega)
    · rw [hi0 (by omega)]
      exact (ih _).2 (by simp only; omega)

/-- The entries `η_m = (F^m e₀)₀` of the controllability matrix of AR(k) (MT p. 91). -/
noncomputable def companionEta {k : ℕ} (α : Fin k → ℝ) (m : ℕ) (h : 0 < k) : ℝ :=
  (companion α ^ m *ᵥ firstVec k) ⟨0, h⟩

/-- MT p. 91: `(F^j e₀)ᵢ = η_{j−i}` for `i ≤ j`, and the recursion
`η_{m+1} = Σᵢ αᵢ (F^m e₀)ᵢ`, i.e. `η_j = Σ_{i=1}^k αᵢ η_{j−i}` with `η_l = 0` for `l < 0`. -/
theorem companion_eta_rec {k : ℕ} (α : Fin k → ℝ) (h : 0 < k) :
    (∀ (j : ℕ) (i : Fin k), (i : ℕ) ≤ j →
      (companion α ^ j *ᵥ firstVec k) i = companionEta α (j - i) h) ∧
    (∀ m, companionEta α (m + 1) h = ∑ i : Fin k, α i *
      (if (i : ℕ) ≤ m then companionEta α (m - i) h else 0)) := by
  have hentry : ∀ (j : ℕ) (i : Fin k), (i : ℕ) ≤ j →
      (companion α ^ j *ᵥ firstVec k) i = companionEta α (j - i) h := by
    intro j
    induction j with
    | zero =>
      intro i hi
      have : i = ⟨0, h⟩ := Fin.ext (Nat.le_zero.1 hi)
      subst this
      rfl
    | succ j ih =>
      intro i hi
      by_cases hi0 : (i : ℕ) = 0
      · have : i = ⟨0, h⟩ := Fin.ext hi0
        subst this
        simp [companionEta]
      · rw [pow_succ', ← mulVec_mulVec, companion_mulVec_of_ne_zero α _ i hi0,
          ih _ (by simp only; omega)]
        congr 1
        simp only
        omega
  refine ⟨hentry, fun m => ?_⟩
  rw [companionEta, pow_succ', ← mulVec_mulVec, companion_mulVec_zero α _ _ rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  split_ifs with hi
  · exact hentry m i hi
  · exact (companion_pow_firstUnit_triangular α m i).1 (by omega)

/-- **Proposition 4.4.2** (MT p. 91): the linear control model of the AR(k) state space form
(2.1), with the companion matrix `F` and `G = (1, 0, …, 0)ᵀ`, is controllable. -/
theorem proposition_4_4_2 {k : ℕ} (α : Fin k → ℝ) :
    IsCtrbRank (companion α) (firstUnit k) ∧ IsControllable (companion α) (firstUnit k) := by
  have hR : LinearMap.range (ctrbMap (companion α) (firstUnit k) k) = ⊤ := by
    set R := LinearMap.range (ctrbMap (companion α) (firstUnit k) k)
    have hpow : ∀ j < k, companion α ^ j *ᵥ firstVec k ∈ R := fun j hj => by
      have := pow_mul_mulVec_mem_range (companion α) (firstUnit k) hj (fun _ => 1)
      rw [← mulVec_mulVec] at this
      convert this using 2
      ext i
      rw [firstUnit_mulVec]
      rfl
    have hsm : ∀ (l : Fin k) (c : ℝ), Pi.single l c = c • Pi.single l (1 : ℝ) := fun l c => by
      ext j
      by_cases hj : j = l
      · subst hj
        simp
      · simp [hj]
    have hsingle : ∀ m : ℕ, ∀ i : Fin k, (i : ℕ) = m → Pi.single i (1 : ℝ) ∈ R := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i hi
        have hv : companion α ^ m *ᵥ firstVec k ∈ R := hpow m (hi ▸ i.isLt)
        set w : Fin k → ℝ := companion α ^ m *ᵥ firstVec k - Pi.single i 1 with hwdef
        have hw : w ∈ R := by
          rw [← Finset.univ_sum_single w]
          refine Submodule.sum_mem _ fun l _ => ?_
          by_cases hl : (l : ℕ) < m
          · rw [hsm]
            exact Submodule.smul_mem _ _ (ih l hl l rfl)
          · have hw0 : w l = 0 := by
              rw [hwdef, Pi.sub_apply]
              rcases lt_or_eq_of_le (not_lt.1 hl) with h | h
              · have hli : l ≠ i := fun hli => by rw [hli] at h; omega
                rw [(companion_pow_firstUnit_triangular α m l).1 h, Pi.single_eq_of_ne hli,
                  sub_zero]
              · have hli : l = i := Fin.ext (by omega)
                rw [(companion_pow_firstUnit_triangular α m l).2 h.symm, hli, Pi.single_eq_same,
                  sub_self]
            rw [hw0, Pi.single_zero]
            exact zero_mem _
        have : Pi.single i (1 : ℝ) = companion α ^ m *ᵥ firstVec k - w := by
          rw [hwdef, sub_sub_cancel]
        rw [this]
        exact sub_mem hv hw
    refine eq_top_iff.2 fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (hsingle l l rfl)
  have h : IsCtrbRank (companion α) (firstUnit k) := (rank_ctrbMatrix_eq_iff _ _ k).2 hR
  exact ⟨h, (proposition_4_4_1 h).1⟩

/-! ### The controllability Gramian and the controllable subspace (§4.4.3) -/

/-- The variance (4.16) of `X_k` under (LSS3), `Σ_k = Σ_{i<k} F^i G Gᵀ (F^i)ᵀ` (MT p. 93). -/
def gramian (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.range k, F ^ i * G * Gᵀ * (F ^ i)ᵀ

/-- `Σ_k = C_k C_kᵀ`. -/
theorem gramian_eq (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    gramian F G k = ctrbMatrix F G k * (ctrbMatrix F G k)ᵀ := by
  have h1 : ctrbMatrix F G k * (ctrbMatrix F G k)ᵀ =
      ∑ i : Fin k, (F ^ (k - 1 - (i : ℕ)) * G) * (F ^ (k - 1 - (i : ℕ)) * G)ᵀ := by
    ext r s
    simp only [mul_apply, transpose_apply, ctrbMatrix, of_apply, Fintype.sum_prod_type,
      Matrix.sum_apply]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => (F ^ (k - 1 - i) * G) * (F ^ (k - 1 - i) * G)ᵀ),
    ← Finset.sum_range_reflect, gramian]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show k - 1 - (k - 1 - i) = i by omega, transpose_mul, ← Matrix.mul_assoc]

/-- `rank Σ_k = rank C_k`. -/
theorem rank_gramian (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    (gramian F G k).rank = (ctrbMatrix F G k).rank := by
  rw [gramian_eq, rank_self_mul_transpose]

/-- MT p. 93: the variance `Σ_k` of `X_k` has full rank `n` for some `k` iff `(F, G)` is
controllable, and then it has full rank for `k = n`. -/
theorem isControllable_iff_gramian (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) :
    (IsControllable F G ↔ ∃ k, (gramian F G k).rank = n) ∧
      (IsControllable F G → (gramian F G n).rank = n) := by
  simp_rw [rank_gramian]
  exact ⟨isControllable_iff_exists_rank F G, fun h => (isControllable_iff_rank F G).1 h⟩

/-- MT p. 93: the range `X₀` of `C_n` is invariant under every step: if `x ∈ X₀` then
`F x + G w ∈ X₀`. -/
theorem ctrbSubspace_absorbing_step (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {x : Fin n → ℝ} (hx : x ∈ LinearMap.range (ctrbMap F G n)) (w : Fin p → ℝ) :
    F *ᵥ x + G *ᵥ w ∈ LinearMap.range (ctrbMap F G n) := by
  obtain ⟨u, rfl⟩ := hx
  refine add_mem ?_ ?_
  · rw [ctrbMap_apply, mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
    exact pow_mul_mulVec_mem_range_n F G _ _
  · have := pow_mul_mulVec_mem_range_n F G 0 w
    rwa [pow_zero, Matrix.one_mul] at this

/-- **Correction to (4.17)** (MT p. 93): the Gramian series need not converge; for `F = G = 1`
on `ℝ¹` its terms are all `1`. -/
theorem gramian_series_counterexample :
    ¬ Summable fun i : ℕ => (1 : Matrix (Fin 1) (Fin 1) ℝ) ^ i * 1 *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * ((1 : Matrix (Fin 1) (Fin 1) ℝ) ^ i)ᵀ := by
  simp only [one_pow, transpose_one, Matrix.mul_one]
  rw [summable_const_iff]
  exact one_ne_zero

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# ψ-irreducible linear state space models (MT §4.4.3)

Meyn and Tweedie, §4.4.3, pp. 92–93: the linear state space model LSS(F, G),
`Xₖ₊₁ = F Xₖ + G Wₖ₊₁` on `ℝⁿ` (`lssMatrixKernel Γ F G`), with a disturbance law `Γ` on `ℝᵖ`.

The book assumes Gaussian noise (LSS3) and argues through the Gaussian density (4.18) of
`Pᵏ(x, ·)`. The proof here needs only that `Γ` is *equivalent* to Lebesgue measure (it has an
everywhere positive density): `Pᵏ(x, ·)` is the image of `Γ^{⊗k}` under the affine map
`u ↦ Fᵏx + C_k u`, and for `k ≥ n` the linear part is onto by controllability, so
`Pᵏ(x, ·)` is equivalent to Lebesgue measure (Mathlib's disintegration of Haar measure along
a surjective linear map).

* `pi_absolutelyContinuous`: `μ ≪ ν` implies `μ^{⊗k} ≪ ν^{⊗k}`.
* `ctrbLaw Γ F G k`: the law of `C_k (W₁, …, W_k)`; `lss_pow_eq`: `Pᵏ(x, ·)` is its translate
  by `Fᵏ x`; `ctrbLaw_equiv`, `lss_pow_equiv`: if `C_k` is onto, these laws are equivalent to
  Lebesgue measure.
* **Proposition 4.4.3** (`proposition_4_4_3`, p. 92), for a controllable pair and noise
  equivalent to Lebesgue measure: (i) the chain is `φ`-irreducible for every `φ ≪ μ_Leb`
  (`lss_isPhiIrreducible`); (ii) Lebesgue measure is a maximal irreducibility measure
  (`lss_isMaximalIrreducibility`); (iii) `A ⇝ B` for every compact `A` and every `B` with
  `μ_Leb(B) > 0` (`lss_unifAccessible`, via the lower semicontinuity `lss_lowerSemicontinuous`
  of `t ↦ ν(B − t)`).
* `proposition_4_4_3_gaussian`: the Gaussian case (LSS3), `W ∼ N(0, I)`.
* `ctrbSubspace_isAbsorbing` (p. 93): for any disturbance law, the range `X₀` of `C_n` is
  absorbing.

**Corrections.**
* The density (4.18) has the wrong normalising constant: it should be
  `(2π)^{−n/2} |Σ_k|^{−1/2}`, not `(2π|Σ_k|)^{−k/2}`. For `n = 1`, `k = 2`, `F = 0`, `G = 1`
  (so `Σ₂ = 1`) the book's function integrates to `(2π)^{−1/2} ≠ 1`, while the corrected one
  integrates to `1` (`density_4_18_counterexample`).

The moment formulas (4.15)–(4.16) and the Gaussian form of `Pᵏ(x, ·)` are not formalised: the
proof above does not use them. Their linear-algebra content, `Σ_k = C_k C_kᵀ` and
`rank Σ_k = rank C_k`, is in `LinearControllability`. The claim that the chain restricted to
`X₀` is again a controllable LSS model, and hence `μ_Leb`-irreducible on `X₀`, is not
formalised (it needs coordinates on the subspace).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal Matrix symmDiff

/-- `μ ≪ ν` implies `μ^{⊗k} ≪ ν^{⊗k}` on `Fin k → α`. -/
theorem pi_absolutelyContinuous {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0
    rw [← (e1.symm _).map_eq, ← (e2.symm _).map_eq]
    exact (h.prod ih).map (MeasurableEquiv.measurable _)

variable {n p : ℕ}

/-- `C_k` is measurable. -/
theorem measurable_ctrbMap (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : Measurable (ctrbMap F G k) :=
  (ctrbMap F G k).continuous_of_finiteDimensional.measurable

/-- The law of `C_k (W₁, …, W_k)` for i.i.d. `Wᵢ ∼ Γ`. -/
noncomputable def ctrbLaw (Γ : Measure (Fin p → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun _ : Fin k => Γ).map (ctrbMap F G k)

/-- `Pᵏ(x, ·)` is the law of `C_k (W₁, …, W_k)` translated by `Fᵏ x` ((4.14)). -/
theorem lss_pow_eq (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (x : Fin n → ℝ) :
    (lssMatrixKernel Γ F G ^ k) x = (ctrbLaw Γ F G k).map fun y => (F ^ k) *ᵥ x + y := by
  rw [lssMatrixKernel_pow_apply, ctrbLaw,
    Measure.map_map (measurable_const_add _) (measurable_ctrbMap F G k)]
  congr 1
  funext u
  simp [ctrbMap_apply]

/-- If `C_k` is onto and `Γ` is equivalent to Lebesgue measure, the law of
`C_k (W₁, …, W_k)` is equivalent to Lebesgue measure. -/
theorem ctrbLaw_equiv (Γ : Measure (Fin p → ℝ)) [SigmaFinite Γ] (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) {k : ℕ} (hsurj : LinearMap.range (ctrbMap F G k) = ⊤)
    (h1 : Γ ≪ volume) (h2 : volume ≪ Γ) :
    ctrbLaw Γ F G k ≪ volume ∧ volume ≪ ctrbLaw Γ F G k := by
  have hL : Function.Surjective (ctrbMap F G k) := LinearMap.range_eq_top.1 hsurj
  have hmL := measurable_ctrbMap F G k
  have key : ∀ S : Set (Fin n → ℝ), MeasurableSet S →
      (volume (ctrbMap F G k ⁻¹' S) = 0 ↔ volume S = 0) := fun S hS => by
    have := ae_comp_linearMap_mem_iff (ctrbMap F G k) (volume : Measure (Fin k → Fin p → ℝ))
      (volume : Measure (Fin n → ℝ)) hL hS.compl
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem]
    simpa using this
  have hpi1 : Measure.pi (fun _ : Fin k => Γ) ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h1 k
  have hpi2 : volume ≪ Measure.pi (fun _ : Fin k => Γ) := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h2 k
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [ctrbLaw, Measure.map_apply hmL hS]
    exact hpi1 ((key S hS).2 h0)
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [ctrbLaw, Measure.map_apply hmL hS] at h0
    exact (key S hS).1 (hpi2 h0)

/-- If `C_k` is onto and `Γ` is equivalent to Lebesgue measure, `Pᵏ(x, ·)` is equivalent to
Lebesgue measure for every `x`. -/
theorem lss_pow_equiv (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) {k : ℕ}
    (hsurj : LinearMap.range (ctrbMap F G k) = ⊤) (h1 : Γ ≪ volume) (h2 : volume ≪ Γ)
    (x : Fin n → ℝ) : (lssMatrixKernel Γ F G ^ k) x ≪ volume ∧
      volume ≪ (lssMatrixKernel Γ F G ^ k) x := by
  obtain ⟨hν1, hν2⟩ := ctrbLaw_equiv Γ F G hsurj h1 h2
  rw [lss_pow_eq]
  have hm := measurable_const_add ((F ^ k) *ᵥ x)
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [Measure.map_apply hm hS]
    exact hν1 (by rw [measure_preimage_add]; exact h0)
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [Measure.map_apply hm hS] at h0
    have := hν2 h0
    rwa [measure_preimage_add] at this

/-- **Proposition 4.4.3 (i)** (MT p. 92): for a controllable pair and a disturbance law
equivalent to Lebesgue measure, LSS(F, G) is `φ`-irreducible for every `φ ≪ μ_Leb`. -/
theorem lss_isPhiIrreducible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    [IsMarkovKernel (lssMatrixKernel Γ F G)] (hc : IsControllable F G) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) {φ : Measure (Fin n → ℝ)} (hφ : φ ≪ volume) :
    IsPhiIrreducible (lssMatrixKernel Γ F G) φ := by
  intro A hA hpos x
  have hA0 : volume A ≠ 0 := fun h => hpos.ne' (hφ h)
  obtain ⟨-, hvol⟩ := lss_pow_equiv Γ F G (k := n + 1) (range_ctrbMap_eq_top hc (by omega))
    h1 h2 x
  exact (hitProb_pos_iff _ hA x).2 ⟨n, pos_iff_ne_zero.2 fun h => hA0 (hvol h)⟩

/-- **Proposition 4.4.3 (ii)** (MT p. 92): Lebesgue measure is a maximal irreducibility measure
for LSS(F, G). -/
theorem lss_isMaximalIrreducibility (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    [IsMarkovKernel (lssMatrixKernel Γ F G)] (hc : IsControllable F G) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) :
    IsMaximalIrreducibility (lssMatrixKernel Γ F G) volume := by
  refine ⟨NeZero.ne _, lss_isPhiIrreducible Γ hc h1 h2 Measure.AbsolutelyContinuous.rfl,
    fun φ' hφ' => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
  by_contra hcon
  set P := lssMatrixKernel Γ F G
  have hreach : ∀ y, ∃ m, 0 < (P ^ (m + 1)) y A := fun y =>
    (hitProb_pos_iff P hA y).1 (hφ' A hA (pos_iff_ne_zero.2 hcon) y)
  have hcover : (⋃ m, {y | 0 < (P ^ (m + 1)) y A}) = univ :=
    eq_univ_of_forall fun y => mem_iUnion.2 (hreach y)
  have := isMarkovKernel_pow P (n + 1)
  have hpos : 0 < (P ^ (n + 1)) 0 (⋃ m, {y | 0 < (P ^ (m + 1)) y A}) := by
    rw [hcover, measure_univ]
    exact one_pos
  obtain ⟨m, hm⟩ := exists_measure_pos_of_iUnion hpos
  have h3 := (pow_add_pos_iff P (n + 1) (m + 1) 0 hA).2 hm
  obtain ⟨hac, -⟩ := lss_pow_equiv Γ F G (k := n + 1 + (m + 1))
    (range_ctrbMap_eq_top hc (by omega)) h1 h2 0
  exact h3.ne' (hac h0)

/-- The translations `y ↦ t + y` as a continuous family of continuous maps. -/
noncomputable def translateCM (n : ℕ) : (Fin n → ℝ) → C(Fin n → ℝ, Fin n → ℝ) :=
  ContinuousMap.curry ⟨fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2, continuous_add⟩

/-- For a finite measure `ν ≪ μ_Leb` and a set `B'` of finite Lebesgue measure,
`t ↦ ν(B' − t)` is lower semicontinuous. -/
theorem lss_lowerSemicontinuous {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]
    (hν : ν ≪ volume) {B' : Set (Fin n → ℝ)} (hB'm : MeasurableSet B')
    (hB'fin : volume B' ≠ ⊤) :
    LowerSemicontinuous fun t => ν (translateCM n t ⁻¹' B') := by
  intro t₀ y hy
  have hfg : Tendsto (translateCM n) (𝓝 t₀) (𝓝 (translateCM n t₀)) :=
    (ContinuousMap.curry _).continuous.tendsto t₀
  have hvol := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume) hfg
    (Eventually.of_forall fun t => measurePreserving_add_left volume t)
    (measurePreserving_add_left volume t₀) hB'm.nullMeasurableSet hB'fin
  have hνeq : volume.withDensity (ν.rnDeriv volume) = ν :=
    Measure.withDensity_rnDeriv_eq ν volume hν
  have hint : ∫⁻ x, ν.rnDeriv volume x ∂volume ≠ ⊤ := by
    rw [Measure.lintegral_rnDeriv hν]
    exact measure_ne_top ν univ
  have hνt : Tendsto (fun t => ν ((translateCM n t ⁻¹' B') ∆ (translateCM n t₀ ⁻¹' B')))
      (𝓝 t₀) (𝓝 0) := by
    refine (tendsto_setLIntegral_zero hint hvol).congr fun t => ?_
    rw [← withDensity_apply', hνeq]
  have hε : 0 < ν (translateCM n t₀ ⁻¹' B') - y := tsub_pos_of_lt hy
  filter_upwards [hνt.eventually (gt_mem_nhds hε)] with t ht
  have hle : ν (translateCM n t₀ ⁻¹' B') ≤
      ν (translateCM n t ⁻¹' B') + ν ((translateCM n t ⁻¹' B') ∆ (translateCM n t₀ ⁻¹' B')) := by
    have := le_measure_symmDiff (μ := ν) (s₁ := translateCM n t₀ ⁻¹' B')
      (s₂ := translateCM n t ⁻¹' B')
    rw [symmDiff_comm] at this
    rw [add_comm]
    exact tsub_le_iff_right.1 this
  by_contra hcon
  push Not at hcon
  have : ν (translateCM n t₀ ⁻¹' B') < ν (translateCM n t₀ ⁻¹' B') :=
    calc ν (translateCM n t₀ ⁻¹' B') ≤
          y + ν ((translateCM n t ⁻¹' B') ∆ (translateCM n t₀ ⁻¹' B')) :=
          hle.trans (add_le_add_left hcon _)
      _ < y + (ν (translateCM n t₀ ⁻¹' B') - y) := ENNReal.add_lt_add_left hy.ne_top ht
      _ = ν (translateCM n t₀ ⁻¹' B') := add_tsub_cancel_of_le hy.le
  exact lt_irrefl _ this

/-- **Proposition 4.4.3 (iii)** (MT p. 92): for every compact `A` and every `B` with
`μ_Leb(B) > 0`, `A ⇝ B`. -/
theorem lss_unifAccessible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    [IsMarkovKernel (lssMatrixKernel Γ F G)] (hc : IsControllable F G) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) {A B : Set (Fin n → ℝ)} (hA : IsCompact A) (hB : MeasurableSet B)
    (hBpos : 0 < volume B) : UnifAccessible (lssMatrixKernel Γ F G) A B := by
  have hsurj := range_ctrbMap_eq_top hc (k := n + 1) (by omega)
  obtain ⟨hν1, hν2⟩ := ctrbLaw_equiv Γ F G hsurj h1 h2
  have hνfin : IsFiniteMeasure (ctrbLaw Γ F G (n + 1)) := by
    rw [ctrbLaw]
    infer_instance
  obtain ⟨R, hR⟩ : ∃ R : ℕ, 0 < volume (B ∩ Metric.ball (0 : Fin n → ℝ) R) := by
    have hU : B = ⋃ R : ℕ, B ∩ Metric.ball (0 : Fin n → ℝ) R := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      refine ⟨fun hy => ?_, fun ⟨_, hy, _⟩ => hy⟩
      obtain ⟨R, hR⟩ := exists_nat_gt ‖y‖
      exact ⟨R, hy, hR⟩
    rw [hU] at hBpos
    exact exists_measure_pos_of_iUnion hBpos
  set B' := B ∩ Metric.ball (0 : Fin n → ℝ) R
  have hB'm : MeasurableSet B' := hB.inter measurableSet_ball
  have hB'fin : volume B' ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  set g : (Fin n → ℝ) → ℝ≥0∞ := fun t => ctrbLaw Γ F G (n + 1) (translateCM n t ⁻¹' B')
  have hgpos : ∀ t, 0 < g t := fun t => pos_iff_ne_zero.2 fun h0 => by
    have := hν2 h0
    change volume ((fun y => t + y) ⁻¹' B') = 0 at this
    rw [measure_preimage_add] at this
    exact hR.ne' this
  have hlsc := lss_lowerSemicontinuous hν1 hB'm hB'fin
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · exact ⟨1, one_pos, fun x hx => by rw [hAe] at hx; exact absurd hx (notMem_empty x)⟩
  have hT : IsCompact ((fun x => (F ^ (n + 1)) *ᵥ x) '' A) :=
    hA.image (Continuous.matrix_mulVec continuous_const continuous_id)
  obtain ⟨t₀, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hAne.image _) hT
    (hlsc.lowerSemicontinuousOn _)
  refine ⟨g t₀, hgpos t₀, fun x hx => ?_⟩
  calc g t₀ ≤ g ((F ^ (n + 1)) *ᵥ x) := isMinOn_iff.1 hmin _ (mem_image_of_mem _ hx)
    _ = (lssMatrixKernel Γ F G ^ (n + 1)) x B' := by
        rw [lss_pow_eq, Measure.map_apply (measurable_const_add _) hB'm]
        rfl
    _ ≤ (lssMatrixKernel Γ F G ^ (n + 1)) x B := measure_mono inter_subset_left
    _ ≤ hitProb (lssMatrixKernel Γ F G) B x := pow_le_hitProb _ hB n x

/-- **Proposition 4.4.3** (MT p. 92). If `(F, G)` is controllable and the disturbance law is
equivalent to Lebesgue measure (for instance Gaussian, `proposition_4_4_3_gaussian`), then
LSS(F, G) is `φ`-irreducible for every `φ` with a density, Lebesgue measure is a maximal
irreducibility measure, and `A ⇝ B` for every compact `A` and every `B` of positive Lebesgue
measure. -/
theorem proposition_4_4_3 (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    (h1 : Γ ≪ volume) (h2 : volume ≪ Γ) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel Γ F G),
      (∀ φ : Measure (Fin n → ℝ), φ ≪ volume → IsPhiIrreducible (lssMatrixKernel Γ F G) φ) ∧
      IsMaximalIrreducibility (lssMatrixKernel Γ F G) volume ∧
      ∀ A B : Set (Fin n → ℝ), IsCompact A → MeasurableSet B → 0 < volume B →
        UnifAccessible (lssMatrixKernel Γ F G) A B := by
  have hM := isMarkovKernel_lssMatrixKernel Γ F G
  exact ⟨hM, fun φ hφ => lss_isPhiIrreducible Γ hc h1 h2 hφ,
    lss_isMaximalIrreducibility Γ hc h1 h2,
    fun A B hA hB hBpos => lss_unifAccessible Γ hc h1 h2 hA hB hBpos⟩

/-- The standard Gaussian law `N(0, I)` on `ℝᵖ` (LSS3) is equivalent to Lebesgue measure. -/
theorem stdGaussian_equiv_volume (p : ℕ) :
    Measure.pi (fun _ : Fin p => gaussianReal 0 1) ≪ volume ∧
      volume ≪ Measure.pi (fun _ : Fin p => gaussianReal 0 1) := by
  rw [volume_pi]
  exact ⟨pi_absolutelyContinuous (gaussianReal_absolutelyContinuous 0 one_ne_zero) p,
    pi_absolutelyContinuous (gaussianReal_absolutelyContinuous' 0 one_ne_zero) p⟩

/-- **Proposition 4.4.3**, Gaussian case (MT p. 92): under (LSS1)–(LSS3), `W ∼ N(0, I)`, with
`(F, G)` controllable, the conclusions of Proposition 4.4.3 hold. -/
theorem proposition_4_4_3_gaussian {F : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G),
      (∀ φ : Measure (Fin n → ℝ), φ ≪ volume →
        IsPhiIrreducible (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) φ) ∧
      IsMaximalIrreducibility (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G)
        volume ∧
      ∀ A B : Set (Fin n → ℝ), IsCompact A → MeasurableSet B → 0 < volume B →
        UnifAccessible (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) A B :=
  proposition_4_4_3 _ hc (stdGaussian_equiv_volume p).1 (stdGaussian_equiv_volume p).2

/-- MT p. 93: for any disturbance law, the range `X₀` of the controllability matrix is an
absorbing set of LSS(F, G). -/
theorem ctrbSubspace_isAbsorbing (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    MeasurableSet (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ)) ∧
      IsAbsorbing (lssMatrixKernel Γ F G)
        (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ)) := by
  have hm : MeasurableSet (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ)) :=
    (Submodule.closed_of_finiteDimensional _).measurableSet
  refine ⟨hm, fun x hx => ?_⟩
  rw [lssMatrixKernel, recursionKernel_apply' Γ (measurable_lssMatrixStep F G) x hm]
  have : {w | F *ᵥ (x, w).1 + G *ᵥ (x, w).2 ∈
      (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ))} = univ :=
    eq_univ_of_forall fun w => ctrbSubspace_absorbing_step F G hx w
  rw [this, measure_univ]

/-- **Correction to (4.18)** (MT p. 93). For `n = 1`, `k = 2`, `F = 0`, `G = 1` the variance is
`Σ₂ = 1`, and the book's density `(2π|Σ_k|)^{−k/2} exp(−y²/2)` integrates to `(2π)^{−1/2} ≠ 1`;
with the correct constant `(2π)^{−n/2} |Σ_k|^{−1/2}` it integrates to `1`. -/
theorem density_4_18_counterexample :
    ∫ y : ℝ, (2 * Real.pi * 1)⁻¹ ^ ((2 : ℝ) / 2) * Real.exp (-(1 / 2) * y ^ 2) ≠ 1 ∧
      ∫ y : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * (1 : ℝ)⁻¹ * Real.exp (-(1 / 2) * y ^ 2) = 1 := by
  have hg : ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2) = Real.sqrt (2 * Real.pi) := by
    rw [integral_gaussian]
    congr 1
    field_simp
  have hpi : 0 < 2 * Real.pi := by positivity
  constructor
  · rw [integral_const_mul, hg, mul_one, div_self two_ne_zero, Real.rpow_one]
    intro h
    have hs : Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
      field_simp at h
      linarith
    have h2 := Real.sq_sqrt hpi.le
    rw [hs] at h2
    nlinarith [Real.two_le_pi]
  · rw [integral_const_mul, hg, inv_one, mul_one]
    exact inv_mul_cancel₀ (Real.sqrt_pos.2 hpi).ne'

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# ψ-irreducibility for random walk and scalar autoregressions (MT §4.3, §4.4.1)

Meyn and Tweedie, §4.3, pp. 87–89, and §4.4.1, pp. 89–90.

**General tools.**
* `exists_pow_pos_of_reach`: if `P(x, S) > 0` and every `y ∈ S` reaches `C`, so does `x`.
* `not_isPhiIrreducible_of_disjoint_absorbing`: a chain with two disjoint non-empty absorbing sets
  is `φ`-irreducible for no nonzero `φ` (Proposition 4.2.3 (i)).
* `isPhiIrreducible_of_skeleton`: irreducibility of a skeleton `Pᵐ`, `m ≥ 1`, passes to `P`.

**Random walk on a half line** (§4.3.1), `halfLineWalkKernel Γ` on `[0, ∞)`.
* `halfLine_pow_zero_ge`: if `Γ(−∞, −ε) ≥ δ`, then `Pⁿ⁺¹(x, {0}) ≥ δⁿ⁺¹` once `x < (n + 1)ε`.
* **Proposition 4.3.1** (`proposition_4_3_1`, p. 87): the walk is `δ₀`-irreducible iff
  `Γ(−∞, 0) > 0` (4.12), and then `C ⇝ {0}` for every compact `C`
  (`proposition_4_3_1_compact`).
* `halfLine_maximal` (p. 87): `ψ(A) = Σₙ Pⁿ(0, A) 2⁻ⁿ` is a maximal irreducibility measure.

**Unrestricted random walk** (§4.3.3) **and scalar AR(1)** (§4.4.1).
* `isPhiIrreducible_of_local_density`: a kernel with
  `Q(x, A) ≥ δ μ_Leb({w ∈ (−β, β) : αx + w ∈ A})`, `|α| ≤ 1`, is irreducible for Lebesgue
  measure on `(−β, β)`.
* `ar1_isPhiIrreducible_of_density`, `randomWalk_isPhiIrreducible_of_density` (p. 88–89): an
  increment law with a density `γ ≥ δ > 0` on `(−β, β)` makes AR(1) with `|α| ≤ 1`, and random
  walk, `μ_Leb`-irreducible on `(−β, β)`; `randomWalk_isPhiIrreducible_Icc`: in particular
  `μ_Leb` restricted to `C = [−β/2, β/2]` is an irreducibility measure, and
  `randomWalk_step_ge` (p. 89): `P(x, B) ≥ δ μ_Leb(B)` for `x ∈ C`, `B ⊆ C`.
* `randomWalk_isPhiIrreducible_of_convPow`: the same when only a convolution power `Γ^{m∗}` has
  such a density (a spread-out increment, (RW2)).
* `randomWalk_rational` (p. 89): increments concentrated on `ℚ` make every `x + ℚ` absorbing,
  uncountably many of them, and the walk is irreducible for no nonzero measure.
* `ar1_uniform_isPhiIrreducible` (p. 89): AR(1) with uniform noise on `[−1, 1]` and `|α| ≤ 1` is
  `μ_Leb`-irreducible on `[−1, 1]`; `ar1_abs_lt_step` and `ar1_explosive_not_irreducible`: if
  `|α| > 1` and the noise lies in `[−1, 1]`, `|Xₙ|` increases once it exceeds `(|α| − 1)⁻¹`,
  and the chain is irreducible for no nonzero measure.

**Corrections.** None. The storage-model discussion of §4.3.2 is the case of Proposition 4.3.1
with increment law the law of `Sₙ − Jₙ` (the reduction is in the `MarkovModels` project); the
content-dependent release discussion is informal and is not formalised. The AR(k) explosion and
stability heuristics of p. 90 (roots of `A(z)`) are not formalised; they are the subject of the
linear-model results of §4.4.3 and Chapter 7.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-! ### General tools -/

/-- If `P(x, S) > 0` and every `y ∈ S` reaches `C` (`Pⁿ(y, C) > 0` for some `n`), then `x`
reaches `C` in at least one step. -/
theorem exists_pow_pos_of_reach {X : Type*} [MeasurableSpace X] (P : Kernel X X) {C S : Set X}
    (hC : MeasurableSet C) {x : X} (hpos : 0 < P x S)
    (hreach : ∀ y ∈ S, ∃ n, 0 < (P ^ n) y C) : ∃ n, 0 < (P ^ (n + 1)) x C := by
  have hsub : S ⊆ ⋃ n, {y | 0 < (P ^ n) y C} := fun y hy => mem_iUnion.2 (hreach y hy)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hsub))
  refine ⟨n, ?_⟩
  rw [add_comm]
  exact (pow_add_pos_iff P 1 n x hC).2 (by rwa [pow_one])

/-- A chain with two disjoint non-empty absorbing sets is `φ`-irreducible for no nonzero `φ`: by
Proposition 4.2.3 (i) both sets would be full. -/
theorem not_isPhiIrreducible_of_disjoint_absorbing {X : Type*} [MeasurableSpace X]
    {P : Kernel X X} [IsMarkovKernel P] {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B)
    (hAabs : IsAbsorbing P A) (hBabs : IsAbsorbing P B) {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) : φ = 0 := by
  have h1 := proposition_4_2_3_i hφ hA hAne hAabs
  have h2 := proposition_4_2_3_i hφ hB hBne hBabs
  rw [← Measure.measure_univ_eq_zero]
  have : (univ : Set X) = Aᶜ ∪ Bᶜ := by
    rw [← compl_inter, hAB.inter_eq, compl_empty]
  rw [this]
  exact measure_union_null h1 h2

/-- Irreducibility of a skeleton `Pᵐ`, `m ≥ 1`, gives irreducibility of `P` (for the same
measure). -/
theorem isPhiIrreducible_of_skeleton {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m) [IsMarkovKernel (P ^ m)] {φ : Measure X}
    (h : IsPhiIrreducible (P ^ m) φ) : IsPhiIrreducible P φ := by
  intro A hA hpos x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff (P ^ m) hA x).1 (h A hA hpos x)
  refine (hitProb_pos_iff P hA x).2 ⟨m * (n + 1) - 1, ?_⟩
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity)), pow_mul]
  exact hn

/-! ### Random walk on a half line (§4.3.1) -/

/-- MT p. 87: if `Γ(−∞, −ε) ≥ δ`, then `Pⁿ⁺¹(x, {0}) ≥ δⁿ⁺¹` whenever `x < (n + 1)ε`. -/
theorem halfLine_pow_zero_ge (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {ε : ℝ} (hε : 0 < ε)
    {δ : ℝ≥0∞} (hδ : δ ≤ Γ (Iio (-ε))) (n : ℕ) (x : ℝ≥0) (hx : (x : ℝ) < (n + 1) * ε) :
    δ ^ (n + 1) ≤ (halfLineWalkKernel Γ ^ (n + 1)) x {0} := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  induction n generalizing x with
  | zero =>
    rw [zero_add, pow_one, pow_one, halfLineWalkKernel_apply_zero]
    refine hδ.trans (measure_mono fun w hw => ?_)
    simp only [mem_Iio, mem_Iic] at hw ⊢
    simp at hx
    linarith
  | succ n ih =>
    set S : Set ℝ≥0 := {y | (y : ℝ) < (n + 1) * ε}
    have hS : MeasurableSet S := measurableSet_lt measurable_coe_nnreal_real measurable_const
    have hPS : δ ≤ halfLineWalkKernel Γ x S := by
      rw [halfLineWalkKernel_apply' Γ x hS]
      refine hδ.trans (measure_mono fun w hw => ?_)
      simp only [mem_Iio, mem_ofPred_eq, S, Real.coe_toNNReal'] at hw ⊢
      push_cast at hx
      refine max_lt (by linarith) (by positivity)
    rw [pow_succ_apply _ (n + 1) x (measurableSet_singleton 0), pow_succ]
    calc δ ^ (n + 1) * δ ≤ δ ^ (n + 1) * halfLineWalkKernel Γ x S := by gcongr
      _ = ∫⁻ _ in S, δ ^ (n + 1) ∂halfLineWalkKernel Γ x := by rw [setLIntegral_const]
      _ ≤ ∫⁻ y in S, (halfLineWalkKernel Γ ^ (n + 1)) y {0} ∂halfLineWalkKernel Γ x :=
          setLIntegral_mono (Kernel.measurable_coe _ (measurableSet_singleton 0))
            fun y hy => ih y hy
      _ ≤ _ := setLIntegral_le_lintegral _ _

/-- If `Γ(−∞, 0) > 0` then `Γ(−∞, −ε) > 0` for some `ε > 0`. -/
theorem exists_Iio_neg_pos (Γ : Measure ℝ) (h : 0 < Γ (Iio 0)) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < Γ (Iio (-ε)) := by
  have hU : Iio (0 : ℝ) = ⋃ k : ℕ, Iio (-(1 / ((k : ℝ) + 1))) := by
    ext w
    simp only [mem_Iio, mem_iUnion]
    constructor
    · intro hw
      obtain ⟨k, hk⟩ := exists_nat_gt (-1 / w)
      refine ⟨k, ?_⟩
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      rw [div_lt_iff_of_neg hw] at hk
      have : 1 / ((k : ℝ) + 1) < -w := by rw [div_lt_iff₀ hk1]; nlinarith
      linarith
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hU] at h
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion h
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- If `Γ(−∞, 0) = 0`, a reflected walk started at `x > 0` never reaches `{0}`: the set
`[x, ∞)` is absorbing. -/
theorem halfLine_hitProb_zero_eq_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsMarkovKernel (halfLineWalkKernel Γ)] (h : Γ (Iio 0) = 0) {x : ℝ≥0} (hx : 0 < x) :
    hitProb (halfLineWalkKernel Γ) {0} x = 0 := by
  have hAbs : IsAbsorbing (halfLineWalkKernel Γ) (Ici x) := by
    intro y hy
    rw [← prob_compl_eq_zero_iff measurableSet_Ici, compl_Ici,
      halfLineWalkKernel_apply' Γ y measurableSet_Iio]
    refine measure_mono_null (fun w hw => ?_) h
    simp only [mem_Ici, mem_ofPred_eq, mem_Iio] at hy hw ⊢
    by_contra hw0
    push Not at hw0
    have : (x : ℝ) ≤ (Real.toNNReal ((y : ℝ) + w) : ℝ) := by
      rw [Real.coe_toNNReal']
      exact le_max_of_le_left (by have : (x : ℝ) ≤ y := hy; linarith)
    exact absurd hw (not_lt.2 (by exact_mod_cast this))
  exact hAbs.hitProb_eq_zero measurableSet_Ici
    (Set.disjoint_left.2 fun y hy h0 => by
      rw [mem_singleton_iff.1 h0, mem_Ici] at hy
      exact absurd hy (not_le.2 hx)) (mem_Ici.2 le_rfl)

/-- **Proposition 4.3.1** (MT p. 87): random walk on a half line is `φ`-irreducible with
`φ = δ₀` (`φ(0, ∞) = 0`, `φ{0} = 1`) iff `Γ(−∞, 0) > 0` (4.12). -/
theorem proposition_4_3_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ),
      (IsPhiIrreducible (halfLineWalkKernel Γ) (Measure.dirac 0) ↔ 0 < Γ (Iio 0)) := by
  have hM := isMarkovKernel_halfLineWalkKernel Γ
  refine ⟨hM, ?_⟩
  rw [isPhiIrreducible_dirac_iff]
  constructor
  · intro h
    by_contra h0
    have h0' : Γ (Iio 0) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
    have := h 1
    rw [halfLine_hitProb_zero_eq_zero Γ h0' one_pos] at this
    exact lt_irrefl _ this
  · intro h x
    obtain ⟨ε, hε, hΓε⟩ := exists_Iio_neg_pos Γ h
    obtain ⟨n, hn⟩ := exists_nat_gt ((x : ℝ) / ε)
    refine (hitProb_pos_iff _ (measurableSet_singleton 0) x).2 ⟨n, ?_⟩
    refine (ENNReal.pow_pos hΓε _).trans_le (halfLine_pow_zero_ge Γ hε le_rfl n x ?_)
    rw [div_lt_iff₀ hε] at hn
    nlinarith

/-- **Proposition 4.3.1**, second part (MT p. 87): if `Γ(−∞, 0) > 0`, then `C ⇝ {0}` for every
compact `C`. -/
theorem proposition_4_3_1_compact (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (h : 0 < Γ (Iio 0)) {C : Set ℝ≥0} (hC : IsCompact C) :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ), UnifAccessible (halfLineWalkKernel Γ) C {0} := by
  have hM := isMarkovKernel_halfLineWalkKernel Γ
  refine ⟨hM, ?_⟩
  obtain ⟨ε, hε, hΓε⟩ := exists_Iio_neg_pos Γ h
  obtain ⟨c, hc⟩ := hC.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt ((c : ℝ) / ε)
  refine ⟨Γ (Iio (-ε)) ^ (n + 1), ENNReal.pow_pos hΓε _, fun x hx => ?_⟩
  refine (halfLine_pow_zero_ge Γ hε le_rfl n x ?_).trans
    (pow_le_hitProb _ (measurableSet_singleton 0) n x)
  have hxc : (x : ℝ) ≤ c := by exact_mod_cast hc hx
  rw [div_lt_iff₀ hε] at hn
  nlinarith

/-- MT p. 87: if `Γ(−∞, 0) > 0`, the measure `ψ(A) = Σₙ Pⁿ(0, A) 2⁻ⁿ`, i.e. `2 K_{a_{1/2}}(0, ·)`,
is a maximal irreducibility measure for random walk on a half line. -/
theorem halfLine_maximal (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : 0 < Γ (Iio 0)) :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ),
      IsMaximalIrreducibility (halfLineWalkKernel Γ)
        ((2 : ℝ≥0∞) • resolventHalf (halfLineWalkKernel Γ) 0) ∧
      ∀ A, MeasurableSet A → ((2 : ℝ≥0∞) • resolventHalf (halfLineWalkKernel Γ) 0) A =
        ∑' n, (halfLineWalkKernel Γ ^ n) 0 A * 2⁻¹ ^ n := by
  obtain ⟨hM, hirr⟩ := proposition_4_3_1 Γ
  refine ⟨hM, ?_, fun A hA => ?_⟩
  · have hmax := isMaximalIrreducibility_maxIrrMeasure _ (hirr.2 h) (Measure.dirac_ne_zero)
    rw [maxIrrMeasure, dirac_kernel] at hmax
    exact hmax.of_equiv (Measure.absolutelyContinuous_smul two_ne_zero)
      Measure.smul_absolutelyContinuous
  · rw [Measure.smul_apply, resolventHalf_apply _ 0 hA, smul_eq_mul, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun n => ?_
    have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc 2 * ((halfLineWalkKernel Γ ^ n) 0 A * 2⁻¹ ^ (n + 1))
        = (halfLineWalkKernel Γ ^ n) 0 A * 2⁻¹ ^ n * (2 * 2⁻¹) := by ring
      _ = _ := by rw [h2, mul_one]

/-! ### Kernels with a local density (§4.3.3, §4.4.1) -/

/-- **Irreducibility from a local density** (MT pp. 88–89). Let `Q` be a transition kernel on
`ℝ` with `Q(x, A) ≥ δ μ_Leb{w ∈ (−β, β) : αx + w ∈ A}` for all `x` and `A`, where `|α| ≤ 1`,
`β > 0`, `δ > 0`. Then `Q` is irreducible for Lebesgue measure on `(−β, β)`. This covers the
unrestricted random walk (`α = 1`) and the scalar AR(1) model with `|α| ≤ 1`. -/
theorem isPhiIrreducible_of_local_density (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {α β : ℝ}
    {δ : ℝ≥0∞} (hα : |α| ≤ 1) (hβ : 0 < β) (hδ : δ ≠ 0)
    (hQ : ∀ x A, MeasurableSet A → δ * volume ({w | α * x + w ∈ A} ∩ Ioo (-β) β) ≤ Q x A) :
    IsPhiIrreducible Q (volume.restrict (Ioo (-β) β)) := by
  have hax : ∀ x : ℝ, |α * x| ≤ |x| := fun x => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hα
  set C : Set ℝ := Ioo (-(β / 2)) (β / 2) with hCdef
  have hCm : MeasurableSet C := measurableSet_Ioo
  -- one step from a point with `|αx| < β/2` lands in `C`
  have hstepC : ∀ x : ℝ, |α * x| < β / 2 → 0 < Q x C := fun x hx => by
    rw [abs_lt] at hx
    refine lt_of_lt_of_le ?_ (hQ x C hCm)
    refine ENNReal.mul_pos hδ (ne_of_gt ?_)
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (-(β / 2) - α * x) (β / 2 - α * x))
      fun w hw => ?_)
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, hCdef] at hw ⊢
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- every state reaches `C`
  have hreachk : ∀ k : ℕ, ∀ x : ℝ, |x| < (k + 1) * (β / 2) → ∃ n, 0 < (Q ^ n) x C := by
    intro k
    induction k with
    | zero =>
      intro x hx
      refine ⟨0, ?_⟩
      rw [pow_zero_apply, Measure.dirac_apply_of_mem]
      · exact one_pos
      · simp only [CharP.cast_eq_zero, zero_add, one_mul] at hx
        exact abs_lt.1 hx
    | succ k ih =>
      intro x hx
      by_cases h1 : |α * x| < β / 2
      · exact ⟨1, by rw [pow_one]; exact hstepC x h1⟩
      · push Not at h1
        set S : Set ℝ := {y | |y| < (k + 1) * (β / 2)}
        have hS : MeasurableSet S := measurableSet_lt continuous_abs.measurable measurable_const
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hxle := hax x
        push_cast at hx
        have hpos : 0 < Q x S := by
          refine lt_of_lt_of_le ?_ (hQ x S hS)
          refine ENNReal.mul_pos hδ (ne_of_gt ?_)
          rcases le_abs'.1 h1 with h2 | h2
          · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (β / 2) β) fun w hw => ?_)
            · rw [Real.volume_Ioo]
              exact ENNReal.ofReal_pos.2 (by linarith)
            · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, S] at hw ⊢
              have := neg_abs_le (α * x)
              have := neg_abs_le x
              refine ⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, by linarith, hw.2⟩
          · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (-β) (-(β / 2))) fun w hw => ?_)
            · rw [Real.volume_Ioo]
              exact ENNReal.ofReal_pos.2 (by linarith)
            · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, S] at hw ⊢
              have := le_abs_self (α * x)
              have := le_abs_self x
              refine ⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, hw.1, by linarith⟩
        obtain ⟨n, hn⟩ := exists_pow_pos_of_reach Q hCm hpos fun y hy => ih y hy
        exact ⟨n + 1, hn⟩
  have hreach : ∀ x : ℝ, ∃ n, 0 < (Q ^ n) x C := fun x => by
    obtain ⟨k, hk⟩ := exists_nat_gt (|x| / (β / 2))
    refine hreachk k x ?_
    rw [div_lt_iff₀ (by linarith)] at hk
    nlinarith
  -- irreducibility
  intro A hA hpos x
  rw [Measure.restrict_apply hA] at hpos
  have hsub : A ∩ Ioo (-β) β ⊆
      ⋃ k : ℕ, A ∩ Ioo (-β + β / ((k : ℝ) + 2)) (β - β / ((k : ℝ) + 2)) := by
    rintro w ⟨hwA, hw⟩
    rw [mem_Ioo] at hw
    have hd : 0 < β - |w| := by rw [sub_pos, abs_lt]; exact ⟨by linarith, hw.2⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (β / (β - |w|))
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : β / ((k : ℝ) + 2) < β - |w| := by
      rw [div_lt_iff₀ hk2]
      rw [div_lt_iff₀ hd] at hk
      nlinarith
    refine mem_iUnion.2 ⟨k, hwA, ?_, ?_⟩ <;>
      [linarith [neg_abs_le w]; linarith [le_abs_self w]]
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hsub))
  set η : ℝ := β / ((k : ℝ) + 2) with hηdef
  have hk2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hη : 0 < η := by positivity
  have hη2 : η ≤ β / 2 := div_le_div_of_nonneg_left hβ.le two_pos hk2
  set A' := A ∩ Ioo (-β + η) (β - η)
  set B : Set ℝ := Ioo (-η) η
  have hBm : MeasurableSet B := measurableSet_Ioo
  -- from `B` the set `A` is reached in one step
  have hBA : B ⊆ {y | 0 < (Q ^ 1) y A} := fun y hy => by
    rw [mem_ofPred_eq, pow_one]
    have hy' : |α * y| < η := (hax y).trans_lt (abs_lt.2 hy)
    rw [abs_lt] at hy'
    refine lt_of_lt_of_le ?_ (hQ y A hA)
    refine ENNReal.mul_pos hδ (ne_of_gt (hk.trans_le ?_))
    calc volume A' = volume ((fun w => α * y + w) ⁻¹' A') := (measure_preimage_add _ _ _).symm
      _ ≤ _ := measure_mono fun w hw => by
        simp only [mem_preimage, mem_inter_iff, mem_Ioo, A'] at hw
        exact ⟨hw.1, by linarith, by linarith⟩
  -- from `C` the set `B` is reached in one step
  have hCB : C ⊆ {y | 0 < (Q ^ 1) y B} := fun y hy => by
    rw [mem_ofPred_eq, pow_one]
    have hy' : |α * y| < β / 2 := (hax y).trans_lt (abs_lt.2 hy)
    rw [abs_lt] at hy'
    refine lt_of_lt_of_le ?_ (hQ y B hBm)
    refine ENNReal.mul_pos hδ (ne_of_gt ?_)
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (-η - α * y) (η - α * y)) fun w hw => ?_)
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, B] at hw ⊢
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨n, hn⟩ := hreach x
  have h1 : 0 < (Q ^ (n + 1)) x B :=
    (pow_add_pos_iff Q n 1 x hBm).2 (hn.trans_le (measure_mono hCB))
  have h2 : 0 < (Q ^ (n + 1 + 1)) x A :=
    (pow_add_pos_iff Q (n + 1) 1 x hA).2 (h1.trans_le (measure_mono hBA))
  exact (hitProb_pos_iff Q hA x).2 ⟨n + 1, h2⟩

/-- A density `γ ≥ δ` on `(−β, β)` below the law `Γ` gives `Γ(A) ≥ δ μ_Leb(A ∩ (−β, β))`. -/
theorem le_of_density {Γ : Measure ℝ} {γ : ℝ → ℝ≥0∞} {β : ℝ} {δ : ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x)
    {A : Set ℝ} (hA : MeasurableSet A) : δ * volume (A ∩ Ioo (-β) β) ≤ Γ A := by
  calc δ * volume (A ∩ Ioo (-β) β) = ∫⁻ _ in A ∩ Ioo (-β) β, δ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in A ∩ Ioo (-β) β, γ x :=
        setLIntegral_mono' (hA.inter measurableSet_Ioo) fun x hx => hγδ x hx.2
    _ ≤ ∫⁻ x in A, γ x := lintegral_mono_set inter_subset_left
    _ ≤ Γ A := hγ A hA

/-- MT §4.4.1, p. 89: the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` with `|α| ≤ 1` and an innovation law
with a density `γ ≥ δ > 0` on `(−β, β)` is irreducible for Lebesgue measure on `(−β, β)`. -/
theorem ar1_isPhiIrreducible_of_density (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α β : ℝ}
    {δ : ℝ≥0∞} (hα : |α| ≤ 1) (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (ar1Kernel Γ α),
      IsPhiIrreducible (ar1Kernel Γ α) (volume.restrict (Ioo (-β) β)) := by
  have hM := isMarkovKernel_ar1Kernel Γ α
  refine ⟨hM, isPhiIrreducible_of_local_density _ hα hβ hδ fun x A hA => ?_⟩
  rw [ar1Kernel_apply' Γ α x hA]
  exact le_of_density hγ hγδ ((measurable_const_add (α * x)) hA)

/-- MT §4.3.3, pp. 88–89: random walk on `ℝ` whose increment law has a density `γ ≥ δ > 0` on
`(−β, β)` is irreducible for Lebesgue measure on `(−β, β)`. -/
theorem randomWalk_isPhiIrreducible_of_density (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ}
    {δ : ℝ≥0∞} (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      IsPhiIrreducible (randomWalkKernel Γ) (volume.restrict (Ioo (-β) β)) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  refine ⟨hM, isPhiIrreducible_of_local_density _ (α := 1) (by simp) hβ hδ fun x A hA => ?_⟩
  rw [randomWalkKernel_apply' Γ x hA]
  simp only [one_mul]
  exact le_of_density hγ hγδ ((measurable_const_add x) hA)

/-- MT p. 89: in particular Lebesgue measure restricted to `C = [−β/2, β/2]` is an irreducibility
measure for the random walk. -/
theorem randomWalk_isPhiIrreducible_Icc (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ}
    {δ : ℝ≥0∞} (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      IsPhiIrreducible (randomWalkKernel Γ) (volume.restrict (Icc (-(β / 2)) (β / 2))) := by
  obtain ⟨hM, h⟩ := randomWalk_isPhiIrreducible_of_density Γ hβ hδ hγ hγδ
  refine ⟨hM, h.mono (Measure.absolutelyContinuous_of_le (Measure.restrict_mono ?_ le_rfl))⟩
  intro w hw
  rw [mem_Icc] at hw
  rw [mem_Ioo]
  constructor <;> linarith

/-- MT p. 89: for `x ∈ C = [−β/2, β/2]` and `B ⊆ C`, `P(x, B) ≥ δ μ_Leb(B)`. -/
theorem randomWalk_step_ge (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ} {δ : ℝ≥0∞}
    {γ : ℝ → ℝ≥0∞} (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A)
    (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) {x : ℝ} (hx : x ∈ Icc (-(β / 2)) (β / 2)) {B : Set ℝ}
    (hB : MeasurableSet B) (hBC : B ⊆ Icc (-(β / 2)) (β / 2)) :
    δ * volume B ≤ randomWalkKernel Γ x B := by
  rw [randomWalkKernel_apply' Γ x hB]
  refine le_trans (mul_le_mul_right ?_ δ) (le_of_density hγ hγδ ((measurable_const_add x) hB))
  rw [mem_Icc] at hx
  calc volume B = volume ((fun w => x + w) ⁻¹' B) := (measure_preimage_add _ _ _).symm
    _ ≤ volume ({w | x + w ∈ B} ∩ Ioo (-β) β ∪ {-β, β}) := measure_mono fun w hw => by
        have hb : x + w ∈ Icc (-(β / 2)) (β / 2) := hBC hw
        rw [mem_Icc] at hb
        by_cases h1 : w = -β
        · exact Or.inr (Or.inl h1)
        by_cases h2 : w = β
        · exact Or.inr (Or.inr h2)
        refine Or.inl ⟨hw, ?_, ?_⟩
        · exact lt_of_le_of_ne (by linarith) (Ne.symm h1)
        · exact lt_of_le_of_ne (by linarith) h2
    _ ≤ volume ({w | x + w ∈ B} ∩ Ioo (-β) β) + volume ({-β, β} : Set ℝ) := measure_union_le _ _
    _ = volume ({w | x + w ∈ B} ∩ Ioo (-β) β) := by
        rw [(Set.toFinite _ : ({-β, β} : Set ℝ).Finite).measure_zero, add_zero]

/-- A spread-out increment (MT (RW2), §4.3.3): if some convolution power `Γ^{m∗}`, `m ≥ 1`, has a
density `γ ≥ δ > 0` on `(−β, β)`, the random walk is irreducible for Lebesgue measure on
`(−β, β)`. -/
theorem randomWalk_isPhiIrreducible_of_convPow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {m : ℕ}
    (hm : 1 ≤ m) {β : ℝ} {δ : ℝ≥0∞} (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ convPow Γ m A)
    (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      IsPhiIrreducible (randomWalkKernel Γ) (volume.restrict (Ioo (-β) β)) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  have hMm := isMarkovKernel_pow (randomWalkKernel Γ) m
  refine ⟨hM, isPhiIrreducible_of_skeleton _ hm ?_⟩
  refine isPhiIrreducible_of_local_density _ (α := 1) (by simp) hβ hδ fun x A hA => ?_
  rw [randomWalkKernel_pow_apply Γ m x, Measure.map_apply (measurable_const_add x) hA]
  simp only [one_mul]
  exact le_of_density hγ hγδ ((measurable_const_add x) hA)

/-- The set `x + ℚ`. -/
def ratCoset (x : ℝ) : Set ℝ := range fun q : ℚ => x + (q : ℝ)

/-- MT p. 89: if the increment law is concentrated on `ℚ`, every `x + ℚ` is absorbing, there are
uncountably many such sets, and the walk is irreducible for no nonzero measure. If moreover
`Γ{q} > 0` for every rational `q`, each `x + ℚ` is an absorbing irreducible set: every point of
it is reached in one step from every other. -/
theorem randomWalk_rational (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ : Γ (range (Rat.cast : ℚ → ℝ))ᶜ = 0) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      (∀ x, IsAbsorbing (randomWalkKernel Γ) (ratCoset x)) ∧
      ¬ (range ratCoset).Countable ∧
      (∀ φ : Measure ℝ, IsPhiIrreducible (randomWalkKernel Γ) φ → φ = 0) ∧
      ((∀ q : ℚ, Γ {(q : ℝ)} ≠ 0) →
        ∀ x, ∀ y ∈ ratCoset x, ∀ z ∈ ratCoset x, 0 < randomWalkKernel Γ y {z}) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  have hmeas : ∀ x, MeasurableSet (ratCoset x) := fun x => (countable_range _).measurableSet
  have hAbs : ∀ x, IsAbsorbing (randomWalkKernel Γ) (ratCoset x) := by
    rintro x y ⟨q, rfl⟩
    rw [← prob_compl_eq_zero_iff (hmeas x), randomWalkKernel_apply' Γ _ (hmeas x).compl]
    refine measure_mono_null (fun w hw => ?_) hΓ
    rintro ⟨r, rfl⟩
    exact hw ⟨q + r, by push_cast; ring⟩
  refine ⟨hM, hAbs, ?_, fun φ hφ => ?_, fun hpos x y hy z hz => ?_⟩
  · intro hc
    apply Cardinal.not_countable_real
    have : (univ : Set ℝ) = ⋃₀ range ratCoset :=
      (eq_univ_of_forall fun x =>
        mem_sUnion.2 ⟨ratCoset x, mem_range_self x, (0 : ℚ), by simp⟩).symm
    rw [this]
    exact hc.sUnion fun s ⟨x, hx⟩ => hx ▸ countable_range _
  · refine not_isPhiIrreducible_of_disjoint_absorbing (hmeas 0) (hmeas √2)
      (show (ratCoset 0).Nonempty from ⟨0, (0 : ℚ), by simp⟩)
      (show (ratCoset √2).Nonempty from ⟨√2, (0 : ℚ), by simp⟩) ?_ (hAbs 0) (hAbs √2) hφ
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    obtain ⟨q, rfl⟩ := hy1
    obtain ⟨r, hr⟩ := hy2
    exact irrational_sqrt_two ⟨q - r, by push_cast; linarith⟩
  · obtain ⟨q, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    rw [randomWalkKernel_apply' Γ _ (measurableSet_singleton _), pos_iff_ne_zero]
    have : {w | x + (q : ℝ) + w ∈ ({x + (r : ℝ)} : Set ℝ)} = {((r - q : ℚ) : ℝ)} := by
      ext w
      simp only [mem_ofPred_eq, mem_singleton_iff]
      push_cast
      constructor <;> intro h <;> linarith
    rw [this]
    exact hpos _

/-- MT p. 89: the AR(1) model with innovations uniform on `[−1, 1]` and `|α| ≤ 1` is
`μ_Leb`-irreducible on `[−1, 1]`. -/
theorem ar1_uniform_isPhiIrreducible {α : ℝ} (hα : |α| ≤ 1) :
    ∃ _ : IsMarkovKernel (ar1Kernel ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)) α),
      IsPhiIrreducible (ar1Kernel ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)) α)
        (volume.restrict (Icc (-1) 1)) := by
  set Γ : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)
  have hΓ : IsProbabilityMeasure Γ := ⟨by
    simp only [Γ, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Icc, smul_eq_mul]
    norm_num
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩
  have hM := isMarkovKernel_ar1Kernel Γ α
  refine ⟨hM, ?_⟩
  have hIoo : volume.restrict (Icc (-1 : ℝ) 1) = volume.restrict (Ioo (-1 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [hIoo]
  refine isPhiIrreducible_of_local_density _ (δ := (2 : ℝ≥0∞)⁻¹) hα one_pos (by simp)
    fun x A hA => ?_
  rw [ar1Kernel_apply' Γ α x hA]
  have hm : MeasurableSet {w | α * x + w ∈ A} := (measurable_const_add (α * x)) hA
  simp only [Γ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hm]
  gcongr
  exact Ioo_subset_Icc_self

/-- MT p. 89: if `|α| > 1` and the noise lies in `[−1, 1]`, then once `|x| > (|α| − 1)⁻¹` the next
state is larger in absolute value: the chain explodes monotonically. -/
theorem ar1_abs_lt_step {α x w : ℝ} (hα : 1 < |α|) (hx : (|α| - 1)⁻¹ < |x|) (hw : |w| ≤ 1) :
    |x| < |α * x + w| := by
  have h1 : 0 < |α| - 1 := by linarith
  have h2 : 1 < (|α| - 1) * |x| := by
    rwa [inv_lt_iff_one_lt_mul₀ h1, mul_comm] at hx
  calc |x| < |α| * |x| - 1 := by nlinarith
    _ ≤ |α * x| - |w| := by rw [abs_mul]; linarith
    _ ≤ |α * x + w| := by
        have := abs_add_le (α * x + w) (-w)
        rw [add_neg_cancel_right, abs_neg] at this
        linarith

/-- MT p. 89: if `|α| > 1` and the noise lies in `[−1, 1]`, the AR(1) chain is irreducible for no
nonzero measure: every set `{|x| ≥ c}`, `c > (|α| − 1)⁻¹`, is absorbing, so an irreducibility
measure charges no bounded set. -/
theorem ar1_explosive_not_irreducible (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hα : 1 < |α|) (hΓ : Γ (Icc (-1) 1)ᶜ = 0) :
    ∃ _ : IsMarkovKernel (ar1Kernel Γ α),
      ∀ φ : Measure ℝ, IsPhiIrreducible (ar1Kernel Γ α) φ → φ = 0 := by
  have hM := isMarkovKernel_ar1Kernel Γ α
  refine ⟨hM, fun φ hφ => ?_⟩
  set c₀ : ℝ := (|α| - 1)⁻¹ + 1
  have hc₀ : (|α| - 1)⁻¹ < c₀ := by linarith
  have hAbs : ∀ k : ℕ, IsAbsorbing (ar1Kernel Γ α) {x | c₀ + k ≤ |x|} := by
    intro k y hy
    have hm : MeasurableSet {x : ℝ | c₀ + k ≤ |x|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    rw [← prob_compl_eq_zero_iff hm, ar1Kernel_apply' Γ α y hm.compl]
    refine measure_mono_null (fun w hw => ?_) hΓ
    intro hw1
    apply hw
    simp only [mem_ofPred_eq] at hy ⊢
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact hy.trans (ar1_abs_lt_step hα (by linarith) (abs_le.2 hw1)).le
  have hfull : ∀ k : ℕ, φ {x | c₀ + k ≤ |x|}ᶜ = 0 := fun k =>
    proposition_4_2_3_i hφ (measurableSet_le measurable_const continuous_abs.measurable)
      ⟨c₀ + k, by simp only [mem_ofPred_eq]; rw [abs_of_pos (by positivity)]⟩ (hAbs k)
  rw [← Measure.measure_univ_eq_zero]
  have : (univ : Set ℝ) = ⋃ k : ℕ, {x | c₀ + k ≤ |x|}ᶜ := by
    refine (eq_univ_of_forall fun x => ?_).symm
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    have : 0 < c₀ := by positivity
    exact mem_iUnion.2 ⟨k, by simp only [mem_compl_iff, mem_ofPred_eq, not_le]; linarith⟩
  rw [this]
  exact measure_iUnion_null hfull

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Small sets for specific models (MT §5.3, and the examples of pp. 96–98)

Meyn and Tweedie, §5.3, pp. 106–110, and the atoms discussed on pp. 96–98.

**Atoms.**
* `isAccessibleAtom_singleton_countable` (p. 96): for an irreducible chain on a countable space
  every point is an accessible atom.
* `map_add_left_inj`, `randomWalk_not_isAccessibleAtom` (p. 96): for random walk on `ℝ` with an
  absolutely continuous increment law there is no accessible atom.
* `halfLine_isAccessibleAtom_zero` (pp. 96, 98): for random walk on a half line with
  `Γ(−∞, 0) > 0`, `{0}` is an accessible atom (for every maximal irreducibility measure).

**Random walk on a half line** (§5.3.1, p. 106).
* `halfLine_isSmallSet_Iic`: if `Γ(−∞, 0) > 0`, every `[0, c]` is small, with minorizing measure
  a multiple of `δ₀`; `halfLine_isSmall_of_isCompact`: every compact set is small.

**Random walk with a density** (§5.3.2, p. 107).
* `randomWalk_isSmallSet_Icc`: if the increment law has a density `γ ≥ δ > 0` on `(−β, β)`, then
  `C = [−β/2, β/2]` is small for the one-step kernel.

**Scalar linear models** (§5.3.5, p. 110, for `n = 1`).
* `ar1_isSmallSet_of_density`: for the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` with an error density
  bounded below on every bounded interval, every bounded measurable set is small (with `m = 1`
  and a multiple of Lebesgue measure on `[−1, 1]`).
* `gaussianReal_density_ge`, `ar1_gaussian_isSmall_of_isCompact`: in the Gaussian case every
  compact set is small; for `α = 1` this is the Gaussian random walk.

**The GI/G/1 queue** (§5.3.3, p. 108).
* **Proposition 5.3.2** (`proposition_5_3_2`): for a ladder kernel on `ℤ₊ × ℝ₊` whose bottom rung
  satisfies `P(0, x; {0} × A) = G(x, ∞) H(A)` (the formula `Λ₀*(x, ·) = H(·) G(x, ∞)` derived in
  the book), `{0} × [0, β]` is `ν₁`-small with `ν₁ = G(β, ∞) H` placed on the bottom rung.

Proposition 5.3.1 (spread-out random walks) is in `SpreadOut`.

**Elsewhere in this project.** Proposition 5.3.3 is in `RenewalSmallSets` (on the forward
recurrence `δ`-skeleton of `RenewalSkeletons`), the multidimensional LSS(F, G) claim of §5.3.5
is in `LinearSmallSets`, and the bottom-rung formula of the GI/G/1 ladder chain, derived from
(5.29)–(5.31) for the queue of `GIG1Embedding`, is in `GIG1SmallSets`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-! ### Atoms -/

/-- MT p. 96: for an irreducible chain on a countable space, every point is an accessible atom
(for counting measure, a maximal irreducibility measure). -/
theorem isAccessibleAtom_singleton_countable {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable X] [Nonempty X] (P : Kernel X X) [IsMarkovKernel P]
    (hP : IsIrreducibleChain P) (x : X) : IsAccessibleAtom P Measure.count {x} :=
  ⟨isAtom_singleton P x, isMaximalIrreducibility_count P hP, by simp⟩

/-- MT pp. 96, 98: for random walk on a half line with `Γ(−∞, 0) > 0`, `{0}` is an accessible
atom for every maximal irreducibility measure. -/
theorem halfLine_isAccessibleAtom_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (h : 0 < Γ (Iio 0)) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    IsAccessibleAtom (halfLineWalkKernel Γ) ψ {0} := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨_, hiff⟩ := proposition_4_3_1 Γ
  have hirr := hiff.2 h
  refine ⟨isAtom_singleton _ 0, hψ, (hψ.pos_iff_hitProb_pos (measurableSet_singleton 0)).2
    fun x => hirr {0} (measurableSet_singleton 0) (by simp) x⟩

/-- A probability measure on `ℝ` is moved by every nonzero translation: if
`Γ(· − x) = Γ(· − y)` then `x = y`. -/
theorem map_add_left_inj (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {x y : ℝ}
    (h : Γ.map (x + ·) = Γ.map (y + ·)) : x = y := by
  by_contra hne
  set s := |y - x| with hs
  have hs0 : 0 < s := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  have hF : ∀ w, Γ (Iic (w - x)) = Γ (Iic (w - y)) := fun w => by
    have := congrArg (fun μ : Measure ℝ => μ (Iic w)) h
    simp only [Measure.map_apply (measurable_const_add _) measurableSet_Iic] at this
    have e : ∀ c : ℝ, (c + ·) ⁻¹' Iic w = Iic (w - c) := fun c => by
      ext v; simp only [mem_preimage, mem_Iic]; constructor <;> intro <;> linarith
    rwa [e, e] at this
  have hG : ∀ w, Γ (Ici (w - x)) = Γ (Ici (w - y)) := fun w => by
    have := congrArg (fun μ : Measure ℝ => μ (Ici w)) h
    simp only [Measure.map_apply (measurable_const_add _) measurableSet_Ici] at this
    have e : ∀ c : ℝ, (c + ·) ⁻¹' Ici w = Ici (w - c) := fun c => by
      ext v; simp only [mem_preimage, mem_Ici]; constructor <;> intro <;> linarith
    rwa [e, e] at this
  -- both distribution functions are `s`-periodic
  have hFs : ∀ w, Γ (Iic (w + s)) = Γ (Iic w) := fun w => by
    rcases abs_cases (y - x) with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hF (w + y); rw [hs, h1] at *
      rw [show w + y - x = w + (y - x) by ring, show w + y - y = w by ring] at this
      exact this
    · have := hF (w + x); rw [hs, h1] at *
      rw [show w + x - y = w + -(y - x) by ring, show w + x - x = w by ring] at this
      exact this.symm
  have hGs : ∀ w, Γ (Ici (w + s)) = Γ (Ici w) := fun w => by
    rcases abs_cases (y - x) with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hG (w + y); rw [hs, h1] at *
      rw [show w + y - x = w + (y - x) by ring, show w + y - y = w by ring] at this
      exact this
    · have := hG (w + x); rw [hs, h1] at *
      rw [show w + x - y = w + -(y - x) by ring, show w + x - x = w by ring] at this
      exact this.symm
  have hFk : ∀ (k : ℕ) w, Γ (Iic (w + k * s)) = Γ (Iic w) := fun k => by
    induction k with
    | zero => intro w; simp
    | succ k ih => intro w; rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hFs, ih]
  have hGk : ∀ (k : ℕ) w, Γ (Ici (w - k * s)) = Γ (Ici w) := fun k => by
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [← ih w, ← hGs (w - ((k + 1 : ℕ) : ℝ) * s)]
      congr 2
      push_cast
      ring
  -- hence `Γ(−∞, 0] = 1` and `Γ[1, ∞) = 1`, which is impossible
  have hk : Tendsto (fun k : ℕ => (k : ℝ) * s) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hs0
  have hF1 : Γ (Iic 0) = 1 := by
    have h1 := (tendsto_measure_Iic_atTop Γ).comp (tendsto_atTop_add_const_left _ 0 hk)
    rw [measure_univ] at h1
    refine tendsto_nhds_unique (tendsto_const_nhds.congr fun k => ?_) h1
    exact (hFk k 0).symm
  have hG1 : Γ (Ici 1) = 1 := by
    have hk' : Tendsto (fun k : ℕ => 1 - (k : ℝ) * s) atTop atBot :=
      tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp hk) |>.congr fun k => by
        simp [sub_eq_add_neg]
    have h1 := (tendsto_measure_Ici_atBot Γ).comp hk'
    rw [measure_univ] at h1
    refine tendsto_nhds_unique (tendsto_const_nhds.congr fun k => ?_) h1
    exact (hGk k 1).symm
  have hdisj : Disjoint (Iic (0 : ℝ)) (Ici 1) :=
    Set.disjoint_left.2 fun v h1 h2 => by simp only [mem_Iic, mem_Ici] at h1 h2; linarith
  have := measure_union hdisj measurableSet_Ici (μ := Γ)
  rw [hF1, hG1] at this
  have hle := prob_le_one (μ := Γ) (s := Iic (0 : ℝ) ∪ Ici 1)
  rw [this] at hle
  norm_num at hle

/-- MT p. 96: for random walk on `ℝ` with an increment law absolutely continuous with respect to
Lebesgue measure, accessible atoms do not exist. An atom is at most one point, since a
probability on `ℝ` is moved by every nonzero translation, and a single point is never hit. -/
theorem randomWalk_not_isAccessibleAtom (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ : Γ ≪ volume) {ψ : Measure ℝ} (α : Set ℝ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    ¬ IsAccessibleAtom (randomWalkKernel Γ) ψ α := by
  have := isMarkovKernel_randomWalkKernel Γ
  rintro ⟨⟨hαm, ν, hν⟩, hψ, hpos⟩
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
  -- `α = {x}`
  have hsub : α ⊆ {x} := fun y hy => by
    have h := (hν y hy).trans (hν x hx).symm
    rw [randomWalkKernel_apply, randomWalkKernel_apply] at h
    exact mem_singleton_iff.2 (map_add_left_inj Γ h)
  have hxpos : 0 < ψ {x} := hpos.trans_le (measure_mono hsub)
  -- but `{x}` is never hit: `P(y, {x}) = Γ{x − y} = 0`
  have h1 : ∀ y, randomWalkKernel Γ y {x} = 0 := fun y => by
    rw [randomWalkKernel_apply' Γ y (measurableSet_singleton x)]
    refine hΓ (measure_mono_null (fun w hw => ?_) (Real.volume_singleton (a := x - y)))
    simp only [mem_ofPred_eq, mem_singleton_iff] at hw ⊢
    linarith
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (measurableSet_singleton x) x).1
    (hψ.2.1 {x} (measurableSet_singleton x) hxpos x)
  rw [pow_succ_apply' _ n x (measurableSet_singleton x)] at hn
  simp [h1] at hn

/-! ### Random walk on a half line -/

/-- MT §5.3.1, p. 106: if `Γ(−∞, 0) > 0`, every `[0, c]` is small for random walk on a half
line, with a multiple of `δ₀` as minorizing measure. -/
theorem halfLine_isSmallSet_Iic (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : 0 < Γ (Iio 0))
    (c : ℝ≥0) : ∃ (m : ℕ) (δ : ℝ≥0∞), 0 < δ ∧
      IsSmallSet (halfLineWalkKernel Γ) m (δ • Measure.dirac 0) (Iic c) := by
  obtain ⟨ε, hε, hΓε⟩ := exists_Iio_neg_pos Γ h
  obtain ⟨n, hn⟩ := exists_nat_gt ((c : ℝ) / ε)
  have hcn : (c : ℝ) < (n + 1) * ε := by
    have := (div_lt_iff₀ hε).1 hn
    nlinarith
  refine ⟨n + 1, Γ (Iio (-ε)) ^ (n + 1), ENNReal.pow_pos hΓε _, measurableSet_Iic, by omega,
    smul_measure_ne_zero (by simp) (ENNReal.pow_pos hΓε _).ne', fun x hx => ?_⟩
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
  by_cases h0 : (0 : ℝ≥0) ∈ B
  · rw [indicator_of_mem h0, Pi.one_apply, mul_one]
    have hx' : (x : ℝ) < (n + 1) * ε := lt_of_le_of_lt (by exact_mod_cast hx) hcn
    exact (halfLine_pow_zero_ge Γ hε le_rfl n x hx').trans
      (measure_mono (singleton_subset_iff.2 h0))
  · rw [indicator_of_notMem h0, mul_zero]
    exact zero_le

/-- MT §5.3.1, p. 106: if `Γ(−∞, 0) > 0`, every compact subset of `[0, ∞)` is small for random
walk on a half line. -/
theorem halfLine_isSmall_of_isCompact (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (h : 0 < Γ (Iio 0)) {C : Set ℝ≥0} (hC : IsCompact C) : IsSmall (halfLineWalkKernel Γ) C := by
  obtain ⟨c, hc⟩ := hC.bddAbove
  obtain ⟨m, δ, -, hs⟩ := halfLine_isSmallSet_Iic Γ h c
  exact ⟨m, _, hs.mono hC.measurableSet fun x hx => hc hx⟩

/-! ### Random walk with a density -/

/-- MT §5.3.2, p. 107: if the increment law of a random walk on `ℝ` has a density `γ ≥ δ > 0` on
`(−β, β)`, then `C = [−β/2, β/2]` is `δ μ_Leb|_C`-small (with `m = 1`). -/
theorem randomWalk_isSmallSet_Icc (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ}
    (hβ : 0 < β) {δ : ℝ≥0∞} (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    IsSmallSet (randomWalkKernel Γ) 1 (δ • volume.restrict (Icc (-(β / 2)) (β / 2)))
      (Icc (-(β / 2)) (β / 2)) := by
  refine ⟨measurableSet_Icc, one_pos, smul_measure_ne_zero ?_ hδ, fun x hx => ?_⟩
  · rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    simp only [ENNReal.ofReal_eq_zero, not_le]
    linarith
  · rw [pow_one]
    refine Measure.le_intro fun B hB _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
    exact (randomWalk_step_ge Γ hγ hγδ hx (hB.inter measurableSet_Icc) inter_subset_right).trans
      (measure_mono inter_subset_left)

/-! ### Scalar linear models -/

/-- MT §5.3.5, p. 110 (`n = 1`): for the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` whose error law has a
density bounded below on every bounded interval, every set `C ⊆ [−R, R]` is small, with `m = 1`
and a multiple of Lebesgue measure on `[−1, 1]` as minorizing measure. -/
theorem ar1_isSmallSet_of_density (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ)
    {γ : ℝ → ℝ≥0∞} (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A)
    (hpos : ∀ R : ℝ, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ w ∈ Icc (-R) R, c ≤ γ w) {R : ℝ} {C : Set ℝ}
    (hCm : MeasurableSet C) (hCR : C ⊆ Icc (-R) R) :
    ∃ c : ℝ≥0∞, 0 < c ∧ IsSmallSet (ar1Kernel Γ α) 1 (c • volume.restrict (Icc (-1) 1)) C := by
  obtain ⟨c, hc, hcγ⟩ := hpos (|α| * |R| + 1)
  refine ⟨c, hc, hCm, one_pos, smul_measure_ne_zero ?_ hc.ne', fun x hx => ?_⟩
  · rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    norm_num
  rw [pow_one]
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB, ar1Kernel_apply' Γ α x hB]
  have hS : MeasurableSet {w | α * x + w ∈ B} := (measurable_const_add (α * x)) hB
  -- the translate of `B ∩ [−1, 1]` lies in `[−R', R']`, where the density is at least `c`
  have hsub : (· + α * x) ⁻¹' (B ∩ Icc (-1) 1) ⊆
      {w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1) := by
    intro y hy
    simp only [mem_preimage, mem_inter_iff, mem_Icc] at hy
    obtain ⟨hyB, hy1, hy2⟩ := hy
    have hxR : |x| ≤ |R| := by
      have := hCR hx
      rw [abs_le]; constructor <;> cases abs_cases R <;> linarith [this.1, this.2]
    have hax : |α * x| ≤ |α| * |R| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hxR (abs_nonneg α)
    refine ⟨by simpa [add_comm] using hyB, ?_, ?_⟩ <;> cases abs_cases (α * x) <;> linarith
  have hvol : volume (B ∩ Icc (-1) 1) = volume ((· + α * x) ⁻¹' (B ∩ Icc (-1) 1)) :=
    (measure_preimage_add_right volume (α * x) _).symm
  calc c * volume (B ∩ Icc (-1) 1)
      ≤ c * volume ({w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1)) := by
        rw [hvol]; gcongr
    _ = ∫⁻ _ in {w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1), c := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in {w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1), γ w :=
        setLIntegral_mono' (hS.inter measurableSet_Icc) fun w hw => hcγ w hw.2
    _ ≤ ∫⁻ w in {w | α * x + w ∈ B}, γ w := lintegral_mono_set inter_subset_left
    _ ≤ Γ {w | α * x + w ∈ B} := hγ _ hS

/-- The standard Gaussian density is bounded below on every bounded interval:
`φ(w) ≥ (2π)^{−1/2} e^{−R²/2}` for `|w| ≤ R`. -/
theorem gaussianReal_density_ge (R : ℝ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ w ∈ Icc (-R) R, c ≤ gaussianPDF 0 1 w := by
  refine ⟨ENNReal.ofReal ((√(2 * Real.pi))⁻¹ * Real.exp (-R ^ 2 / 2)), ?_, fun w hw => ?_⟩
  · rw [ENNReal.ofReal_pos]
    positivity
  · rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have : w ^ 2 ≤ R ^ 2 := sq_le_sq' hw.1 hw.2
    linarith

/-- MT §5.3.5, p. 110 (`n = 1`): for the Gaussian AR(1) model (and, with `α = 1`, the Gaussian
random walk), every compact set is small. -/
theorem ar1_gaussian_isSmall_of_isCompact (α : ℝ) {C : Set ℝ} (hC : IsCompact C) :
    IsSmall (ar1Kernel (gaussianReal 0 1) α) C := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  have hCR : C ⊆ Icc (-R) R := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at this
    exact this
  have hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, gaussianPDF 0 1 x ≤ gaussianReal 0 1 A :=
    fun A hA => by
      rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ hA]
  obtain ⟨c, -, hs⟩ := ar1_isSmallSet_of_density (gaussianReal 0 1) α hγ gaussianReal_density_ge
    hC.measurableSet hCR
  exact ⟨1, _, hs⟩

/-! ### The GI/G/1 queue: Proposition 5.3.2 -/

/-- **Proposition 5.3.2** (MT p. 108). Let `P` be a transition kernel on `ℤ₊ × ℝ₊` (queue length
and residual service time at arrival epochs) whose bottom rung satisfies
`P(0, x; {0} × A) = G(x, ∞) H(A)`, the formula `Λ₀*(x, ·) = H(·) G(x, ∞)` of the book. If
`G(β, ∞) > 0` and `H` is a probability, then `{0} × [0, β]` is `ν₁`-small with
`ν₁ = G(β, ∞) H` on the bottom rung. -/
theorem proposition_5_3_2 (P : Kernel (ℕ × ℝ≥0) (ℕ × ℝ≥0)) (G : Measure ℝ≥0) (H : Measure ℝ≥0)
    [IsProbabilityMeasure H]
    (hP : ∀ x A, MeasurableSet A → P (0, x) ({0} ×ˢ A) = G (Ioi x) * H A) {β : ℝ≥0}
    (hG : 0 < G (Ioi β)) :
    IsSmallSet P 1 (G (Ioi β) • H.map (fun y => ((0 : ℕ), y))) ({0} ×ˢ Iic β) := by
  have hmk : Measurable fun y : ℝ≥0 => ((0 : ℕ), y) := measurable_const.prodMk measurable_id
  refine ⟨(measurableSet_singleton 0).prod measurableSet_Iic, one_pos, smul_measure_ne_zero ?_
    hG.ne', fun z hz => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (ℕ × ℝ≥0) => μ univ) h0
    simp [Measure.map_apply hmk MeasurableSet.univ] at this
  obtain ⟨z1, z2⟩ := z
  simp only [mem_prod, mem_singleton_iff, mem_Iic] at hz
  obtain ⟨rfl, hz2⟩ := hz
  rw [pow_one]
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmk hB]
  have hsec : MeasurableSet ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B) := hmk hB
  calc G (Ioi β) * H ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B)
      ≤ G (Ioi z2) * H ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B) := by
        gcongr
    _ = P (0, z2) ({0} ×ˢ ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B)) := (hP z2 _ hsec).symm
    _ ≤ P (0, z2) B := by
        refine measure_mono ?_
        rintro ⟨q1, q2⟩ ⟨hq1, hq2⟩
        rw [mem_singleton_iff] at hq1
        subst hq1
        exact hq2

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Small sets for the linear state space model (MT §5.3.5)

Meyn and Tweedie, §5.3.5, p. 110: for the controllable Gaussian LSS(F, G) model every compact set
is small.

The book argues from the continuity and positivity of the Gaussian density of `Pⁿ(x, ·)`, whose
covariance `Σ_n = C_n C_nᵀ` is positive definite under controllability. Mathlib has no
multivariate Gaussian density, so the proof here is coordinate-free: `Pᵐ(x, ·)` is the image of
`Γ^{⊗m}` under `u ↦ Fᵐx + C_m u`, and

* `exists_preimage_ge_of_surjective`: a surjective linear map `L : E → ℝⁿ` pulls Lebesgue
  measure on a ball back to at least a multiple of it under any Haar measure on `E`, restricted
  to a larger ball (uniqueness of Haar measure on `ℝⁿ × ker L ≃ E`);
* `pi_fin_mono`, `pi_smul_restrict`, `pi_ge_restrict`: lower bounds pass to products;
* `gaussianReal_ge_restrict`, `gaussianPi_ge_restrict`: `N(0, I)` dominates a multiple of
  Lebesgue measure on every closed ball, since its density is bounded below there;
* `lss_isSmallSet_of_isCompact`: for any disturbance law with that property and a controllable
  pair `(F, G)`, every compact `K` is `max n 1`-small, with minorising measure a multiple of
  Lebesgue measure on any ball `B̄(0, r)`, `r > 0`; the compactness of `K` enters only through
  the boundedness of `Fᵐ K`;
* `lss_gaussian_isSmallSet_of_isCompact`, `lss_gaussian_isSmall_of_isCompact`: the Gaussian
  case (LSS3).

The book takes `m = n`; here `m = max n 1`, since `IsSmallSet` requires `m ≥ 1` and `n = 0` is
allowed.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal Matrix

variable {n p : ℕ}

/-- **A surjective linear map pushes a Haar measure above a multiple of Lebesgue measure on a
ball.** For a surjective linear `L : E → ℝⁿ` and `R ≥ 0` there are `R'` and `c > 0` with
`μ(L⁻¹(S) ∩ B̄(0, R')) ≥ c μ_Leb(S ∩ B̄(0, R))` for every measurable `S`. -/
theorem exists_preimage_ge_of_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {n : ℕ} (L : E →ₗ[ℝ] (Fin n → ℝ)) (hL : Function.Surjective L)
    (R : ℝ) : ∃ R' : ℝ, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ S, MeasurableSet S →
      c * volume (S ∩ closedBall 0 R) ≤ μ (L ⁻¹' S ∩ closedBall 0 R') := by
  obtain ⟨T, hT⟩ := LinearMap.exists_rightInverse_of_surjective L (LinearMap.range_eq_top.2 hL)
  set K := LinearMap.ker L
  let f : (Fin n → ℝ) × K →ₗ[ℝ] E := T ∘ₗ LinearMap.fst ℝ _ _ + K.subtype ∘ₗ LinearMap.snd ℝ _ _
  have hLT : ∀ y, L (T y) = y := fun y => LinearMap.congr_fun hT y
  have hf : ∀ q, f q = T q.1 + q.2 := fun q => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, k⟩ h
    rw [hf] at h
    have h1 : y = 0 := by
      have := congrArg L h
      rwa [map_add, hLT, show L (k : E) = 0 from k.2, add_zero, map_zero] at this
    subst h1
    simp only [map_zero, zero_add] at h
    exact Prod.ext rfl (Subtype.ext h)
  have hsurj : Function.Surjective f := fun e => by
    refine ⟨(L e, ⟨e - T (L e), ?_⟩), ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hLT, sub_self]
    · rw [hf]; simp
  let Φ := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hΦ : ∀ q, Φ q = T q.1 + q.2 := fun q => rfl
  set lam := μ.map Φ.symm with hlam
  have : lam.IsAddHaarMeasure := Φ.symm.isAddHaarMeasure_map μ
  set ρ := (volume : Measure (Fin n → ℝ)).prod (Measure.addHaar : Measure K) with hρ
  have hlamρ : lam = Measure.addHaarScalarFactor lam ρ • ρ :=
    Measure.isAddLeftInvariant_eq_smul lam ρ
  set c₀ := Measure.addHaarScalarFactor lam ρ
  have hc₀ : (c₀ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have hz : lam = 0 := by rw [hlamρ, ENNReal.coe_eq_zero.1 h0, zero_smul]
    have := measure_ball_pos lam (0 : (Fin n → ℝ) × K) one_pos
    rw [hz] at this
    exact lt_irrefl _ this
  set Tc := LinearMap.toContinuousLinearMap T
  refine ⟨‖Tc‖ * R + 1, c₀ * Measure.addHaar (ball (0 : K) 1),
    ENNReal.mul_pos hc₀ (measure_ball_pos _ _ one_pos).ne', fun S hS => ?_⟩
  set A := (S ∩ closedBall 0 R) ×ˢ ball (0 : K) 1 with hA
  have hAm : MeasurableSet A := (hS.inter measurableSet_closedBall).prod measurableSet_ball
  have hsub : Φ '' A ⊆ L ⁻¹' S ∩ closedBall 0 (‖Tc‖ * R + 1) := by
    rintro _ ⟨⟨y, k⟩, ⟨⟨hyS, hyR⟩, hk⟩, rfl⟩
    rw [hΦ]
    refine ⟨?_, ?_⟩
    · change L (T y + (k : E)) ∈ S
      rwa [map_add, hLT, show L (k : E) = 0 from k.2, add_zero]
    · rw [mem_closedBall_zero_iff] at hyR ⊢
      rw [mem_ball_zero_iff] at hk
      calc ‖T y + (k : E)‖ ≤ ‖T y‖ + ‖(k : E)‖ := norm_add_le _ _
        _ ≤ ‖Tc‖ * R + 1 := by
          gcongr
          · calc ‖T y‖ = ‖Tc y‖ := rfl
              _ ≤ ‖Tc‖ * ‖y‖ := Tc.le_opNorm y
              _ ≤ ‖Tc‖ * R := by gcongr
          · exact hk.le
  have hmeasA : μ (Φ '' A) = lam A := by
    rw [hlam, Measure.map_apply Φ.symm.continuous.measurable hAm,
      ContinuousLinearEquiv.image_eq_preimage_symm]
  calc c₀ * Measure.addHaar (ball (0 : K) 1) * volume (S ∩ closedBall 0 R)
      = lam A := by
        rw [hlamρ, Measure.smul_apply, hA, hρ, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
        ring
    _ = μ (Φ '' A) := hmeasA.symm
    _ ≤ _ := measure_mono hsub


/-! ### Lower bounds for product measures -/

/-- Products of measures are monotone: `μ ≤ ν` implies `μ^{⊗k} ≤ ν^{⊗k}`. -/
theorem pi_fin_mono {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (h : μ ≤ ν) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) ≤ Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0
    rw [← (e1.symm _).map_eq, ← (e2.symm _).map_eq]
    exact Measure.map_mono (Measure.prod_mono h ih) (MeasurableEquiv.measurable _)

/-- `(c μ|_s)^{⊗ι} = c^{|ι|} μ^{⊗ι}|_{sⁱ}`. -/
theorem pi_smul_restrict {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (c : NNReal) (s : Set α) :
    Measure.pi (fun _ : ι => c • μ.restrict s) =
      c ^ Fintype.card ι • (Measure.pi fun _ : ι => μ).restrict (Set.univ.pi fun _ => s) := by
  rw [Measure.restrict_pi_pi]
  refine Measure.pi_eq fun t _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/-- The standard Gaussian law on `ℝ` dominates a multiple of Lebesgue measure on every closed
ball. -/
theorem gaussianReal_ge_restrict (R : ℝ) :
    ∃ c : NNReal, 0 < c ∧ c • volume.restrict (closedBall (0 : ℝ) R) ≤ gaussianReal 0 1 := by
  set c := Real.toNNReal ((√(2 * Real.pi))⁻¹ * Real.exp (-R ^ 2 / 2))
  refine ⟨c, Real.toNNReal_pos.2 (by positivity), Measure.le_intro fun B hB _ => ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hB, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    withDensity_apply _ hB, ENNReal.smul_def, smul_eq_mul]
  calc (c : ℝ≥0∞) * volume (B ∩ closedBall 0 R) = ∫⁻ _ in B ∩ closedBall 0 R, (c : ℝ≥0∞) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in B ∩ closedBall 0 R, gaussianPDF 0 1 w :=
        setLIntegral_mono' (hB.inter measurableSet_closedBall) fun w hw => by
          change ENNReal.ofReal _ ≤ ENNReal.ofReal _
          refine ENNReal.ofReal_le_ofReal ?_
          rw [gaussianPDFReal]
          simp only [NNReal.coe_one, mul_one, sub_zero]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          have h2 := hw.2
          rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at h2
          have : w ^ 2 ≤ R ^ 2 := sq_le_sq' h2.1 h2.2
          linarith
    _ ≤ ∫⁻ w in B, gaussianPDF 0 1 w := lintegral_mono_set inter_subset_left

/-- The standard Gaussian law on `ℝᵖ` dominates a multiple of Lebesgue measure on every closed
ball. -/
theorem gaussianPi_ge_restrict (p : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : NNReal, 0 < c ∧ c • volume.restrict (closedBall (0 : Fin p → ℝ) R) ≤
      Measure.pi (fun _ : Fin p => gaussianReal 0 1) := by
  obtain ⟨c, hc, hle⟩ := gaussianReal_ge_restrict R
  refine ⟨c ^ p, pow_pos hc p, ?_⟩
  have h := pi_fin_mono hle p
  rw [pi_smul_restrict, Fintype.card_fin] at h
  rwa [closedBall_pi _ hR, volume_pi]

/-- A law on `ℝᵖ` dominating multiples of Lebesgue measure on balls has products with the same
property. -/
theorem pi_ge_restrict {p : ℕ} {Γ : Measure (Fin p → ℝ)} [SigmaFinite Γ] (k : ℕ) {R : ℝ}
    (hR : 0 ≤ R) {c : NNReal} (hle : c • volume.restrict (closedBall (0 : Fin p → ℝ) R) ≤ Γ) :
    c ^ k • volume.restrict (closedBall (0 : Fin k → Fin p → ℝ) R) ≤
      Measure.pi (fun _ : Fin k => Γ) := by
  have h := pi_fin_mono hle k
  rw [pi_smul_restrict, Fintype.card_fin] at h
  rwa [closedBall_pi _ hR, volume_pi]


/-! ### Compact sets are small -/

/-- **Compact sets are small for LSS(F, G)** (MT §5.3.5, p. 110), for any disturbance law `Γ`
dominating a multiple of Lebesgue measure on each closed ball about `0`: if `(F, G)` is
controllable, every compact `K` is small, with `m = max n 1` and a minorising measure a multiple
of Lebesgue measure on any closed ball `B̄(0, r)`, `r > 0`. -/
theorem lss_isSmallSet_of_isCompact (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hΓ : ∀ R : ℝ, 0 ≤ R → ∃ c : NNReal, 0 < c ∧
      c • volume.restrict (closedBall (0 : Fin p → ℝ) R) ≤ Γ)
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      IsSmallSet (lssMatrixKernel Γ F G) (max n 1) (a • volume.restrict (closedBall 0 r)) K := by
  set m := max n 1 with hm
  set L := ctrbMap F G m
  have hL : Function.Surjective L :=
    LinearMap.range_eq_top.1 (range_ctrbMap_eq_top hc (le_max_left n 1))
  obtain ⟨R₀, hR₀⟩ := (hK.image (Matrix.mulVecLin (F ^ m)).continuous_of_finiteDimensional
    ).isBounded.subset_closedBall (0 : Fin n → ℝ)
  obtain ⟨R', c₁, hc₁, hA⟩ := exists_preimage_ge_of_surjective
    (volume : Measure (Fin m → Fin p → ℝ)) L hL (R₀ + r)
  obtain ⟨c₂, hc₂, hle⟩ := hΓ (max R' 0) (le_max_right _ _)
  have hpi := pi_ge_restrict m (le_max_right R' 0) hle
  refine ⟨(c₂ : ℝ≥0∞) ^ m * c₁, ENNReal.mul_pos (pow_ne_zero _ (by exact_mod_cast hc₂.ne'))
    hc₁.ne', hK.isClosed.measurableSet, lt_max_of_lt_right one_pos, ?_, fun x hx => ?_⟩
  · intro h0
    have h1 := congrArg (fun μ : Measure (Fin n → ℝ) => μ univ) h0
    simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at h1
    rcases h1 with (h1 | h1) | h1
    · exact pow_ne_zero m (ENNReal.coe_ne_zero.2 hc₂.ne') h1
    · exact hc₁.ne' h1
    · exact (measure_closedBall_pos volume 0 hr).ne' h1
  refine Measure.le_intro fun B hB _ => ?_
  set v := (F ^ m) *ᵥ x
  have hv : ‖v‖ ≤ R₀ := mem_closedBall_zero_iff.1 (hR₀ ⟨x, hx, rfl⟩)
  set S := (fun y => v + y) ⁻¹' B with hS
  have hSm : MeasurableSet S := measurable_const_add v hB
  rw [lss_pow_eq, Measure.map_apply (measurable_const_add v) hB, ctrbLaw,
    Measure.map_apply (measurable_ctrbMap F G m) hSm, Measure.smul_apply,
    Measure.restrict_apply hB, smul_eq_mul]
  have hshift : (fun y => v + y) ⁻¹' (B ∩ closedBall 0 r) ⊆ S ∩ closedBall 0 (R₀ + r) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have h2 := mem_closedBall_zero_iff.1 hy.2
    rw [mem_closedBall_zero_iff]
    calc ‖y‖ = ‖(v + y) - v‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖v + y‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ R₀ + r := by linarith
  calc (c₂ : ℝ≥0∞) ^ m * c₁ * volume (B ∩ closedBall 0 r)
      = (c₂ : ℝ≥0∞) ^ m * (c₁ * volume ((fun y => v + y) ⁻¹' (B ∩ closedBall 0 r))) := by
        rw [measure_preimage_add, mul_assoc]
    _ ≤ (c₂ : ℝ≥0∞) ^ m * (c₁ * volume (S ∩ closedBall 0 (R₀ + r))) := by
        gcongr
    _ ≤ (c₂ : ℝ≥0∞) ^ m * volume (L ⁻¹' S ∩ closedBall 0 (max R' 0)) := by
        gcongr
        exact (hA S hSm).trans (measure_mono (inter_subset_inter_right _
          (closedBall_subset_closedBall (le_max_left R' 0))))
    _ = (c₂ ^ m • volume.restrict (closedBall (0 : Fin m → Fin p → ℝ) (max R' 0)))
          (L ⁻¹' S) := by
        rw [Measure.smul_apply, Measure.restrict_apply ((measurable_ctrbMap F G m) hSm),
          ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
    _ ≤ (Measure.pi fun _ : Fin m => Γ) (L ⁻¹' S) := hpi _

/-- **§5.3.5, Gaussian case** (MT p. 110): for the controllable LSS(F, G) model with
`W ∼ N(0, I)` (LSS3), every compact set is small. -/
theorem lss_gaussian_isSmallSet_of_isCompact {F : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      IsSmallSet (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) (max n 1)
        (a • volume.restrict (closedBall 0 r)) K :=
  lss_isSmallSet_of_isCompact _ (fun R hR => gaussianPi_ge_restrict p R hR) hc hK hr

/-- **§5.3.5** (MT p. 110): for the controllable Gaussian LSS(F, G) model every compact set is
small. -/
theorem lss_gaussian_isSmall_of_isCompact {F : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) :
    IsSmall (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) K := by
  obtain ⟨a, -, h⟩ := lss_gaussian_isSmallSet_of_isCompact hc hK one_pos
  exact ⟨_, _, h⟩

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sampled chains (MT §5.5.1)

Meyn and Tweedie, §5.5.1, pp. 115–117. A sampling distribution is a probability `a` on `ℤ₊`,
and `K_a = Σₙ a(n) Pⁿ` (5.43) is `sampledKernel P a` (Chapter 3).

* `IsSamplingDist a`: `Σₙ a(n) = 1`; `diracDist m` (`K_{δ_m} = Pᵐ`, `sampledKernel_diracDist`),
  `geomDist ε` (`K_{a_ε}` is the resolvent, `sampledKernel_geomDist`), `uniformDist N`
  (`a(i) = 1/N` for `1 ≤ i ≤ N`) and `mixDist` (`½(a₁ + a₂)`), all sampling distributions.
* `sampleConv a b = a ∗ b`, the convolution of sampling distributions, and
  `isSamplingDist_sampleConv`; `tsum_sum_antidiagonal`: `Σₙ Σ_{i+j=n} f(i, j) = Σᵢ Σⱼ f(i, j)`.
* **Lemma 5.5.2 (i)** (`lemma_5_5_2_i`, (5.46), p. 116): `K_{a∗b}(x, A) = ∫ K_a(x, dy) K_b(y, A)`,
  that is `K_{a∗b} = K_b ∘ₖ K_a`.
* `SampledAccessible P a A B`, `A ⇝ᵃ B` (5.44), p. 116: `inf_{x ∈ A} K_a(x, B) ≥ δ > 0`.
* **Lemma 5.5.1** (p. 116): `lemma_5_5_1_counterexample` shows that it fails as stated, and
  (5.45) with it, when `a(0) > 0`; `lemma_5_5_1` is the corrected statement for `a(0) = 0`, and
  `lemma_5_5_1_firstHit` the statement for the hitting time `σ_B` (time `0` included) for every
  `a`.
* **Lemma 5.5.2 (ii)** (`lemma_5_5_2_ii`): `A ⇝ᵃ B` and `B ⇝ᵇ C` give `A ⇝^{a∗b} C`.
* **Lemma 5.5.2 (iii)** (`lemma_5_5_2_iii`, (5.47)): `U(x, A) ≥ ∫ U(x, dy) K_a(y, A)`.

**Corrections.** Lemma 5.5.1 and (5.45) are false when `a(0) > 0` (the book's proof identifies
`L(x, B) = Pₓ(τ_B < ∞)` with the probability of ever being in `B`, time `0` included):
`lemma_5_5_1_counterexample`. They hold for `a(0) = 0`, and with `σ_B` in place of `τ_B` for every
`a`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Sampling distributions -/

/-- `a` is a **sampling distribution** (MT p. 115): a probability on `ℤ₊`. -/
def IsSamplingDist (a : ℕ → ℝ≥0∞) : Prop := ∑' n, a n = 1

/-- The point mass `δ_m` at time `m`. -/
noncomputable def diracDist (m : ℕ) (n : ℕ) : ℝ≥0∞ := if n = m then 1 else 0

/-- `δ_m` is a sampling distribution. -/
theorem isSamplingDist_diracDist (m : ℕ) : IsSamplingDist (diracDist m) := by
  unfold IsSamplingDist diracDist
  rw [tsum_ite_eq]

/-- `K_{δ_m} = Pᵐ`: the `δ_m`-sampled chain is the `m`-skeleton (MT p. 116). -/
theorem sampledKernel_diracDist (P : Kernel X X) (m : ℕ) :
    sampledKernel P (diracDist m) = P ^ m := by
  ext x A hA
  rw [sampledKernel_apply P _ x hA]
  unfold diracDist
  simp only [ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq]

/-- The geometric distribution `a_ε(n) = (1 − ε) εⁿ`. -/
noncomputable def geomDist (ε : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := (1 - ε) * ε ^ n

/-- `a_ε` is a sampling distribution for `ε < 1`. -/
theorem isSamplingDist_geomDist {ε : ℝ≥0∞} (hε : ε < 1) : IsSamplingDist (geomDist ε) :=
  tsum_geometric_weights hε

/-- `K_{a_ε}` is the resolvent (MT p. 116). -/
theorem sampledKernel_geomDist (P : Kernel X X) (ε : ℝ≥0∞) :
    sampledKernel P (geomDist ε) = resolvent P ε := rfl

/-- The uniform distribution `a(i) = 1/N` for `1 ≤ i ≤ N` (MT p. 120). -/
noncomputable def uniformDist (N : ℕ) (n : ℕ) : ℝ≥0∞ := if 1 ≤ n ∧ n ≤ N then (N : ℝ≥0∞)⁻¹ else 0

/-- The uniform distribution vanishes off `{1, …, N}`. -/
theorem uniformDist_eq_indicator (N : ℕ) :
    uniformDist N = (Finset.Icc 1 N : Set ℕ).indicator fun _ => (N : ℝ≥0∞)⁻¹ := by
  ext n
  simp [uniformDist, indicator]

/-- `Σ_{n ∈ {1, …, N}} f(n) ≥ ...`: the uniform kernel is the average of `P, …, Pᴺ`. -/
theorem sampledKernel_uniformDist_apply (P : Kernel X X) (N : ℕ) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    sampledKernel P (uniformDist N) x A = (N : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.Icc 1 N, (P ^ n) x A := by
  rw [sampledKernel_apply P _ x hA, Finset.mul_sum, tsum_eq_sum (s := Finset.Icc 1 N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp [uniformDist, hn.1, hn.2]
  · intro n hn
    rw [Finset.mem_Icc] at hn
    simp [uniformDist, hn]

/-- The uniform distribution on `{1, …, N}` is a sampling distribution for `N ≥ 1`. -/
theorem isSamplingDist_uniformDist {N : ℕ} (hN : 1 ≤ N) : IsSamplingDist (uniformDist N) := by
  unfold IsSamplingDist
  rw [uniformDist_eq_indicator, ← sum_eq_tsum_indicator, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, Nat.add_sub_cancel]
  exact ENNReal.mul_inv_cancel (by simp; omega) (by simp)

/-- The uniform distribution has finite mean `Σ i a(i) = (N + 1)/2` (MT p. 120). -/
theorem tsum_mul_uniformDist_ne_top (N : ℕ) :
    ∑' n : ℕ, (n : ℝ≥0∞) * uniformDist N n ≠ ∞ := by
  have : (fun n : ℕ => (n : ℝ≥0∞) * uniformDist N n) =
      (Finset.Icc 1 N : Set ℕ).indicator fun n : ℕ => (n : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
    ext n
    simp [uniformDist, indicator]
  rw [this, ← sum_eq_tsum_indicator]
  refine ENNReal.sum_ne_top.2 fun n hn => ENNReal.mul_ne_top (by simp) ?_
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h] at hn
  · simp; omega

/-- The mixture `½(a₁ + a₂)` of two sampling distributions (MT p. 119). -/
noncomputable def mixDist (a b : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := 2⁻¹ * a n + 2⁻¹ * b n

/-- The mixture is a sampling distribution. -/
theorem isSamplingDist_mixDist {a b : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    (hb : IsSamplingDist b) : IsSamplingDist (mixDist a b) := by
  unfold IsSamplingDist mixDist at *
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ha, hb, mul_one,
    ENNReal.inv_two_add_inv_two]

/-- `K_{½(a + b)} = ½ K_a + ½ K_b`. -/
theorem sampledKernel_mixDist_apply (P : Kernel X X) (a b : ℕ → ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) : sampledKernel P (mixDist a b) x A =
      2⁻¹ * sampledKernel P a x A + 2⁻¹ * sampledKernel P b x A := by
  simp only [sampledKernel_apply P _ x hA, mixDist, add_mul, ENNReal.tsum_add, mul_assoc,
    ENNReal.tsum_mul_left]

/-! ### Convolution -/

/-- The convolution `a ∗ b (n) = Σ_{i+j=n} a(i) b(j)` (MT p. 116). -/
noncomputable def sampleConv (a b : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Summation over antidiagonals: `Σₙ Σ_{i+j=n} f(i, j) = Σᵢ Σⱼ f(i, j)`. -/
theorem tsum_sum_antidiagonal (f : ℕ × ℕ → ℝ≥0∞) :
    ∑' n, ∑ p ∈ Finset.antidiagonal n, f p = ∑' i, ∑' j, f (i, j) := by
  rw [← ENNReal.tsum_prod', ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [← Finset.tsum_subtype]
  rfl

/-- The convolution of sampling distributions is a sampling distribution. -/
theorem isSamplingDist_sampleConv {a b : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    (hb : IsSamplingDist b) : IsSamplingDist (sampleConv a b) := by
  unfold IsSamplingDist sampleConv at *
  rw [tsum_sum_antidiagonal (fun p => a p.1 * b p.2)]
  simp_rw [ENNReal.tsum_mul_left, hb, mul_one, ha]

/-- **Lemma 5.5.2 (i)**, the generalized Chapman–Kolmogorov equations (5.46), MT p. 116:
`K_{a∗b}(x, A) = ∫ K_a(x, dy) K_b(y, A)`. -/
theorem lemma_5_5_2_i (P : Kernel X X) (a b : ℕ → ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    sampledKernel P (sampleConv a b) x A = ∫⁻ y, sampledKernel P b y A ∂sampledKernel P a x := by
  rw [sampledKernel_apply P _ x hA]
  simp_rw [sampleConv, Finset.sum_mul]
  have h1 : ∀ n, ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 * (P ^ n) x A =
      ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 * (P ^ (p.1 + p.2)) x A := fun n =>
    Finset.sum_congr rfl fun p hp => by rw [Finset.mem_antidiagonal.1 hp]
  simp_rw [h1]
  rw [tsum_sum_antidiagonal (fun p => a p.1 * b p.2 * (P ^ (p.1 + p.2)) x A)]
  change _ = ∫⁻ y, sampledKernel P b y A ∂(Measure.sum fun n => a n • (P ^ n) x)
  rw [lintegral_sum_measure]
  refine tsum_congr fun i => ?_
  rw [lintegral_smul_measure]
  simp_rw [sampledKernel_apply P _ _ hA]
  rw [lintegral_tsum fun j => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable,
    smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA),
    ← Kernel.pow_add_apply_eq_lintegral P i j x hA]
  ring

/-- Lemma 5.5.2 (i) as an identity of kernels: `K_{a∗b} = K_b ∘ₖ K_a`. -/
theorem sampledKernel_sampleConv (P : Kernel X X) (a b : ℕ → ℝ≥0∞) :
    sampledKernel P (sampleConv a b) = sampledKernel P b ∘ₖ sampledKernel P a := by
  ext x A hA
  rw [lemma_5_5_2_i P a b x hA, Kernel.comp_apply' _ _ _ hA]

/-! ### Uniform accessibility using a sampling distribution -/

/-- `A ⇝ᵃ B` (5.44), MT p. 116: `K_a(x, B) ≥ δ` for all `x ∈ A`, for some `δ > 0`. -/
def SampledAccessible (P : Kernel X X) (a : ℕ → ℝ≥0∞) (A B : Set X) : Prop :=
  ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ A, δ ≤ sampledKernel P a x B

/-- (5.45), corrected: if `a(0) = 0`, then `K_a(x, B) ≤ L(x, B)`. -/
theorem sampledKernel_le_hitProb (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) (ha0 : a 0 = 0) {B : Set X} (hB : MeasurableSet B) (x : X) :
    sampledKernel P a x B ≤ hitProb P B x := by
  rw [sampledKernel_apply P a x hB]
  calc ∑' n, a n * (P ^ n) x B ≤ ∑' n, a n * hitProb P B x := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rcases n with _ | n
        · rw [ha0, zero_mul, zero_mul]
        · gcongr
          exact pow_le_hitProb P hB n x
    _ = hitProb P B x := by rw [ENNReal.tsum_mul_right, ha, one_mul]

/-- **Lemma 5.5.1**, corrected (MT p. 116): if `a(0) = 0` and `A ⇝ᵃ B`, then `A ⇝ B`. -/
theorem lemma_5_5_1 (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    (ha0 : a 0 = 0) {A B : Set X} (hB : MeasurableSet B) (h : SampledAccessible P a A B) :
    UnifAccessible P A B := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun x hx => (h x hx).trans (sampledKernel_le_hitProb P ha ha0 hB x)⟩

/-- **Lemma 5.5.1** for the hitting time `σ_B` (time `0` included), for every sampling
distribution: `K_a(x, B) ≤ Pₓ(Φₙ ∈ B for some n ≥ 0)`, so `A ⇝ᵃ B` gives a uniform lower bound on
the probability of ever being in `B`. -/
theorem lemma_5_5_1_firstHit (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {B : Set X} (hB : MeasurableSet B) (x : X) :
    sampledKernel P a x B ≤ pathKernel P x {ω | ∃ n, ω n ∈ B} := by
  rw [sampledKernel_apply P a x hB]
  calc ∑' n, a n * (P ^ n) x B ≤ ∑' n, a n * pathKernel P x {ω | ∃ n, ω n ∈ B} := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        gcongr
        rw [← pathKernel_coord_mem P x n hB]
        exact measure_mono fun ω hω => ⟨n, hω⟩
    _ = pathKernel P x {ω | ∃ n, ω n ∈ B} := by rw [ENNReal.tsum_mul_right, ha, one_mul]

/-- The chain on `Bool` that jumps to `true` from every state. -/
noncomputable def toTrueKernel : Kernel Bool Bool := Kernel.const Bool (Measure.dirac true)

/-- `toTrueKernel` is a transition kernel. -/
theorem isMarkovKernel_toTrueKernel : IsMarkovKernel toTrueKernel := by
  unfold toTrueKernel; infer_instance

/-- **Correction to Lemma 5.5.1 and (5.45)** (MT p. 116): with `a = δ₀` (so `a(0) > 0`), the
chain that jumps to `true` from every state has `{false} ⇝ᵃ {false}`, since `K_{δ₀}(x, ·) = δₓ`,
but `L(false, {false}) = 0`: the chain never returns to `false`. -/
theorem lemma_5_5_1_counterexample :
    haveI := isMarkovKernel_toTrueKernel
    SampledAccessible toTrueKernel (diracDist 0) {false} {false} ∧
      ¬ UnifAccessible toTrueKernel {false} {false} := by
  have := isMarkovKernel_toTrueKernel
  refine ⟨⟨1, one_pos, fun x hx => ?_⟩, ?_⟩
  · rw [mem_singleton_iff.1 hx, sampledKernel_diracDist, pow_zero_apply]
    simp
  · rintro ⟨δ, hδ, h⟩
    have h0 : hitProb toTrueKernel {false} false = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := (hitProb_pos_iff toTrueKernel (measurableSet_singleton false) false).1
        (pos_iff_ne_zero.2 hne)
      rw [pow_succ_apply' _ n false (measurableSet_singleton false)] at hn
      simp [toTrueKernel] at hn
    exact hδ.ne' (le_antisymm ((h false rfl).trans h0.le) zero_le)

/-- **Lemma 5.5.2 (ii)** (MT p. 116): if `A ⇝ᵃ B` and `B ⇝ᵇ C` then `A ⇝^{a∗b} C`. -/
theorem lemma_5_5_2_ii (P : Kernel X X) {a b : ℕ → ℝ≥0∞} {A B C : Set X}
    (hC : MeasurableSet C) (hab : SampledAccessible P a A B)
    (hbc : SampledAccessible P b B C) : SampledAccessible P (sampleConv a b) A C := by
  obtain ⟨δa, hδa, ha⟩ := hab
  obtain ⟨δb, hδb, hb⟩ := hbc
  refine ⟨δa * δb, ENNReal.mul_pos hδa.ne' hδb.ne', fun x hx => ?_⟩
  rw [lemma_5_5_2_i P a b x hC]
  calc δa * δb ≤ sampledKernel P a x B * δb := by gcongr; exact ha x hx
    _ = ∫⁻ _ in B, δb ∂sampledKernel P a x := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in B, sampledKernel P b y C ∂sampledKernel P a x :=
        setLIntegral_mono (Kernel.measurable_coe _ hC) fun y hy => hb y hy
    _ ≤ ∫⁻ y, sampledKernel P b y C ∂sampledKernel P a x := setLIntegral_le_lintegral _ _

/-- **Lemma 5.5.2 (iii)** (5.47), MT p. 116: `U(x, A) ≥ ∫ U(x, dy) K_a(y, A)`. -/
theorem lemma_5_5_2_iii (P : Kernel X X) {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) (x : X)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ y, sampledKernel P a y A ∂potKernel P x ≤ potKernel P x A := by
  have hU : potKernel P x = Measure.sum fun m => (P ^ (m + 1)) x := by
    rw [potKernel, Kernel.sum_apply]
  rw [hU, lintegral_sum_measure, Measure.sum_apply _ hA]
  simp_rw [sampledKernel_apply P a _ hA]
  calc ∑' m, ∫⁻ y, ∑' n, a n * (P ^ n) y A ∂(P ^ (m + 1)) x
      = ∑' m, ∑' n, a n * (P ^ (m + 1 + n)) x A := by
        refine tsum_congr fun m => ?_
        rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable]
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA),
          Kernel.pow_add_apply_eq_lintegral P (m + 1) n x hA]
    _ = ∑' n, a n * ∑' m, (P ^ (m + n + 1)) x A := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun n => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun m => ?_
        rw [show m + 1 + n = m + n + 1 by omega]
    _ ≤ ∑' n, a n * ∑' k, (P ^ (k + 1)) x A := by
        refine ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl ?_
        exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun m => m + n)
          (add_left_injective n) (fun k => (P ^ (k + 1)) x A)
    _ = ∑' k, (P ^ (k + 1)) x A := by rw [ENNReal.tsum_mul_right, ha, one_mul]

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Petite sets (MT §5.5.2–5.5.3)

Meyn and Tweedie, §5.5.2–5.5.3, pp. 117–121.

* `IsPetiteSet P a ν C` (p. 117): `C` is `ν_a`-petite, `K_a(x, ·) ≥ ν_a` on `C` for a sampling
  distribution `a` and a nonzero `ν_a`; `IsPetite P C`.
* **Proposition 5.5.3** (`proposition_5_5_3`, p. 118): a `ν_m`-small set is `ν_{δ_m}`-petite.
* `smul_le_comp_of_le_on`: `μ(C) ν ≤ μK` when `K(y, ·) ≥ ν` on `C`; `lintegral_pos_of_pos`.
* **Proposition 5.5.4** (p. 118): (i) `proposition_5_5_4_i`, if `A` is `ν_a`-petite and `D ⇝ᵇ A`
  then `D` is petite for `b ∗ a`, with a multiple of `ν_a`; (ii) `proposition_5_5_4_ii`, the
  petite measure of a petite set in `B⁺(X)` is an irreducibility measure.
* **Proposition 5.5.5** (p. 118), on a countably generated space: (i) `proposition_5_5_5_i`,
  every petite set is `ψ_b`-petite for a maximal irreducibility measure `ψ_b`; (ii)
  `proposition_5_5_5_ii`, the union of two petite sets is petite; (iii) `proposition_5_5_5_iii`,
  `K_c(x, ·) ≥ s(x) ψ_c` with `s > 0` measurable and `ψ_c` maximal, and
  `proposition_5_5_5_iii_cover`: `X` is the increasing union of the `ψ_c`-petite sets
  `{s ≥ (n + 1)⁻¹}`.
* **Proposition 5.5.6 (i)** (`proposition_5_5_6_i`, p. 120): a petite set is petite for a uniform
  sampling distribution on `{1, …, N}` (which has finite mean) and for every geometric `a_ε`.
* **Theorem 5.5.7** (`theorem_5_5_7`, p. 120): for an aperiodic `ψ`-irreducible chain on a
  countably generated space, every petite set is small.

**Corrections and hypotheses.** Propositions 5.5.5–5.5.6 and Theorem 5.5.7 use the existence of a
small set in `B⁺(X)` (Theorem 5.2.2), hence a countably generated `B(X)`. In the proof of
Proposition 5.5.6 (i) the book's bound `Σ_{k ≤ N} Pᵏ(x, A) ≥ ½ ψ_b(A)` follows from a tail bound
on `b`, which is how it is proved here.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- `C` is **`ν_a`-petite** (MT p. 117): `a` is a sampling distribution, `ν ≠ 0`, and
`K_a(x, ·) ≥ ν` for every `x ∈ C`. -/
def IsPetiteSet (P : Kernel X X) (a : ℕ → ℝ≥0∞) (ν : Measure X) (C : Set X) : Prop :=
  MeasurableSet C ∧ IsSamplingDist a ∧ ν ≠ 0 ∧ ∀ x ∈ C, ν ≤ sampledKernel P a x

/-- `C` is **petite** if it is `ν_a`-petite for some `a` and `ν`. -/
def IsPetite (P : Kernel X X) (C : Set X) : Prop := ∃ a ν, IsPetiteSet P a ν C

/-- **Proposition 5.5.3** (MT p. 118): a `ν_m`-small set is `ν_{δ_m}`-petite. -/
theorem proposition_5_5_3 {P : Kernel X X} {m : ℕ} {ν : Measure X} {C : Set X}
    (h : IsSmallSet P m ν C) : IsPetiteSet P (diracDist m) ν C :=
  ⟨h.1, isSamplingDist_diracDist m, h.2.2.1, fun x hx => by
    rw [sampledKernel_diracDist]; exact h.2.2.2 x hx⟩

/-- `μ(C) ν ≤ μK` when `K(y, ·) ≥ ν` for every `y ∈ C`. -/
theorem smul_le_comp_of_le_on {Y : Type*} [MeasurableSpace Y] (K : Kernel X Y) (μ : Measure X)
    {C : Set X} {ν : Measure Y} (h : ∀ y ∈ C, ν ≤ K y) : μ C • ν ≤ K ∘ₘ μ :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hB K.aemeasurable]
    calc μ C * ν B = ∫⁻ _ in C, ν B ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in C, K y B ∂μ := setLIntegral_mono (Kernel.measurable_coe _ hB) fun y hy =>
          h y hy B
      _ ≤ ∫⁻ y, K y B ∂μ := setLIntegral_le_lintegral _ _

/-- The integral of an everywhere positive function against a nonzero measure is positive. -/
theorem lintegral_pos_of_pos {μ : Measure X} (hμ : μ ≠ 0) {f : X → ℝ≥0∞} (hf : Measurable f)
    (h : ∀ x, 0 < f x) : 0 < ∫⁻ x, f x ∂μ := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hf]
  intro h0
  have : ∀ᵐ x ∂μ, False := h0.mono fun x hx => (h x).ne' hx
  exact hμ (ae_eq_bot.1 (by simpa using this))

/-- **Proposition 5.5.4 (i)** (MT p. 118): if `A` is `ν_a`-petite and `D ⇝ᵇ A`, then `D` is
`ν_{b∗a}`-petite with `ν_{b∗a} = δ ν_a`: `K_{b∗a}(x, B) ≥ ∫_A K_b(x, dy) K_a(y, B) ≥ δ ν_a(B)`
(5.49). -/
theorem proposition_5_5_4_i (P : Kernel X X) {a b : ℕ → ℝ≥0∞} {ν : Measure X} {A D : Set X}
    (hA : IsPetiteSet P a ν A) (hD : MeasurableSet D) (hb : IsSamplingDist b)
    (hDA : SampledAccessible P b D A) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ IsPetiteSet P (sampleConv b a) (δ • ν) D := by
  obtain ⟨δ, hδ, h⟩ := hDA
  refine ⟨δ, hδ, hD, isSamplingDist_sampleConv hb hA.2.1, smul_measure_ne_zero hA.2.2.1 hδ.ne',
    fun x hx => ?_⟩
  rw [sampledKernel_sampleConv, Kernel.comp_apply]
  exact (smul_measure_le_smul (h x hx) ν).trans (smul_le_comp_of_le_on _ _ hA.2.2.2)

/-- **Proposition 5.5.4 (ii)** (MT p. 118): for a `ψ`-irreducible chain, the minorizing measure
of a `ν_a`-petite set `A ∈ B⁺(X)` is an irreducibility measure. -/
theorem proposition_5_5_4_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {A : Set X}
    (hA : IsPetiteSet P a ν A) (hψA : 0 < ψ A) : IsPhiIrreducible P ν := by
  intro B hB hνB x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA.1 x).1 (hψ A hA.1 hψA x)
  -- `Pⁿ⁺¹ K_a(x, B) ≥ Pⁿ⁺¹(x, A) ν(B) > 0`
  have h1 : 0 < ∫⁻ y, sampledKernel P a y B ∂(P ^ (n + 1)) x := by
    have := smul_le_comp_of_le_on (sampledKernel P a) ((P ^ (n + 1)) x) hA.2.2.2
    have h2 := this B
    rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hB (Kernel.aemeasurable _)] at h2
    exact (ENNReal.mul_pos hn.ne' hνB.ne').trans_le h2
  simp_rw [sampledKernel_apply P a _ hB] at h1
  rw [lintegral_tsum fun k => ((Kernel.measurable_coe _ hB).const_mul _).aemeasurable] at h1
  obtain ⟨k, hk⟩ : ∃ k, 0 < ∫⁻ y, a k * (P ^ k) y B ∂(P ^ (n + 1)) x := by
    by_contra hc
    push Not at hc
    exact h1.ne' (ENNReal.tsum_eq_zero.2 fun k => nonpos_iff_eq_zero.1 (hc k))
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hB),
    ← Kernel.pow_add_apply_eq_lintegral P (n + 1) k x hB] at hk
  refine (hitProb_pos_iff P hB x).2 ⟨n + k, ?_⟩
  rw [show n + k + 1 = n + 1 + k by omega]
  exact pos_of_mul_pos_right hk zero_le

/-! ### Proposition 5.5.5 -/

/-- The geometric distribution `a_{1/2}`: `K_{a_{1/2}}` is `resolventHalf`. -/
theorem sampledKernel_geomDist_half (P : Kernel X X) :
    sampledKernel P (geomDist 2⁻¹) = resolventHalf P := rfl

/-- `a_{1/2}` is a sampling distribution. -/
theorem isSamplingDist_geomDist_half : IsSamplingDist (geomDist 2⁻¹) :=
  isSamplingDist_geomDist (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)

variable [MeasurableSpace.CountablyGenerated X]

/-- **Proposition 5.5.5 (i)** (MT p. 118). On a countably generated space, for a `ψ`-irreducible
chain every `ν_a`-petite set `A` is `ψ_b`-petite for some sampling distribution `b` and some
maximal irreducibility measure `ψ_b`. -/
theorem proposition_5_5_5_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {A : Set X}
    (hA : IsPetiteSet P a ν A) :
    ∃ b ψb, IsPetiteSet P b ψb A ∧ IsMaximalIrreducibility P ψb := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  -- `A ⇝ C` for the sampling distribution `a ∗ a_{1/2}`
  have hKpos : ∀ y, 0 < resolventHalf P y C := fun y =>
    (proposition_4_2_1 P ψ).2.2.1 hψ.2.1 C hC.1 hψC y
  have hδ := lintegral_pos_of_pos hA.2.2.1 (Kernel.measurable_coe _ hC.1) hKpos
  have hacc : SampledAccessible P (sampleConv a (geomDist 2⁻¹)) A C := by
    refine ⟨_, hδ, fun x hx => ?_⟩
    rw [lemma_5_5_2_i P _ _ x hC.1, sampledKernel_geomDist_half]
    exact lintegral_mono' (hA.2.2.2 x hx) le_rfl
  obtain ⟨δ', hδ', hpet⟩ := proposition_5_5_4_i P (proposition_5_5_3 hC) hA.1
    (isSamplingDist_sampleConv hA.2.1 isSamplingDist_geomDist_half) hacc
  -- the petite measure is an irreducibility measure; spread it by `K_{a_{1/2}}`
  have hirr : IsPhiIrreducible P (δ' • νC) :=
    (hC.isPhiIrreducible hψ.2.1 hψC).mono Measure.smul_absolutelyContinuous
  have hmax := isMaximalIrreducibility_maxIrrMeasure P hirr hpet.2.2.1
  refine ⟨sampleConv (sampleConv (sampleConv a (geomDist 2⁻¹)) (diracDist m)) (geomDist 2⁻¹),
    maxIrrMeasure P (δ' • νC), ⟨hA.1, isSamplingDist_sampleConv hpet.2.1
      isSamplingDist_geomDist_half, hmax.1, fun x hx => ?_⟩, hmax⟩
  rw [sampledKernel_sampleConv, Kernel.comp_apply, sampledKernel_geomDist_half]
  exact comp_le_comp _ (hpet.2.2.2 x hx)

/-- **Proposition 5.5.5 (ii)** (MT p. 119). On a countably generated space, for a
`ψ`-irreducible chain the union of two petite sets is petite. -/
theorem proposition_5_5_5_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A₁ A₂ : Set X} (h₁ : IsPetite P A₁)
    (h₂ : IsPetite P A₂) : IsPetite P (A₁ ∪ A₂) := by
  obtain ⟨a₁, ν₁, h₁⟩ := h₁
  obtain ⟨a₂, ν₂, h₂⟩ := h₂
  obtain ⟨b₁, ψ₁, hp₁, hm₁⟩ := proposition_5_5_5_i P hψ h₁
  obtain ⟨b₂, ψ₂, hp₂, hm₂⟩ := proposition_5_5_5_i P hψ h₂
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hψ₁C : 0 < ψ₁ C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hm₁).1 h0)
  have hψ₂C : 0 < ψ₂ C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hm₂).1 h0)
  have hacc : SampledAccessible P (mixDist b₁ b₂) (A₁ ∪ A₂) C := by
    refine ⟨2⁻¹ * min (ψ₁ C) (ψ₂ C), ENNReal.mul_pos (by simp)
      (lt_min hψ₁C hψ₂C).ne', fun x hx => ?_⟩
    rw [sampledKernel_mixDist_apply P _ _ x hC.1]
    rcases hx with hx | hx
    · calc 2⁻¹ * min (ψ₁ C) (ψ₂ C) ≤ 2⁻¹ * sampledKernel P b₁ x C := by
            gcongr
            exact (min_le_left _ _).trans (hp₁.2.2.2 x hx C)
        _ ≤ _ := le_self_add
    · calc 2⁻¹ * min (ψ₁ C) (ψ₂ C) ≤ 2⁻¹ * sampledKernel P b₂ x C := by
            gcongr
            exact (min_le_right _ _).trans (hp₂.2.2.2 x hx C)
        _ ≤ _ := le_add_self
  obtain ⟨δ, -, hpet⟩ := proposition_5_5_4_i P (proposition_5_5_3 hC) (h₁.1.union h₂.1)
    (isSamplingDist_mixDist hp₁.2.1 hp₂.2.1) hacc
  exact ⟨_, _, hpet⟩

/-- **Proposition 5.5.5 (iii)** (MT p. 118). On a countably generated space, for a
`ψ`-irreducible chain there are a sampling distribution `c`, an everywhere positive measurable
`s` and a maximal irreducibility measure `ψ_c` with `K_c(x, B) ≥ s(x) ψ_c(B)` for all `x`, `B`. -/
theorem proposition_5_5_5_iii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ (c : ℕ → ℝ≥0∞) (s : X → ℝ≥0∞) (ψc : Measure X), IsSamplingDist c ∧ Measurable s ∧
      (∀ x, 0 < s x) ∧
      IsMaximalIrreducibility P ψc ∧ ∀ x, s x • ψc ≤ sampledKernel P c x := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨b, ψb, hpet, hmax⟩ := proposition_5_5_5_i P hψ (proposition_5_5_3 hC)
  refine ⟨sampleConv (geomDist 2⁻¹) b, fun x => resolventHalf P x C, ψb,
    isSamplingDist_sampleConv isSamplingDist_geomDist_half hpet.2.1,
    Kernel.measurable_coe _ hC.1, fun x => (proposition_4_2_1 P ψ).2.2.1 hψ.2.1 C hC.1 hψC x,
    hmax, fun x => ?_⟩
  rw [sampledKernel_sampleConv, Kernel.comp_apply, sampledKernel_geomDist_half]
  exact smul_le_comp_of_le_on _ _ hpet.2.2.2

/-- Proposition 5.5.5 (iii), the cover (MT p. 119): the sets `Cₙ = {x : s(x) ≥ (n + 1)⁻¹}`
increase, are `ψ_c`-petite with one sampling distribution `c` and minorizing measure a multiple
of `ψ_c`, and cover `X`. -/
theorem proposition_5_5_5_iii_cover (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ (c : ℕ → ℝ≥0∞) (ψc : Measure X), IsMaximalIrreducibility P ψc ∧ ∃ Cs : ℕ → Set X,
      Monotone Cs ∧ (∀ n : ℕ, IsPetiteSet P c (((n : ℝ≥0∞) + 1)⁻¹ • ψc) (Cs n)) ∧
        ⋃ n, Cs n = univ := by
  obtain ⟨c, s, ψc, hc, hs, hspos, hmax, hle⟩ := proposition_5_5_5_iii P hψ
  refine ⟨c, ψc, hmax, fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ s x}, fun n k hnk x hx => ?_,
    fun n => ⟨measurableSet_le measurable_const hs, hc,
      smul_measure_ne_zero hmax.1 (ENNReal.inv_ne_zero.2 (by simp)), fun x hx =>
        (smul_measure_le_smul hx ψc).trans (hle x)⟩, ?_⟩
  · refine le_trans ?_ (show ((n : ℝ≥0∞) + 1)⁻¹ ≤ s x from hx)
    change ((k : ℝ≥0∞) + 1)⁻¹ ≤ ((n : ℝ≥0∞) + 1)⁻¹
    gcongr
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hspos x).ne'
    refine ⟨n, le_trans ?_ hn.le⟩
    gcongr
    exact le_self_add

/-! ### Tails of sampling distributions -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- The tail of a sampling distribution beyond some `K` is at most any `ε > 0`. -/
theorem exists_tail_le {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, ∑' k, a (k + K) ≤ ε := by
  have h := ENNReal.tendsto_sum_nat_add a (by rw [ha]; exact ENNReal.one_ne_top)
  obtain ⟨K, hK⟩ := (h.eventually (Iio_mem_nhds hε)).exists
  exact ⟨K, le_of_lt hK⟩

omit [MeasurableSpace.CountablyGenerated X] in
/-- If `K_b(x, A) ≥ t`, `2ε ≤ t` and the tail of `b` beyond `K` is at most `ε`, then
`Σ_{k < K} b(k) Pᵏ(x, A) ≥ ε`. -/
theorem le_sum_head (P : Kernel X X) [IsMarkovKernel P] {b : ℕ → ℝ≥0∞} (K : ℕ) (x : X)
    {A : Set X} (hA : MeasurableSet A) {t ε : ℝ≥0∞} (hεt : ε ≠ ∞)
    (htail : ∑' k, b (k + K) ≤ ε) (h2 : 2 * ε ≤ t) (ht : t ≤ sampledKernel P b x A) :
    ε ≤ ∑ k ∈ Finset.range K, b k * (P ^ k) x A := by
  have hsplit : ∑' k, b k * (P ^ k) x A = ∑ k ∈ Finset.range K, b k * (P ^ k) x A +
      ∑' k, b (k + K) * (P ^ (k + K)) x A :=
    (Summable.sum_add_tsum_nat_add' (f := fun k => b k * (P ^ k) x A) (k := K)
      ENNReal.summable).symm
  rw [sampledKernel_apply P b x hA, hsplit] at ht
  have htl : ∑' k, b (k + K) * (P ^ (k + K)) x A ≤ ε := by
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) htail
    have := isMarkovKernel_pow P (k + K)
    exact mul_le_of_le_one_right' prob_le_one
  have h3 : ε + ε ≤ (∑ k ∈ Finset.range K, b k * (P ^ k) x A) + ε := by
    calc ε + ε = 2 * ε := (two_mul ε).symm
      _ ≤ t := h2
      _ ≤ _ := ht.trans (add_le_add_right htl _)
  exact (ENNReal.add_le_add_iff_right hεt).1 h3

omit [MeasurableSpace.CountablyGenerated X] in
/-- The constant `ε₀ = ½ min(t, 1)` used in the tail estimates. -/
theorem half_min_spec {t : ℝ≥0∞} (ht : 0 < t) :
    0 < 2⁻¹ * min t 1 ∧ 2⁻¹ * min t 1 ≠ ∞ ∧ 2 * (2⁻¹ * min t 1) ≤ t := by
  refine ⟨ENNReal.mul_pos (by simp) (lt_min ht one_pos).ne', ENNReal.mul_ne_top (by simp)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)), ?_⟩
  rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact min_le_left _ _

/-- The core estimate of Proposition 5.5.6 (i) (MT p. 120): for a petite `C` there are `N ≥ 1`,
a constant `ε₀ > 0` and a nonzero `νₙ` with `Σ_{j=1}^{N} Pʲ(x, B) ≥ ε₀ νₙ(B)` for `x ∈ C`. -/
theorem exists_sum_Icc_pow_ge (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {C : Set X}
    (hC : IsPetiteSet P a ν C) :
    ∃ N, 1 ≤ N ∧ ∃ ε₀ : ℝ≥0∞, 0 < ε₀ ∧ ∃ νₙ : Measure X, νₙ ≠ 0 ∧
      ∀ x ∈ C, ∀ B, MeasurableSet B → ε₀ * νₙ B ≤ ∑ j ∈ Finset.Icc 1 N, (P ^ j) x B := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨A, -, n, νₙ, hA, hψA, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨b, ψb, hpet, hmax⟩ := proposition_5_5_5_i P hψ hC
  have ht : 0 < ψb A := pos_iff_ne_zero.2 fun h0 => hψA.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψb A) 1
  obtain ⟨K, hK⟩ := exists_tail_le hpet.2.1 hε0
  refine ⟨K + n, by have := hA.2.1; omega, ε₀, hε0, νₙ, hA.2.2.1, fun x hx B hB => ?_⟩
  have hhead := le_sum_head P K x hA.1 hεt hK h2 (hpet.2.2.2 x hx A)
  have hb1 : ∀ k, b k ≤ 1 := fun k => hpet.2.1 ▸ ENNReal.le_tsum k
  calc ε₀ * νₙ B ≤ (∑ k ∈ Finset.range K, b k * (P ^ k) x A) * νₙ B := by gcongr
    _ = ∑ k ∈ Finset.range K, b k * ((P ^ k) x A * νₙ B) := by
        rw [Finset.sum_mul]; simp_rw [mul_assoc]
    _ ≤ ∑ k ∈ Finset.range K, (P ^ (k + n)) x B := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact (mul_le_of_le_one_left' (hb1 k)).trans (pow_add_ge_of_le P hA.2.2.2 x hB)
    _ = ∑ j ∈ (Finset.range K).image (· + n), (P ^ j) x B :=
        (Finset.sum_image (f := fun j => (P ^ j) x B) (g := (· + n))
          fun i _ j _ h => Nat.add_right_cancel h).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 (K + n), (P ^ j) x B := by
        refine Finset.sum_le_sum_of_subset fun j hj => ?_
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hj
        have := hA.2.1
        rw [Finset.mem_range] at hk
        rw [Finset.mem_Icc]
        omega

/-- **Proposition 5.5.6 (i)** (MT p. 120). On a countably generated space, for a
`ψ`-irreducible chain, a petite set is petite for a uniform sampling distribution
`a(i) = 1/N`, `1 ≤ i ≤ N` (which has finite mean), and for every geometric distribution `a_ε`,
`0 < ε < 1`. -/
theorem proposition_5_5_6_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {C : Set X}
    (hC : IsPetiteSet P a ν C) :
    (∃ N, 1 ≤ N ∧ (∃ ν', IsPetiteSet P (uniformDist N) ν' C) ∧
      ∑' n : ℕ, (n : ℝ≥0∞) * uniformDist N n ≠ ∞) ∧
      ∀ ε : ℝ≥0∞, 0 < ε → ε < 1 → ∃ ν'', IsPetiteSet P (geomDist ε) ν'' C := by
  obtain ⟨N, hN, ε₀, hε₀, νₙ, hνₙ, hsum⟩ := exists_sum_Icc_pow_ge P hψ hC
  refine ⟨⟨N, hN, ⟨((N : ℝ≥0∞)⁻¹ * ε₀) • νₙ, hC.1, isSamplingDist_uniformDist hN,
    smul_measure_ne_zero hνₙ (ENNReal.mul_pos (by simp) hε₀.ne').ne', fun x hx =>
      Measure.le_intro fun B hB _ => ?_⟩, tsum_mul_uniformDist_ne_top N⟩, fun ε hε0 hε1 => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, sampledKernel_uniformDist_apply P N x hB, mul_assoc]
    gcongr
    exact hsum x hx B hB
  · refine ⟨((1 - ε) * ε ^ N * ε₀) • νₙ, hC.1, isSamplingDist_geomDist hε1,
      smul_measure_ne_zero hνₙ (ENNReal.mul_pos (ENNReal.mul_pos (tsub_pos_of_lt hε1).ne'
        (pow_ne_zero _ hε0.ne')).ne' hε₀.ne').ne', fun x hx => Measure.le_intro fun B hB _ => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, sampledKernel_geomDist, resolvent_apply P ε x hB,
      mul_assoc, mul_assoc]
    gcongr
    calc ε ^ N * (ε₀ * νₙ B) ≤ ε ^ N * ∑ j ∈ Finset.Icc 1 N, (P ^ j) x B := by
          gcongr; exact hsum x hx B hB
      _ = ∑ j ∈ Finset.Icc 1 N, ε ^ N * (P ^ j) x B := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 N, ε ^ j * (P ^ j) x B := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul' (pow_le_pow_right_of_le_one' hε1.le (Finset.mem_Icc.1 hj).2) le_rfl
      _ ≤ ∑' j, ε ^ j * (P ^ j) x B := ENNReal.sum_le_tsum _

/-- **Theorem 5.5.7** (MT p. 120). On a countably generated space, if a `ψ`-irreducible chain is
aperiodic then every petite set is small. -/
theorem theorem_5_5_7 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {A : Set X}
    (hA : IsPetite P A) : IsSmall P A := by
  obtain ⟨a', ν', hpet'⟩ := hA
  obtain ⟨a, ψa, hpet, hmax⟩ := proposition_5_5_5_i P hψ hpet'
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  have ht : 0 < ψa C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψa C) 1
  obtain ⟨K, hK⟩ := exists_tail_le hpet.2.1 hε0
  -- the times `n₀ − k`, `k < K`, all lie in `E_C`
  choose δ hδ hδle using fun k => (hN (N + (K - k) + 1) (by omega)).2
  set δ' := min ((Finset.range K).inf δ) 1
  have hδ' : 0 < δ' := lt_min ((Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun k _ => hδ k)
    one_pos
  refine ⟨N + K + 1, (ε₀ * δ') • ν, hpet.1, by omega,
    smul_measure_ne_zero hC.2.2.1 (ENNReal.mul_pos hε0.ne' hδ'.ne').ne', fun x hx =>
      Measure.le_intro fun B hB _ => ?_⟩
  have hbound : ∀ k ∈ Finset.range K, (P ^ k) x C * (δ' * ν B) ≤ (P ^ (N + K + 1)) x B :=
    fun k hk => by
      have hk' := Finset.mem_range.1 hk
      have hle : ∀ y ∈ C, δ' • ν ≤ (P ^ (N + (K - k) + 1)) y := fun y hy =>
        (smul_measure_le_smul ((min_le_left _ _).trans (Finset.inf_le hk)) ν).trans (hδle k y hy)
      have := pow_add_ge_of_le P (m := k) hle x hB
      rw [show k + (N + (K - k) + 1) = N + K + 1 by omega, Measure.smul_apply,
        smul_eq_mul] at this
      exact this
  have hhead := le_sum_head P K x hC.1 hεt hK h2 (hpet.2.2.2 x hx C)
  have hsum1 : ∑ k ∈ Finset.range K, a k ≤ 1 := hpet.2.1 ▸ ENNReal.sum_le_tsum _
  rw [Measure.smul_apply, smul_eq_mul, mul_assoc]
  calc ε₀ * (δ' * ν B) ≤ (∑ k ∈ Finset.range K, a k * (P ^ k) x C) * (δ' * ν B) := by gcongr
    _ = ∑ k ∈ Finset.range K, a k * ((P ^ k) x C * (δ' * ν B)) := by
        rw [Finset.sum_mul]; simp_rw [mul_assoc]
    _ ≤ ∑ k ∈ Finset.range K, a k * (P ^ (N + K + 1)) x B :=
        Finset.sum_le_sum fun k hk => by gcongr; exact hbound k hk
    _ = (∑ k ∈ Finset.range K, a k) * (P ^ (N + K + 1)) x B := (Finset.sum_mul _ _ _).symm
    _ ≤ (P ^ (N + K + 1)) x B := mul_le_of_le_one_left' hsum1

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Spread-out random walks (MT §5.3.2, Proposition 5.3.1)

Meyn and Tweedie, §5.3.2, p. 107. A random walk on `ℝ` is spread out (RW2) if some convolution
power `Γ^{n∗}` is not singular with respect to Lebesgue measure (`IsSpreadOut`, Chapter 3).

* `exists_lebesgue_minorant`: a finite measure on `ℝ` that is not singular with respect to
  Lebesgue measure dominates `η μ_Leb|_E` for some `η > 0` and some bounded `E` with
  `μ_Leb(E) > 0`.
* `selfConv E u = μ_Leb(E ∩ (u − E))`, the self-convolution of `1_E`;
  `lintegral_selfConv`: `∫ selfConv E = μ_Leb(E)²`, so it is positive somewhere;
  `eventually_lt_selfConv`: it is lower semicontinuous (by continuity of translation in measure,
  Mathlib's `tendsto_measure_symmDiff_preimage_nhds_zero`). Together these replace Lemma D.4.3
  (continuity of `γ ∗ γ`) in the book's proof.
* `randomWalk_pow_two_mul_ge`: `P²ⁿ(x, B) ≥ η² ∫_B selfConv E (u − x) du`, the bound (5.28).
* **Proposition 5.3.1** (`proposition_5_3_1`, p. 107): for a spread-out random walk there are
  `β > 0`, an interval `[s, t]` and `ε > 0` such that `[−β, β]` is `ν₂ₙ`-small with
  `ν₂ₙ = ε μ_Leb|_{[s, t]}`.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology symmDiff

/-! ### A Lebesgue minorant -/

/-- A finite measure on `ℝ` which is not singular with respect to Lebesgue measure dominates
`η μ_Leb|_E` for some `η > 0` and some bounded measurable `E` with `μ_Leb(E) > 0`. -/
theorem exists_lebesgue_minorant {μ : Measure ℝ} [IsFiniteMeasure μ] (h : ¬ μ ⟂ₘ volume) :
    ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧ volume E ≠ ∞ ∧
      ∃ η : ℝ≥0∞, 0 < η ∧ η • volume.restrict E ≤ μ := by
  set f := μ.rnDeriv volume with hf
  have hfm : Measurable f := Measure.measurable_rnDeriv μ volume
  have hwd : volume.withDensity f ≠ 0 := fun h0 => h ((Measure.withDensity_rnDeriv_eq_zero μ
    volume).1 h0)
  set L : ℕ → ℕ → Set ℝ := fun k R => {x | ((k : ℝ≥0∞) + 1)⁻¹ ≤ f x} ∩ Icc (-(R : ℝ)) R
  have hLm : ∀ k R, MeasurableSet (L k R) := fun k R =>
    (measurableSet_le measurable_const hfm).inter measurableSet_Icc
  obtain ⟨k, R, hkR⟩ : ∃ k R, 0 < volume (L k R) := by
    by_contra hc
    push Not at hc
    apply hwd
    have hnull : volume {x | f x ≠ 0} = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun k =>
        measure_iUnion_null fun R => nonpos_iff_eq_zero.1 (hc k R))
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx
      obtain ⟨R, hR⟩ := exists_nat_ge |x|
      refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨R, ?_, ?_⟩⟩
      · refine le_trans ?_ hk.le
        change ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹
        gcongr
        exact le_self_add
      · rw [mem_Icc, ← abs_le]; exact hR
    have hae : f =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simpa using hnull
    rw [withDensity_congr_ae hae, withDensity_zero]
  refine ⟨L k R, hLm k R, hkR, ne_top_of_le_ne_top (by simp [Real.volume_Icc])
    (measure_mono inter_subset_right), ((k : ℝ≥0∞) + 1)⁻¹, ENNReal.inv_pos.2 (by simp),
    Measure.le_intro fun B hB _ => ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  calc ((k : ℝ≥0∞) + 1)⁻¹ * volume (B ∩ L k R) = ∫⁻ _ in B ∩ L k R, ((k : ℝ≥0∞) + 1)⁻¹ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in B ∩ L k R, f x := setLIntegral_mono' (hB.inter (hLm k R)) fun x hx => hx.2.1
    _ ≤ ∫⁻ x in B, f x := lintegral_mono_set inter_subset_left
    _ = volume.withDensity f B := (withDensity_apply _ hB).symm
    _ ≤ μ B := Measure.withDensity_rnDeriv_le μ volume B

/-! ### The self-convolution of an indicator -/

/-- `selfConv E u = μ_Leb(E ∩ (u − E)) = ∫ 1_E(v) 1_E(u − v) dv`. -/
noncomputable def selfConv (E : Set ℝ) (u : ℝ) : ℝ≥0∞ := volume (E ∩ {v | u - v ∈ E})

/-- The integrand form of `selfConv`. -/
theorem selfConv_eq_lintegral {E : Set ℝ} (hE : MeasurableSet E) (u : ℝ) :
    selfConv E u = ∫⁻ v, E.indicator 1 v * E.indicator 1 (u - v) := by
  have hm : MeasurableSet {v | u - v ∈ E} := (measurable_const.sub measurable_id) hE
  rw [selfConv, ← lintegral_indicator_one (hE.inter hm)]
  refine lintegral_congr fun v => ?_
  by_cases h1 : v ∈ E <;> by_cases h2 : u - v ∈ E <;> simp [h1, h2, indicator]

/-- `∫ selfConv E = μ_Leb(E)²`. -/
theorem lintegral_selfConv {E : Set ℝ} (hE : MeasurableSet E) :
    ∫⁻ u, selfConv E u = volume E * volume E := by
  simp_rw [selfConv_eq_lintegral hE]
  have hmeas : Measurable (Function.uncurry fun (u v : ℝ) =>
      E.indicator (1 : ℝ → ℝ≥0∞) v * E.indicator 1 (u - v)) :=
    ((measurable_one.indicator hE).comp measurable_snd).mul
      ((measurable_one.indicator hE).comp (measurable_fst.sub measurable_snd))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h1 : ∀ v, ∫⁻ u, E.indicator (1 : ℝ → ℝ≥0∞) v * E.indicator 1 (u - v) =
      E.indicator 1 v * volume E := fun v => by
    rw [lintegral_const_mul' _ _ (by by_cases hv : v ∈ E <;> simp [hv]),
      lintegral_sub_right_eq_self (fun u => E.indicator (1 : ℝ → ℝ≥0∞) u) v,
      lintegral_indicator_one hE]
  simp_rw [h1]
  rw [lintegral_mul_const _ (measurable_one.indicator hE), lintegral_indicator_one hE]

/-- `selfConv E` is lower semicontinuous: if `c < selfConv E u₀` then `c < selfConv E u` for all
`u` near `u₀`. This follows from the continuity of translation in measure. -/
theorem eventually_lt_selfConv {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ∞)
    {u₀ : ℝ} {c : ℝ≥0∞} (hc : c < selfConv E u₀) : ∀ᶠ u in 𝓝 u₀, c < selfConv E u := by
  set g : ℝ → C(ℝ, ℝ) := ⇑(ContinuousMap.curry ⟨fun q : ℝ × ℝ => q.2 - q.1, by fun_prop⟩)
    with hg
  set S : Set ℝ := {x | -x ∈ E} with hS
  have hSm : MeasurableSet S := measurable_neg hE
  have hSfin : volume S ≠ ∞ := by
    rw [hS, show {x : ℝ | -x ∈ E} = -E from rfl, Measure.measure_neg]
    exact hfin
  have hpre : ∀ u, ⇑(g u) ⁻¹' S = {v | u - v ∈ E} := fun u => by
    ext v
    simp [hg, hS]
  have hfg : Tendsto g (𝓝 u₀) (𝓝 (g u₀)) := (ContinuousMap.curry _).continuous.tendsto u₀
  have hmp : ∀ u, MeasurePreserving (g u) volume volume := fun u =>
    measurePreserving_sub_right volume u
  have hvol := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume) hfg
    (Eventually.of_forall hmp) (hmp u₀) hSm.nullMeasurableSet hSfin
  have hε : 0 < selfConv E u₀ - c := tsub_pos_of_lt hc
  filter_upwards [hvol.eventually (gt_mem_nhds hε)] with u hu
  have hle : selfConv E u₀ ≤ selfConv E u + volume ((g u ⁻¹' S) ∆ (g u₀ ⁻¹' S)) := by
    rw [selfConv, selfConv, ← hpre, ← hpre]
    calc volume (E ∩ g u₀ ⁻¹' S)
        ≤ volume ((E ∩ g u ⁻¹' S) ∪ ((g u ⁻¹' S) ∆ (g u₀ ⁻¹' S))) := measure_mono fun v hv => by
          by_cases h : v ∈ g u ⁻¹' S
          · exact Or.inl ⟨hv.1, h⟩
          · exact Or.inr (Or.inr ⟨hv.2, h⟩)
      _ ≤ _ := measure_union_le _ _
  by_contra hcon
  push Not at hcon
  have : selfConv E u₀ < selfConv E u₀ :=
    calc selfConv E u₀ ≤ c + volume ((g u ⁻¹' S) ∆ (g u₀ ⁻¹' S)) :=
          hle.trans (add_le_add_left hcon _)
      _ < c + (selfConv E u₀ - c) := ENNReal.add_lt_add_left hc.ne_top hu
      _ = selfConv E u₀ := add_tsub_cancel_of_le hc.le
  exact lt_irrefl _ this

/-! ### The bound (5.28) -/

/-- The bound (5.28), MT p. 107: if `Γ^{n∗} ≥ η μ_Leb|_E`, then
`P²ⁿ(x, B) ≥ η² ∫_B μ_Leb(E ∩ (u − x − E)) du`. -/
theorem randomWalk_pow_two_mul_ge (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {n : ℕ} {E : Set ℝ}
    (hE : MeasurableSet E) {η : ℝ≥0∞} (hle : η • volume.restrict E ≤ convPow Γ n) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    η * η * ∫⁻ u in B, selfConv E (u - x) ≤ (randomWalkKernel Γ ^ (n + n)) x B := by
  have iE : Measurable (E.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hE
  have iB : Measurable (B.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hB
  -- `F(y) = μ_Leb(E ∩ (B − y))`
  set F : ℝ → ℝ≥0∞ := fun y => ∫⁻ w, E.indicator 1 w * B.indicator 1 (y + w) with hF
  have hFm : Measurable F := by
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
      E.indicator (1 : ℝ → ℝ≥0∞) p.2 * B.indicator 1 (p.1 + p.2)) ?_
    exact (iE.comp measurable_snd).mul (iB.comp (measurable_fst.add measurable_snd))
  have hy : ∀ y, η * F y ≤ (randomWalkKernel Γ ^ n) y B := fun y => by
    have hpre : MeasurableSet {w | y + w ∈ B} := (measurable_const_add y) hB
    rw [randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add y) hB]
    have h1 := hle {w | y + w ∈ B}
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hpre] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [hF, ← lintegral_indicator_one (hpre.inter hE)]
    congr 1
    refine lintegral_congr fun w => ?_
    by_cases h1 : w ∈ E <;> by_cases h2 : y + w ∈ B <;> simp [h1, h2, indicator]
  -- integrate against `Pⁿ(x, ·) ≥ η μ_Leb|_E` shifted by `x`
  have hstep : η * ∫⁻ v in E, η * F (x + v) ≤ ∫⁻ y, (randomWalkKernel Γ ^ n) y B
      ∂(randomWalkKernel Γ ^ n) x := by
    rw [randomWalkKernel_pow_apply, lintegral_map (Kernel.measurable_coe _ hB)
      (measurable_const_add x)]
    calc η * ∫⁻ v in E, η * F (x + v) = ∫⁻ v, η * F (x + v) ∂(η • volume.restrict E) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ v, η * F (x + v) ∂convPow Γ n := lintegral_mono' hle le_rfl
      _ ≤ ∫⁻ v, (randomWalkKernel Γ ^ n) (x + v) B ∂convPow Γ n :=
          lintegral_mono fun v => hy (x + v)
  -- the change of variables `u = x + v + w`
  have hcv : ∫⁻ v in E, F (x + v) = ∫⁻ u in B, selfConv E (u - x) := by
    have h1 : ∀ v, F (x + v) = ∫⁻ u, E.indicator 1 (u - (x + v)) * B.indicator 1 u := fun v => by
      rw [hF]
      simp only
      rw [← lintegral_sub_right_eq_self (fun w => E.indicator (1 : ℝ → ℝ≥0∞) w *
        B.indicator 1 (x + v + w)) (x + v)]
      simp only [add_sub_cancel]
    rw [← lintegral_indicator hE]
    have h2 : ∀ v, E.indicator (fun v => F (x + v)) v =
        ∫⁻ u, E.indicator 1 v * (E.indicator 1 (u - (x + v)) * B.indicator 1 u) := fun v => by
      rw [lintegral_const_mul' _ _ (by by_cases hv : v ∈ E <;> simp [hv]), ← h1]
      by_cases hv : v ∈ E <;> simp [hv]
    simp_rw [h2]
    have hmeas : Measurable (Function.uncurry fun (v u : ℝ) =>
        E.indicator (1 : ℝ → ℝ≥0∞) v * (E.indicator 1 (u - (x + v)) * B.indicator 1 u)) :=
      (iE.comp measurable_fst).mul ((iE.comp (measurable_snd.sub
        (measurable_const.add measurable_fst))).mul (iB.comp measurable_snd))
    rw [lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_indicator hB]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ B
    · have hR : B.indicator (fun u => selfConv E (u - x)) u = selfConv E (u - x) :=
        indicator_of_mem hu _
      rw [hR, selfConv_eq_lintegral hE]
      refine lintegral_congr fun v => ?_
      rw [indicator_of_mem hu, Pi.one_apply, mul_one, show u - (x + v) = u - x - v by ring]
    · rw [indicator_of_notMem hu]
      simp [hu]
  rw [Kernel.pow_add_apply_eq_lintegral _ n n x hB]
  calc η * η * ∫⁻ u in B, selfConv E (u - x) = η * ∫⁻ v in E, η * F (x + v) := by
        rw [lintegral_const_mul η (f := fun v => F (x + v)) (hFm.comp (measurable_const_add x)),
          hcv, mul_assoc]
    _ ≤ _ := hstep

/-! ### Proposition 5.3.1 -/

/-- **Proposition 5.3.1** (MT p. 107). If the random walk is spread out, with `Γ^{n∗}` not
singular with respect to Lebesgue measure, there are `β > 0`, an interval `[s, t]` and `ε > 0`
such that `C_β = [−β, β]` is `ν₂ₙ`-small with `ν₂ₙ = ε μ_Leb|_{[s, t]}`. -/
theorem proposition_5_3_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : IsSpreadOut Γ) :
    ∃ n, 1 ≤ n ∧ ∃ β : ℝ, 0 < β ∧ ∃ s t : ℝ, s < t ∧ ∃ ε : ℝ≥0∞, 0 < ε ∧
      IsSmallSet (randomWalkKernel Γ) (2 * n) (ε • volume.restrict (Icc s t)) (Icc (-β) β) := by
  obtain ⟨n, hn, hns⟩ := h
  have : IsFiniteMeasure (convPow Γ n) := by unfold convPow; infer_instance
  obtain ⟨E, hEm, hEpos, hEfin, η, hη, hle⟩ := exists_lebesgue_minorant hns
  -- a point where the self-convolution is positive
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, 0 < selfConv E u₀ := by
    by_contra hc
    push Not at hc
    have h0 : ∫⁻ u, selfConv E u = 0 := by
      rw [lintegral_congr fun u => nonpos_iff_eq_zero.1 (hc u), lintegral_zero]
    rw [lintegral_selfConv hEm] at h0
    exact (ENNReal.mul_pos hEpos.ne' hEpos.ne').ne' h0
  have hcfin : selfConv E u₀ ≠ ⊤ := ne_top_of_le_ne_top hEfin (measure_mono inter_subset_left)
  have hc0 : 0 < selfConv E u₀ / 2 := ENNReal.div_pos hu₀.ne' (by simp)
  have hclt : selfConv E u₀ / 2 < selfConv E u₀ := ENNReal.half_lt_self hu₀.ne' hcfin
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_lt_selfConv hEm hEfin hclt)
  refine ⟨n, hn, r / 4, by positivity, u₀ - r / 4, u₀ + r / 4, by linarith,
    η * η * (selfConv E u₀ / 2), ENNReal.mul_pos (ENNReal.mul_pos hη.ne' hη.ne').ne' hc0.ne',
    measurableSet_Icc, by omega, smul_measure_ne_zero ?_ (ENNReal.mul_pos (ENNReal.mul_pos
      hη.ne' hη.ne').ne' hc0.ne').ne', fun x hx => Measure.le_intro fun B hB _ => ?_⟩
  · rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]
    linarith
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB, two_mul]
  refine le_trans ?_ (randomWalk_pow_two_mul_ge Γ hEm hle x hB)
  rw [mul_assoc]
  gcongr
  calc selfConv E u₀ / 2 * volume (B ∩ Icc (u₀ - r / 4) (u₀ + r / 4))
      = ∫⁻ _ in B ∩ Icc (u₀ - r / 4) (u₀ + r / 4), selfConv E u₀ / 2 := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ u in B ∩ Icc (u₀ - r / 4) (u₀ + r / 4), selfConv E (u - x) := by
        refine setLIntegral_mono' (hB.inter measurableSet_Icc) fun u hu => (hball ?_).le
        rw [Real.dist_eq]
        have h1 := hu.2.1
        have h2 := hu.2.2
        have h3 := hx.1
        have h4 := hx.2
        rw [abs_lt]
        constructor <;> linarith
    _ ≤ ∫⁻ u in B, selfConv E (u - x) := lintegral_mono_set inter_subset_left

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Small sets and aperiodicity of the forward recurrence time `δ`-skeleton (MT §§5.3.4, 5.4.4)

Meyn and Tweedie, Proposition 5.3.3 (p. 109) and Proposition 5.4.7 (p. 115), for the forward
recurrence time `δ`-skeleton `V⁺_δ` with kernel `fwdSkelKernel Γ δ` (copied from the
`TransitionProbabilities` project, `RenewalSkeletons`). The increment law `Γ` lives on `[0, ∞)`
and is not concentrated at `0`, so that `V⁺_δ` is a Markov chain (`fwdSkeleton_isMarkovChain`).

* `fwdSkelKernel_pow_apply`: `Pᴹ(x, B) = Γ^{⊗ℕ}{V⁺(Mδ) ∈ B}` for the renewal process with
  first epoch `x > 0`.
* `fwdTimeCts_eq_of_window`: if the epoch `Z_{n+1} = x + S_n + y` lies in `(t, t + δ)` and
  `y ≥ δ`, then `V⁺(t) = Z_{n+1} − t` (the argument of (5.33)).
* `exists_convPow_minorant`: a spread-out `Γ` has `Γ^{N∗} ≥ β μ_Leb|_{[a, b]}` with `0 ≤ a < b`
  (from Proposition 5.3.1, as in (5.28)).
* `fwdSkel_pow_ge`: the bound (5.35), `Pᴹ(x, B) ≥ β γ μ_Leb(B)` for `x, B ⊆ (0, δ)` and
  `M ∈ {k + m + 2, k + m + 3}`.
* **Proposition 5.3.3** (`proposition_5_3_3`, p. 109): if `Γ` is spread out, then for every small
  enough `δ > 0` the set `(0, δ)` is small for `V⁺_δ`, with a multiple of Lebesgue measure on
  `(0, δ)` as minorizing measure, at the two consecutive times `M` and `M + 1`.
* **Proposition 5.4.7** (`proposition_5_4_7`, p. 115): for such `δ`, `g.c.d. E_C = 1` for
  `C = (0, δ)`, so `V⁺_δ` is aperiodic for every maximal irreducibility measure `ψ` with
  `ψ(C) > 0`.

**Corrections and hypotheses.** The book uses the set `[0, δ)`. In this construction
`V⁺(t) > 0` always (the first epoch strictly after `t`), so the small set is `(0, δ)`. The book
leaves the irreducibility of `V⁺_δ` implicit in "aperiodic". Here the conclusion is the g.c.d.
statement (5.40), which is how the book proves it, and aperiodicity for every maximal
irreducibility measure that charges `(0, δ)`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- The forward skeleton kernel is a transition kernel. -/
theorem isMarkovKernel_fwdSkelKernel (δ : ℝ) : IsMarkovKernel (fwdSkelKernel Γ δ) :=
  isMarkovKernel_recursionKernel _ (measurable_fwdSkelStep δ)

/-- `Pᴹ(x, B) = Γ^{⊗ℕ}{w : V⁺(Mδ) ∈ B}` for the renewal process with first epoch `x > 0` and
increments `w`. -/
theorem fwdSkelKernel_pow_apply (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ}
    (hδ : 0 ≤ δ) {x : ℝ} (hx : 0 < x) (M : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    (fwdSkelKernel Γ δ ^ M) x B =
      (Measure.infinitePi fun _ : ℕ => Γ) {w | fwdTimeCts (resEpoch x w) (M * δ) ∈ B} := by
  have := isMarkovKernel_fwdSkelKernel Γ δ
  have h := fwdSkeleton_isMarkovChain_delayed Γ hΓ0 hΓpos (Measure.dirac x)
    (by simp [hx.not_ge]) hδ
  have hmap := congrArg (fun μ : Measure ℝ => μ B) (h.map_eq M)
  rw [Measure.map_apply (measurable_fwdSkel δ M) hB, Measure.dirac_bind (Kernel.measurable _),
    Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
      ((measurable_fwdSkel δ M) hB)] at hmap
  rw [← hmap]
  rfl

/-- **The window argument of (5.33).** With nonnegative increments, if `y = wₙ ≥ δ` and the epoch
`Z_{n+2} = x + w₀ + ⋯ + wₙ` lies in `(t, t + δ)`, then `V⁺(t) = Z_{n+2} − t`. -/
theorem fwdTimeCts_eq_of_window {x t δ : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (n : ℕ)
    (hy : δ ≤ w n) (h1 : t < resEpoch x w (n + 2)) (h2 : resEpoch x w (n + 2) < t + δ) :
    fwdTimeCts (resEpoch x w) t = resEpoch x w (n + 2) - t := by
  have hprev : resEpoch x w (n + 1) ≤ t := by
    have : resEpoch x w (n + 2) = resEpoch x w (n + 1) + w n := by
      simp only [resEpoch_succ_eq, Finset.sum_range_succ]
      ring
    linarith
  refine IsLeast.csInf_eq ⟨⟨n + 2, by omega, h1, rfl⟩, ?_⟩
  rintro d ⟨j, hj, htj, rfl⟩
  have hj2 : n + 2 ≤ j := by
    by_contra hlt
    have := resEpoch_mono (x := x) hw hj (show j ≤ n + 1 by omega)
    linarith
  have := resEpoch_mono (x := x) hw (show 1 ≤ n + 2 by omega) hj2
  linarith

/-- A spread-out increment law on `[0, ∞)` has `Γ^{N∗} ≥ β μ_Leb|_{[a, b]}` for some `N`,
`0 ≤ a < b` and `β > 0` (from Proposition 5.3.1, as in (5.28)). -/
theorem exists_convPow_minorant (hΓ0 : Γ (Iio 0) = 0) (h : IsSpreadOut Γ) :
    ∃ N : ℕ, ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ ∃ β : ℝ≥0∞, 0 < β ∧
      ∀ B, MeasurableSet B → β * volume (B ∩ Icc a b) ≤ convPow Γ N B := by
  obtain ⟨n, -, r, hr, s, t, hst, ε, hε, hsmall⟩ := proposition_5_3_1 Γ h
  have hle : ∀ B, MeasurableSet B → ε * volume (B ∩ Icc s t) ≤ convPow Γ (2 * n) B :=
    fun B hB => by
      have := hsmall.le_apply (x := 0) ⟨by linarith, by linarith⟩ B
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
        randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add 0) hB] at this
      have hpre : (fun w : ℝ => 0 + w) ⁻¹' B = B := by ext w; simp
      rwa [hpre] at this
  have ht : 0 < t := by
    by_contra hneg
    push Not at hneg
    have h1 := hle (Iio 0) measurableSet_Iio
    rw [convPow_Iio_zero Γ hΓ0] at h1
    have h2 : volume (Ico s t) ≤ volume (Iio (0 : ℝ) ∩ Icc s t) :=
      measure_mono fun u hu => ⟨lt_of_lt_of_le hu.2 hneg, hu.1, hu.2.le⟩
    rw [Real.volume_Ico] at h2
    have h3 : 0 < ENNReal.ofReal (t - s) := ENNReal.ofReal_pos.2 (by linarith)
    exact absurd (nonpos_iff_eq_zero.1 h1) (mul_ne_zero hε.ne' (h3.trans_le h2).ne')
  refine ⟨2 * n, max s 0, t, le_max_right _ _, max_lt hst ht, ε, hε, fun B hB => ?_⟩
  refine le_trans ?_ (hle B hB)
  gcongr
  exact le_max_left s 0

/-- **The bound (5.35)** (MT p. 109). Suppose `Γ^{N∗} ≥ β μ_Leb|_{[a, b]}`,
`[kδ, (k + 4)δ] ⊆ [a, b]`, `m ≥ 1` and `k + m + 2 ≤ M ≤ k + m + 3`. Then
`Pᴹ(x, B) ≥ β Γ[mδ, (m + 1)δ) μ_Leb(B)` for `x ∈ (0, δ)` and `B ⊆ (0, δ)`. -/
theorem fwdSkel_pow_ge (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {N : ℕ} {a b : ℝ}
    {β : ℝ≥0∞} (hmin : ∀ B, MeasurableSet B → β * volume (B ∩ Icc a b) ≤ convPow Γ N B)
    {δ : ℝ} (hδ : 0 < δ) {k m : ℕ} (hm : 1 ≤ m) (hka : a ≤ k * δ) (hkb : (k + 4) * δ ≤ b)
    {M : ℕ} (hM1 : k + m + 2 ≤ M) (hM2 : M ≤ k + m + 3) {x : ℝ} (hx : x ∈ Ioo 0 δ)
    {B : Set ℝ} (hB : MeasurableSet B) (hBδ : B ⊆ Ioo 0 δ) :
    β * Γ (Ico (m * δ) ((m + 1) * δ)) * volume B ≤ (fwdSkelKernel Γ δ ^ M) x B := by
  rw [fwdSkelKernel_pow_apply Γ hΓ0 hΓpos hδ.le hx.1 M hB]
  have : IsFiniteMeasure (convPow Γ N) := by unfold convPow; infer_instance
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  set R : Set (ℝ × ℝ) := {q | δ ≤ q.2 ∧ x + q.1 + q.2 - M * δ ∈ B} with hRdef
  have hRm : MeasurableSet R :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hB)
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range N, w i, w N) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply N)
  have hMr1 : ((k : ℝ) + m + 2) ≤ M := by exact_mod_cast hM1
  have hMr2 : (M : ℝ) ≤ (k : ℝ) + m + 3 := by exact_mod_cast hM2
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- (5.33): the event `{(S_N, w_N) ∈ R}` forces `V⁺(Mδ) ∈ B`
  have hsub : ν ((fun w : ℕ → ℝ => (∑ i ∈ Finset.range N, w i, w N)) ⁻¹' R) ≤
      ν {w | fwdTimeCts (resEpoch x w) (M * δ) ∈ B} := by
    refine measure_mono_ae ?_
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨_, hw⟩ hwR
    obtain ⟨hy, hb⟩ := hwR
    have hZ : resEpoch x w (N + 2) = x + ∑ i ∈ Finset.range N, w i + w N := by
      rw [resEpoch_succ_eq, Finset.sum_range_succ, add_assoc]
    have hb' := hBδ hb
    have h1 : (M : ℝ) * δ < resEpoch x w (N + 2) := by rw [hZ]; linarith [hb'.1]
    have h2 : resEpoch x w (N + 2) < M * δ + δ := by rw [hZ]; linarith [hb'.2]
    change fwdTimeCts (resEpoch x w) (M * δ) ∈ B
    rw [fwdTimeCts_eq_of_window hw N hy h1 h2, hZ]
    exact hb
  refine le_trans ?_ hsub
  rw [← Measure.map_apply hpair hRm, infinitePi_map_partialSum_next Γ N,
    Measure.prod_apply_symm hRm]
  calc β * Γ (Ico (m * δ) ((m + 1) * δ)) * volume B
      = ∫⁻ _ in Ico (m * δ) ((m + 1) * δ), β * volume B ∂Γ := by
        rw [setLIntegral_const]; ring
    _ ≤ ∫⁻ y in Ico (m * δ) ((m + 1) * δ), convPow Γ N ((fun s => (s, y)) ⁻¹' R) ∂Γ := by
        refine setLIntegral_mono' measurableSet_Ico fun y hy => ?_
        have hsec : (fun s => (s, y)) ⁻¹' R = (· + (x + y - M * δ)) ⁻¹' B := by
          ext s
          simp only [hRdef, mem_preimage, mem_ofPred_eq]
          constructor
          · rintro ⟨-, h⟩; convert h using 1; ring
          · intro h
            refine ⟨?_, by convert h using 1; ring⟩
            nlinarith [hy.1]
        have hwin : (· + (x + y - M * δ)) ⁻¹' B ⊆ Icc a b := fun s hs => by
          have := hBδ hs
          simp only [mem_Ioo] at this
          constructor
          · nlinarith [hx.2, hy.2]
          · nlinarith [hx.1, hy.1]
        have hpre : MeasurableSet ((· + (x + y - M * δ)) ⁻¹' B) :=
          (measurable_add_const _) hB
        rw [hsec]
        calc β * volume B = β * volume ((· + (x + y - M * δ)) ⁻¹' B ∩ Icc a b) := by
              rw [inter_eq_left.2 hwin, measure_preimage_add_right]
          _ ≤ _ := hmin _ hpre
    _ ≤ ∫⁻ y, convPow Γ N ((fun s => (s, y)) ⁻¹' R) ∂Γ := setLIntegral_le_lintegral _ _

/-- **Proposition 5.3.3** (MT p. 109). If `Γ` is spread out, then for every small enough
`δ > 0` the set `C = (0, δ)` is small for the forward recurrence time `δ`-skeleton, with
minorizing measure `c μ_Leb|_C`, at two consecutive times `M` and `M + 1`. -/
theorem proposition_5_3_3 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (h : IsSpreadOut Γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ M : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧
      IsSmallSet (fwdSkelKernel Γ δ) M (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) ∧
      IsSmallSet (fwdSkelKernel Γ δ) (M + 1) (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) := by
  obtain ⟨N, a, b, ha0, hab, β, hβ, hmin⟩ := exists_convPow_minorant Γ hΓ0 h
  -- a level `δ₁ > 0` with `Γ[δ₁, ∞) > 0`
  obtain ⟨j₁, hj₁⟩ : ∃ j : ℕ, 0 < Γ (Ici ((j : ℝ) + 1)⁻¹) := by
    refine exists_measure_pos_of_iUnion (hΓpos.trans_le (measure_mono fun y hy => ?_))
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (mem_Ioi.1 hy)
    exact mem_iUnion.2 ⟨j, mem_Ici.2 (by rw [← one_div]; exact hj.le)⟩
  set δ₁ : ℝ := ((j₁ : ℝ) + 1)⁻¹
  have hδ₁ : 0 < δ₁ := by positivity
  refine ⟨min ((b - a) / 5) δ₁, lt_min (by linarith) hδ₁, fun δ hδ hδ₀ => ?_⟩
  have hδa : δ ≤ (b - a) / 5 := hδ₀.trans (min_le_left _ _)
  have hδb : δ ≤ δ₁ := hδ₀.trans (min_le_right _ _)
  -- the window `[kδ, (k + 4)δ] ⊆ [a, b]`
  set k := ⌈a / δ⌉₊
  have hka : a ≤ k * δ := (div_le_iff₀ hδ).1 (Nat.le_ceil _)
  have hkb : (k + 4) * δ ≤ b := by
    have := Nat.ceil_lt_add_one (div_nonneg ha0 hδ.le)
    have h2 : (k : ℝ) * δ < a + δ := by
      have := (lt_div_iff₀ hδ).1 (show (k : ℝ) - 1 < a / δ by linarith)
      linarith
    linarith
  -- a cell `[mδ, (m + 1)δ)`, `m ≥ 1`, charged by `Γ`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 0 < Γ (Ico (((j : ℝ) + 1) * δ) (((j : ℝ) + 2) * δ)) := by
    refine exists_measure_pos_of_iUnion (hj₁.trans_le (measure_mono fun y hy => ?_))
    have hy' : δ ≤ y := hδb.trans (mem_Ici.1 hy)
    set f := ⌊y / δ⌋₊
    have hf1 : 1 ≤ f := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ]; linarith)
    have hf2 : (f : ℝ) * δ ≤ y :=
      (le_div_iff₀ hδ).1 (Nat.floor_le (div_nonneg (hδ.le.trans hy') hδ.le))
    have hf3 : y < ((f : ℝ) + 1) * δ := (div_lt_iff₀ hδ).1 (Nat.lt_floor_add_one _)
    refine mem_iUnion.2 ⟨f - 1, ?_, ?_⟩
    · rw [Nat.cast_sub hf1, Nat.cast_one]; linarith
    · rw [Nat.cast_sub hf1, Nat.cast_one]; linarith
  set m := j + 1
  have hm : 1 ≤ m := by omega
  have hγ : Γ (Ico (m * δ) ((m + 1) * δ)) = Γ (Ico (((j : ℝ) + 1) * δ) (((j : ℝ) + 2) * δ)) := by
    congr 2 <;> push_cast [m] <;> ring
  have hc : 0 < β * Γ (Ico (m * δ) ((m + 1) * δ)) :=
    ENNReal.mul_pos hβ.ne' (by rw [hγ]; exact hj.ne')
  have hsmall : ∀ M, k + m + 2 ≤ M → M ≤ k + m + 3 →
      IsSmallSet (fwdSkelKernel Γ δ) M
        ((β * Γ (Ico (m * δ) ((m + 1) * δ))) • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) :=
    fun M hM1 hM2 => by
      refine ⟨measurableSet_Ioo, by omega, smul_measure_ne_zero ?_ hc.ne', fun x hx => ?_⟩
      · rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
        linarith
      refine Measure.le_intro fun B hB _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
      exact (fwdSkel_pow_ge Γ hΓ0 hΓpos hmin hδ hm hka hkb hM1 hM2 hx
        (hB.inter measurableSet_Ioo) inter_subset_right).trans (measure_mono inter_subset_left)
  exact ⟨k + m + 2, _, hc, hsmall _ le_rfl (by omega), hsmall _ (by omega) le_rfl⟩

/-- **Proposition 5.4.7** (MT p. 115). If `Γ` is spread out, then for every small enough `δ > 0`
the forward recurrence time `δ`-skeleton has a small set `C = (0, δ)` with `ν(C) > 0` and
`g.c.d. E_C = 1`. Hence it is aperiodic for every maximal irreducibility measure `ψ` with
`ψ(C) > 0`. -/
theorem proposition_5_4_7 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (h : IsSpreadOut Γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ M : ℕ, ∃ ν : Measure ℝ,
      IsSmallSet (fwdSkelKernel Γ δ) M ν (Ioo 0 δ) ∧ 0 < ν (Ioo 0 δ) ∧
      setGcd (smallTimes (fwdSkelKernel Γ δ) (Ioo 0 δ) ν) = 1 ∧
      ∀ ψ : Measure ℝ, (haveI := isMarkovKernel_fwdSkelKernel Γ δ
        IsMaximalIrreducibility (fwdSkelKernel Γ δ) ψ) → 0 < ψ (Ioo 0 δ) →
        IsAperiodic (fwdSkelKernel Γ δ) ψ := by
  obtain ⟨δ₀, hδ₀, hall⟩ := proposition_5_3_3 Γ hΓ0 hΓpos h
  refine ⟨δ₀, hδ₀, fun δ hδ hle => ?_⟩
  have := isMarkovKernel_fwdSkelKernel Γ δ
  obtain ⟨M, c, hc, h1, h2⟩ := hall δ hδ hle
  have hνC : 0 < (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) := by
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo, inter_self,
      Real.volume_Ioo, smul_eq_mul]
    exact ENNReal.mul_pos hc.ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hS := smallTimes_isAddClosed (fwdSkelKernel Γ δ) hνC
  have hM := mem_smallTimes_of_isSmallSet h1
  have hM1 := mem_smallTimes_of_isSmallSet h2
  have hg : setGcd (smallTimes (fwdSkelKernel Γ δ) (Ioo 0 δ) (c • volume.restrict (Ioo 0 δ))) =
      1 := Nat.dvd_one.1 ((Nat.dvd_add_right (setGcd_dvd hS hM h1.2.1 hM)).1
        (setGcd_dvd hS hM h1.2.1 hM1))
  refine ⟨M, _, h1, hνC, hg, fun ψ hψ hψC => ?_⟩
  have := isPeriod_gcd (fwdSkelKernel Γ δ) hψ h1 hψC hνC
  rwa [hg] at this

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Petite sets for the split chain (MT Proposition 5.5.6 (ii))

Meyn and Tweedie, Proposition 5.5.6 (ii), p. 120: if `Φ` is strongly aperiodic and split on the
small set `A`, then `C₀ ∪ C₁` is petite for the split chain whenever `C` is petite for `Φ`.

* `split_comp_sampledKernel`: (5.10) for sampled chains, `μ* Ǩ_a = (μ K_a)*`.
* `split_dirac_of_notMem`, `sampledKernel_split_false_of_notMem`: off `C` the split of `δₓ` is
  `δ_{x₀}`, so `Ǩ_a(x₀, ·) = K_a(x, ·)*`.
* `proposition_5_5_6_ii_average`: for `x ∈ C`, the split initial law `δₓ*` satisfies
  `δₓ* Ǩ_a ≥ ν_a*`: `C` is petite "on average over the coin".
* `proposition_5_5_6_ii`, the corrected statement: on a countably generated space and for a
  `ψ`-irreducible chain, `(C \ A)₀ ∪ X₁` is petite for the split chain for every minorization
  on `A` and every petite `C`.
* `proposition_5_5_6_ii_counterexample`: the claim as stated is false. For the ladder chain
  `ladderKernel` on `ℕ` (even states `2i` jump to `0` or to `2i + 1` with probability `½` each,
  odd states descend `2k + 3 ↦ 2k + 1 ↦ ⋯ ↦ 1 ↦ 0`), the set `A` of even states is `½δ₀`-small,
  the chain is strongly aperiodic, and `A₀` (hence `A₀ ∪ A₁`) is not petite for the split chain:
  the residual law from `(2i, 0)` is `δ_{2i+1}`, and the split chain then needs `i + 1` steps to
  return to the region where the paths from different `i` meet.

**Corrections.** Proposition 5.5.6 (ii) is false as stated (`proposition_5_5_6_ii_counterexample`).
The book's step "`A₀` is small since `P̌(x₀, X₁) ≥ δ` for `x₀ ∈ A₀`" fails: `P̌(x₀, X₁) =
δ R(x, A)` with `R` the residual kernel (5.6), which can vanish. The averaged and the corrected
statements above hold.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace Minorization

variable {P : Kernel X X}

/-- (5.10) for sampled chains: `μ* Ǩ_a = (μ K_a)*`. -/
theorem split_comp_sampledKernel (M : Minorization P) (a : ℕ → ℝ≥0∞) (μ : Measure X) :
    sampledKernel M.splitKernel a ∘ₘ M.split μ = M.split (sampledKernel P a ∘ₘ μ) := by
  ext s hs
  have hg : Measurable fun y => M.splitK y s := Kernel.measurable_coe _ hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [sampledKernel_apply _ a _ hs]
  rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hs).const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ (Kernel.measurable_coe _ hs)]
  have h1 : ∀ n, ∫⁻ z, (M.splitKernel ^ n) z s ∂M.split μ =
      M.split ((P ^ n : Kernel X X) ∘ₘ μ) s := fun n => by
    rw [← split_comp_splitKernel_pow, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [h1]
  rw [split, Measure.bind_apply hs M.splitK.aemeasurable,
    Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  change _ = ∫⁻ x, ∫⁻ y, M.splitK y s ∂(Measure.sum fun n => a n • (P ^ n) x) ∂μ
  simp_rw [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_tsum fun n => (hg.lintegral_kernel.const_mul _).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ hg.lintegral_kernel, split,
    Measure.bind_apply hs M.splitK.aemeasurable,
    Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

/-- Off `C`, the split of `δₓ` is `δ_{x₀}`. -/
theorem split_dirac_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) :
    M.split (Measure.dirac x) = Measure.dirac (x, false) := by
  rw [split, Measure.dirac_bind M.splitK.measurable, splitK_apply, splitMeas,
    M.splitProb_of_notMem hx]
  simp

/-- Off `C`, `Ǩ_a(x₀, ·) = K_a(x, ·)*`. -/
theorem sampledKernel_split_false_of_notMem (M : Minorization P) (a : ℕ → ℝ≥0∞) {x : X}
    (hx : x ∉ M.C) :
    sampledKernel M.splitKernel a (x, false) = M.split (sampledKernel P a x) := by
  have h := M.split_comp_sampledKernel a (Measure.dirac x)
  rwa [M.split_dirac_of_notMem hx, Measure.dirac_bind (Kernel.measurable _),
    Measure.dirac_bind (Kernel.measurable _)] at h

/-- `μ*` is nonzero when `μ` is. -/
theorem split_ne_zero (M : Minorization P) {μ : Measure X} (hμ : μ ≠ 0) : M.split μ ≠ 0 := by
  intro h
  apply hμ
  rw [← Measure.measure_univ_eq_zero, ← M.split_univ, h]
  rfl

/-- Proposition 5.5.6 (ii), averaged form: if `C` is `ν_a`-petite for `Φ`, then for every
`x ∈ C` the split initial law satisfies `δₓ* Ǩ_a ≥ ν_a*`. -/
theorem proposition_5_5_6_ii_average (M : Minorization P) {a : ℕ → ℝ≥0∞} {ν : Measure X}
    {C : Set X} (hC : IsPetiteSet P a ν C) {x : X} (hx : x ∈ C) :
    M.split ν ≤ sampledKernel M.splitKernel a ∘ₘ M.split (Measure.dirac x) := by
  rw [M.split_comp_sampledKernel, Measure.dirac_bind (Kernel.measurable _)]
  exact comp_le_comp _ (hC.2.2.2 x hx)

/-- **Proposition 5.5.6 (ii)**, corrected (MT p. 120). On a countably generated space, let `Φ` be
`ψ`-irreducible, `M` a minorization on a set `A` and `C` a petite set. Then `(C \ A)₀ ∪ X₁` is
petite for the split chain. -/
theorem proposition_5_5_6_ii [MeasurableSpace.CountablyGenerated X] (M : Minorization P)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {C : Set X}
    (hC : IsPetite P C) :
    haveI := M.isMarkovKernel_splitKernel
    IsPetite M.splitKernel ((C \ M.C) ×ˢ {false} ∪ univ ×ˢ {true}) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_ν
  obtain ⟨a, ν, hpet⟩ := hC
  have hψ' := M.isMaximalIrreducibility_split hψ
  -- the top level outside `A`
  have h0 : IsPetite M.splitKernel ((C \ M.C) ×ˢ {false}) := by
    refine ⟨a, M.split ν, (hpet.1.diff M.measurableSet_C).prod (measurableSet_singleton _),
      hpet.2.1, M.split_ne_zero hpet.2.2.1, fun z hz => ?_⟩
    obtain ⟨x, b⟩ := z
    obtain ⟨⟨hxC, hxA⟩, hb⟩ := hz
    have hb' : b = false := hb
    subst hb'
    rw [M.sampledKernel_split_false_of_notMem a hxA]
    exact comp_le_comp _ (hpet.2.2.2 x hxC)
  -- the bottom level is an atom
  have h1 : IsPetite M.splitKernel (univ ×ˢ ({true} : Set Bool)) := by
    obtain ⟨hm, -, hν⟩ := M.isAtom_bottom
    exact ⟨_, _, proposition_5_5_3 (isSmallSet_of_atom M.splitKernel
      (MeasurableSet.univ.prod (measurableSet_singleton true)) (fun z hz => by
        obtain ⟨x, b⟩ := z
        obtain ⟨-, hb⟩ := hz
        have hb' : b = true := hb
        subst hb'
        rw [splitKernel_apply_true]) (M.split_ne_zero
          (IsProbabilityMeasure.ne_zero M.ν)))⟩
  exact proposition_5_5_5_ii M.splitKernel hψ' h0 h1

end Minorization

/-! ### The counterexample -/

/-- The transition law of the ladder chain on `ℕ`: from an even state `n = 2i`, jump to `0` or to
`2i + 1` with probability `½` each; from an odd state `n`, move to `n − 2` (and from `1` to
`0`). -/
noncomputable def ladderMeas (n : ℕ) : Measure ℕ :=
  if Even n then (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (n + 1)
  else Measure.dirac (n - 2)

/-- The ladder chain. -/
noncomputable def ladderKernel : Kernel ℕ ℕ := ⟨ladderMeas, measurable_of_countable _⟩

/-- The ladder chain is a transition kernel. -/
theorem isMarkovKernel_ladderKernel : IsMarkovKernel ladderKernel := by
  refine ⟨fun n => ⟨?_⟩⟩
  change ladderMeas n univ = 1
  unfold ladderMeas
  split_ifs
  · simp [ENNReal.inv_two_add_inv_two]
  · simp

/-- The minorization `P(x, ·) ≥ ½ δ₀` on the even states. -/
noncomputable def ladderMinorization : Minorization ladderKernel where
  C := {n | Even n}
  δ := 2⁻¹
  ν := Measure.dirac 0
  measurableSet_C := measurableSet_of_countable _
  δ_pos := by simp
  δ_lt_one := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  isProbabilityMeasure_ν := inferInstance
  le x hx := by
    change _ ≤ ladderMeas x
    have hx' : Even x := hx
    simp only [ladderMeas, hx', ite_true]
    exact Measure.le_add_right le_rfl

/-- The ladder chain is strongly aperiodic: the even states are `½δ₀`-small. -/
theorem ladder_isStronglyAperiodic : IsStronglyAperiodic ladderKernel :=
  ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac 0, {n | Even n}, ⟨measurableSet_of_countable _, one_pos,
    smul_measure_ne_zero (by simp) (by simp), fun x hx => by
      rw [pow_one]; exact ladderMinorization.le x hx⟩, by simp⟩

/-- The residual law of the ladder chain at an even state `x` is `δ_{x+1}`. -/
theorem ladder_resid_even {x : ℕ} (hx : Even x) :
    ladderMinorization.resid x = Measure.dirac (x + 1) := by
  ext s hs
  rw [Minorization.resid_apply, Minorization.residMeas_apply_of_mem _ hx hs]
  change (1 - 2⁻¹)⁻¹ * (ladderMeas x s - 2⁻¹ * Measure.dirac 0 s) = _
  simp only [ladderMeas, hx, ite_true]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, ENNReal.add_sub_cancel_left (ENNReal.mul_ne_top (by simp)
      (measure_ne_top _ _)), ENNReal.one_sub_inv_two, inv_inv, ← mul_assoc,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- The split of `δ_y` at an odd state `y` is `δ_{(y, 0)}`. -/
theorem ladder_split_dirac_odd {y : ℕ} (hy : ¬ Even y) :
    ladderMinorization.split (Measure.dirac y) = Measure.dirac (y, false) :=
  ladderMinorization.split_dirac_of_notMem hy

/-- From `(2i, 0)` the split chain moves to `(2i + 1, 0)`. -/
theorem ladder_splitKernel_even (i : ℕ) :
    ladderMinorization.splitKernel (2 * i, false) = Measure.dirac (2 * i + 1, false) := by
  rw [Minorization.splitKernel_apply, Minorization.baseK_apply_false,
    ladder_resid_even (even_two_mul i), ladder_split_dirac_odd (by simp)]

/-- From `(2k + 3, 0)` the split chain moves to `(2k + 1, 0)`. -/
theorem ladder_splitKernel_odd (k : ℕ) :
    ladderMinorization.splitKernel (2 * k + 3, false) = Measure.dirac (2 * k + 1, false) := by
  have hodd : ¬ Even (2 * k + 3) := by
    rw [Nat.not_even_iff_odd]; exact ⟨k + 1, by ring⟩
  rw [ladderMinorization.splitKernel_apply_false_of_notMem hodd]
  change ladderMinorization.split (ladderMeas (2 * k + 3)) = _
  simp only [ladderMeas, hodd, ite_false]
  rw [show 2 * k + 3 - 2 = 2 * k + 1 by omega,
    ladder_split_dirac_odd (by rw [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩)]

/-- From `(2i, 0)`, after `n + 1 ≤ i + 1` steps the split chain is at `(2(i − n) + 1, 0)`. -/
theorem ladder_splitKernel_pow (i n : ℕ) (hn : n ≤ i) :
    (ladderMinorization.splitKernel ^ (n + 1)) (2 * i, false) =
      Measure.dirac (2 * (i - n) + 1, false) := by
  induction n with
  | zero => rw [zero_add, pow_one, ladder_splitKernel_even, Nat.sub_zero]
  | succ n ih =>
    rw [pow_succ']
    change (ladderMinorization.splitKernel ∘ₖ (ladderMinorization.splitKernel ^ (n + 1)))
      (2 * i, false) = _
    rw [Kernel.comp_apply, ih (by omega), Measure.dirac_bind (Kernel.measurable _),
      show 2 * (i - n) + 1 = 2 * (i - (n + 1)) + 3 by omega, ladder_splitKernel_odd]

/-- **Correction to Proposition 5.5.6 (ii)** (MT p. 120). For the strongly aperiodic ladder chain
split on the `½δ₀`-small set `A` of even states, `A` is petite for `Φ` but `A₀ ∪ A₁` is not
petite for the split chain. -/
theorem proposition_5_5_6_ii_counterexample :
    haveI := isMarkovKernel_ladderKernel
    IsPetite ladderKernel {n | Even n} ∧
      ¬ IsPetite ladderMinorization.splitKernel ({n | Even n} ×ˢ univ) := by
  have := isMarkovKernel_ladderKernel
  refine ⟨⟨_, _, proposition_5_5_3 (m := 1) (ν := (2⁻¹ : ℝ≥0∞) • Measure.dirac 0)
    ⟨measurableSet_of_countable _, one_pos, smul_measure_ne_zero (by simp) (by simp),
      fun x hx => by rw [pow_one]; exact ladderMinorization.le x hx⟩⟩, ?_⟩
  set Q := ladderMinorization.splitKernel with hQ
  have hM : IsMarkovKernel Q := ladderMinorization.isMarkovKernel_splitKernel
  rintro ⟨a, ν', -, ha, hν, hle⟩
  -- a point charged by the minorizing measure
  have hpos : 0 < ν' univ := pos_iff_ne_zero.2 fun h => hν (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨w, -, hw⟩ := exists_singleton_pos_of_pos ν' hpos
  have hK := isMarkovKernel_sampledKernel Q ha
  have hct : ν' {w} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((hle (0, false) ⟨Even.zero, mem_univ _⟩ {w}).trans prob_le_one)
  have hc2 : 0 < ν' {w} / 2 := ENNReal.div_pos hw.ne' (by simp)
  obtain ⟨T, hT⟩ := exists_tail_le ha hc2
  -- the state `(2i, 0)`, `i = T + w₁`, has not reached `w` before time `T`
  set i := T + w.1 with hi
  have h1 := hle (2 * i, false) ⟨even_two_mul i, mem_univ _⟩ {w}
  rw [sampledKernel_apply _ a _ (measurableSet_singleton w)] at h1
  have hsplit : ∑' n, a n * (Q ^ n) (2 * i, false) {w} =
      ∑ n ∈ Finset.range T, a n * (Q ^ n) (2 * i, false) {w} +
        ∑' k, a (k + T) * (Q ^ (k + T)) (2 * i, false) {w} :=
    (Summable.sum_add_tsum_nat_add' (f := fun n => a n * (Q ^ n) (2 * i, false) {w}) (k := T)
      ENNReal.summable).symm
  have hhead : ∑ n ∈ Finset.range T, a n * (Q ^ n) (2 * i, false) {w} = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_range] at hn
    rcases n with _ | m
    · rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton w),
        indicator_of_notMem, mul_zero]
      intro h
      have := congrArg Prod.fst (mem_singleton_iff.1 h)
      simp only at this
      omega
    · rw [hQ, ladder_splitKernel_pow i m (by omega),
        Measure.dirac_apply' _ (measurableSet_singleton w), indicator_of_notMem, mul_zero]
      intro h
      have := congrArg Prod.fst (mem_singleton_iff.1 h)
      simp only at this
      omega
  have htail : ∑' k, a (k + T) * (Q ^ (k + T)) (2 * i, false) {w} ≤ ν' {w} / 2 := by
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) hT
    have := isMarkovKernel_pow Q (k + T)
    exact mul_le_of_le_one_right' prob_le_one
  rw [hsplit, hhead, zero_add] at h1
  exact absurd (h1.trans htail) (not_le.2 (ENNReal.half_lt_self hw.ne' hct))

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The counterexample to Proposition 5.5.6 (ii) is ψ-irreducible

Meyn and Tweedie, Proposition 5.5.6 (ii), p. 120, assumes that `Φ` is `ψ`-irreducible. This module
shows that the ladder chain `ladderKernel` of `SplitPetite` satisfies that hypothesis, so the
counterexample `proposition_5_5_6_ii_counterexample` applies to the proposition as stated.

* `ladder_pow_odd`: the odd states descend, `Pᵏ(2j + 1, ·) = δ_{2j+1−2k}` for `k ≤ j + 1`, and
  `ladder_reaches_zero`: every state reaches `0`.
* `ladder_isPhiIrreducible_dirac`: the ladder chain is `δ₀`-irreducible.
* `ladder_isAbsorbing_zero_one`: `{0, 1}` is absorbing.
* `ladder_isMaximalIrreducibility`: `δ₀ + δ₁` is a maximal irreducibility measure.
* `proposition_5_5_6_ii_counterexample_irreducible`, the strengthened counterexample: the ladder
  chain has a maximal irreducibility measure `ψ`, is strongly aperiodic, and the set `A` of even
  states is `½δ₀`-small with `ψ(A) > 0`. Yet `A × Bool` is not petite for the chain split on `A`.

**Corrections.** None beyond those of `SplitPetite`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- An odd state moves to `n − 2`. -/
theorem ladderKernel_odd {n : ℕ} (hn : ¬ Even n) : ladderKernel n = Measure.dirac (n - 2) := by
  change ladderMeas n = _
  simp only [ladderMeas, hn, ite_false]

/-- An even state moves to `0` with probability at least `½`. -/
theorem ladderKernel_even_zero {n : ℕ} (hn : Even n) : 2⁻¹ ≤ ladderKernel n {0} := by
  change 2⁻¹ ≤ ladderMeas n {0}
  simp only [ladderMeas, hn, ite_true, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp

/-- The odd states descend: `Pᵏ(2j + 1, ·) = δ_{2j+1−2k}` for `k ≤ j + 1`. -/
theorem ladder_pow_odd (j : ℕ) {k : ℕ} (hk : k ≤ j + 1) :
    (ladderKernel ^ k) (2 * j + 1) = Measure.dirac (2 * j + 1 - 2 * k) := by
  induction k with
  | zero => rw [pow_zero_apply, Nat.mul_zero, Nat.sub_zero]
  | succ k ih =>
    rw [pow_succ']
    change (ladderKernel ∘ₖ (ladderKernel ^ k)) (2 * j + 1) = _
    rw [Kernel.comp_apply, ih (by omega), Measure.dirac_bind (Kernel.measurable _),
      ladderKernel_odd (by rw [Nat.not_even_iff_odd]; exact ⟨j - k, by omega⟩)]
    congr 1

/-- Every state reaches `0`: `Pᵏ⁺¹(n, {0}) > 0` for some `k`. -/
theorem ladder_reaches_zero (n : ℕ) : ∃ k, 0 < (ladderKernel ^ (k + 1)) n {0} := by
  rcases Nat.even_or_odd n with hn | ⟨j, rfl⟩
  · refine ⟨0, ?_⟩
    rw [zero_add, pow_one]
    exact (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top).trans_le (ladderKernel_even_zero hn)
  · refine ⟨j, ?_⟩
    rw [ladder_pow_odd j le_rfl, show 2 * j + 1 - 2 * (j + 1) = 0 by omega]
    simp

/-- The ladder chain is `δ₀`-irreducible. -/
theorem ladder_isPhiIrreducible_dirac :
    haveI := isMarkovKernel_ladderKernel
    IsPhiIrreducible ladderKernel (Measure.dirac 0) := by
  have := isMarkovKernel_ladderKernel
  rw [isPhiIrreducible_dirac_iff]
  exact fun n => (hitProb_pos_iff _ (measurableSet_singleton 0) n).2 (ladder_reaches_zero n)

/-- `{0, 1}` is absorbing for the ladder chain. -/
theorem ladder_isAbsorbing_zero_one : IsAbsorbing ladderKernel {0, 1} := by
  have := isMarkovKernel_ladderKernel
  intro x hx
  rcases hx with rfl | hx
  · change ladderMeas 0 {0, 1} = 1
    simp only [ladderMeas, Even.zero, ite_true, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul]
    simp [ENNReal.inv_two_add_inv_two]
  · rw [mem_singleton_iff.1 hx, ladderKernel_odd (by decide)]
    simp

/-- Every state reaches `1`. -/
theorem ladder_reaches_one (n : ℕ) : ∃ k, 0 < (ladderKernel ^ (k + 1)) n {1} := by
  obtain ⟨k, hk⟩ := ladder_reaches_zero n
  refine ⟨k + 1, ?_⟩
  have h01 : 0 < (ladderKernel ^ 1) 0 {1} := by
    rw [pow_one]
    change 0 < ladderMeas 0 {1}
    simp [ladderMeas, Measure.add_apply, Measure.smul_apply]
  exact (ENNReal.mul_pos hk.ne' h01.ne').trans_le (pow_add_singleton_ge _ (k + 1) 1 n 0 1)

/-- **`δ₀ + δ₁` is a maximal irreducibility measure for the ladder chain.** -/
theorem ladder_isMaximalIrreducibility :
    haveI := isMarkovKernel_ladderKernel
    IsMaximalIrreducibility ladderKernel (Measure.dirac 0 + Measure.dirac 1) := by
  have := isMarkovKernel_ladderKernel
  refine ⟨fun h => by simpa using congrArg (fun μ : Measure ℕ => μ {0}) h, ?_, ?_⟩
  · intro B hB hpos x
    rw [Measure.add_apply, Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB] at hpos
    by_cases h0 : (0 : ℕ) ∈ B
    · obtain ⟨k, hk⟩ := ladder_reaches_zero x
      exact (hk.trans_le (measure_mono (singleton_subset_iff.2 h0))).trans_le
        (pow_le_hitProb _ hB k x)
    · have h1 : (1 : ℕ) ∈ B := by
        by_contra h1
        simp [h0, h1] at hpos
      obtain ⟨k, hk⟩ := ladder_reaches_one x
      exact (hk.trans_le (measure_mono (singleton_subset_iff.2 h1))).trans_le
        (pow_le_hitProb _ hB k x)
  · intro φ hφ
    refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
    rw [Measure.add_apply, Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB,
      add_eq_zero] at h0
    have hB01 : B ⊆ ({0, 1} : Set ℕ)ᶜ := fun y hy hy01 => by
      rcases hy01 with rfl | rfl
      · simp [hy] at h0
      · simp [hy] at h0
    by_contra hpos
    have h := hφ B hB (pos_iff_ne_zero.2 hpos) 0
    have hc := ladder_isAbsorbing_zero_one.hitProb_compl (measurableSet_of_countable _)
      (show (0 : ℕ) ∈ ({0, 1} : Set ℕ) from Or.inl rfl)
    exact h.ne' (le_antisymm ((measure_mono fun ω hω => by
      obtain ⟨n, hn, h'⟩ := (firstReturn_ne_top_iff B ω).1 hω
      exact (firstReturn_ne_top_iff _ ω).2 ⟨n, hn, hB01 h'⟩).trans_eq hc) zero_le)

/-- **Correction to Proposition 5.5.6 (ii)**, with all of the book's hypotheses. The ladder
chain is `ψ`-irreducible (with maximal `ψ = δ₀ + δ₁`) and strongly aperiodic. The set `A` of even
states is `½δ₀`-small with `ψ(A) > 0`, and it is the set on which the chain is split. Yet
`A × Bool = A₀ ∪ A₁` is not petite for the split chain. -/
theorem proposition_5_5_6_ii_counterexample_irreducible :
    haveI := isMarkovKernel_ladderKernel
    IsMaximalIrreducibility ladderKernel (Measure.dirac 0 + Measure.dirac 1) ∧
      IsStronglyAperiodic ladderKernel ∧
      IsSmallSet ladderKernel 1 ((2⁻¹ : ℝ≥0∞) • Measure.dirac 0) {n | Even n} ∧
      0 < (Measure.dirac 0 + Measure.dirac 1 : Measure ℕ) {n | Even n} ∧
      ladderMinorization.C = {n | Even n} ∧
      ¬ IsPetite ladderMinorization.splitKernel ({n | Even n} ×ˢ univ) := by
  have := isMarkovKernel_ladderKernel
  refine ⟨ladder_isMaximalIrreducibility, ladder_isStronglyAperiodic,
    ⟨measurableSet_of_countable _, one_pos, smul_measure_ne_zero (by simp) (by simp),
      fun x hx => by rw [pow_one]; exact ladderMinorization.le x hx⟩, ?_, rfl,
    proposition_5_5_6_ii_counterexample.2⟩
  rw [Measure.add_apply, Measure.dirac_apply' _ (measurableSet_of_countable _)]
  simp

end MeynTweedie.PseudoAtoms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The three kinds of state space (MT §3.1)

Meyn and Tweedie, §3.1, p. 50, "State space definitions".

* `IsCountableStateSpace`: `X` is countable and every subset is measurable.
* `IsGeneralStateSpace`: the σ-algebra of `X` is countably generated.
* `IsTopologicalStateSpace`: `X` is locally compact, separable and metrizable, with its Borel
  σ-algebra.
* `IsCountableStateSpace.isGeneral`, `IsTopologicalStateSpace.isGeneral`: countable and
  topological state spaces are general state spaces.

None of the results of this chapter need these assumptions: the construction of the chain
(Theorem 3.4.1) and the Markov and strong Markov properties hold on every measurable space.

**Corrections.** None.
-/

namespace MeynTweedie.PseudoAtoms

variable (X : Type*) [MeasurableSpace X]

/-- A countable state space (MT p. 50): `X` is countable and `B(X)` is all subsets of `X`. -/
def IsCountableStateSpace : Prop := Countable X ∧ ∀ s : Set X, MeasurableSet s

/-- A general state space (MT p. 50): `B(X)` is countably generated. -/
def IsGeneralStateSpace : Prop := MeasurableSpace.CountablyGenerated X

/-- A topological state space (MT p. 50): a locally compact, separable, metrizable space with
its Borel σ-algebra. -/
def IsTopologicalStateSpace [TopologicalSpace X] : Prop :=
  LocallyCompactSpace X ∧ TopologicalSpace.SeparableSpace X ∧
    TopologicalSpace.MetrizableSpace X ∧ BorelSpace X

variable {X}

/-- A countable state space is a general state space. -/
theorem IsCountableStateSpace.isGeneral (h : IsCountableStateSpace X) :
    IsGeneralStateSpace X := by
  obtain ⟨h1, h2⟩ := h
  have : MeasurableSingletonClass X := ⟨fun x => h2 {x}⟩
  exact inferInstanceAs (MeasurableSpace.CountablyGenerated X)

/-- A topological state space is a general state space. -/
theorem IsTopologicalStateSpace.isGeneral [TopologicalSpace X] (h : IsTopologicalStateSpace X) :
    IsGeneralStateSpace X := by
  obtain ⟨-, h2, h3, h4⟩ := h
  let := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  have := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  exact inferInstanceAs (MeasurableSpace.CountablyGenerated X)

end MeynTweedie.PseudoAtoms

set_option linter.style.longLine false
#print axioms MeynTweedie.PseudoAtoms.trajKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_trajKernel
#print axioms MeynTweedie.PseudoAtoms.pathKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_pathKernel
#print axioms MeynTweedie.PseudoAtoms.pathMeasure
#print axioms MeynTweedie.PseudoAtoms.isProbabilityMeasure_pathMeasure
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_eq_comp
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_dirac
#print axioms MeynTweedie.PseudoAtoms.pathKernel_map_zero
#print axioms MeynTweedie.PseudoAtoms.pathKernel_zero_mem
#print axioms MeynTweedie.PseudoAtoms.ae_pathKernel_zero
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_inter_zero
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_map_zero
#print axioms MeynTweedie.PseudoAtoms.natFilt
#print axioms MeynTweedie.PseudoAtoms.measurable_coord_natFilt
#print axioms MeynTweedie.PseudoAtoms.measurableSet_coord_natFilt
#print axioms MeynTweedie.PseudoAtoms.setLIntegral_succ
#print axioms MeynTweedie.PseudoAtoms.cylFn
#print axioms MeynTweedie.PseudoAtoms.measurable_cylFn
#print axioms MeynTweedie.PseudoAtoms.boxSet
#print axioms MeynTweedie.PseudoAtoms.measurableSet_boxSet
#print axioms MeynTweedie.PseudoAtoms.measure_inter_shift_box
#print axioms MeynTweedie.PseudoAtoms.pathKernel_boxSet
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_boxSet
#print axioms MeynTweedie.PseudoAtoms.IsMarkovChain
#print axioms MeynTweedie.PseudoAtoms.IsMarkovChain.mk
#print axioms MeynTweedie.PseudoAtoms.IsMarkovChain.measurable
#print axioms MeynTweedie.PseudoAtoms.IsMarkovChain.fdd
#print axioms MeynTweedie.PseudoAtoms.theorem_3_4_1
#print axioms MeynTweedie.PseudoAtoms.generateFrom_boxSets
#print axioms MeynTweedie.PseudoAtoms.isPiSystem_boxSets
#print axioms MeynTweedie.PseudoAtoms.theorem_3_4_1_unique
#print axioms MeynTweedie.PseudoAtoms.law_eq_pathMeasure
#print axioms MeynTweedie.PseudoAtoms.IsSubstochasticKernel
#print axioms MeynTweedie.PseudoAtoms.isSubstochasticKernel_of_markov
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_pow
#print axioms MeynTweedie.PseudoAtoms.pow_zero_apply
#print axioms MeynTweedie.PseudoAtoms.pow_succ_apply
#print axioms MeynTweedie.PseudoAtoms.pow_succ_apply'
#print axioms MeynTweedie.PseudoAtoms.theorem_3_4_2
#print axioms MeynTweedie.PseudoAtoms.pow_add_eq
#print axioms MeynTweedie.PseudoAtoms.skeleton
#print axioms MeynTweedie.PseudoAtoms.skeleton_pow
#print axioms MeynTweedie.PseudoAtoms.sampledKernel
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_apply
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_sampledKernel
#print axioms MeynTweedie.PseudoAtoms.resolvent
#print axioms MeynTweedie.PseudoAtoms.resolvent_apply
#print axioms MeynTweedie.PseudoAtoms.tsum_geometric_weights
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_resolvent
#print axioms MeynTweedie.PseudoAtoms.kfun
#print axioms MeynTweedie.PseudoAtoms.measurable_kfun
#print axioms MeynTweedie.PseudoAtoms.kfun_indicator
#print axioms MeynTweedie.PseudoAtoms.kfun_one
#print axioms MeynTweedie.PseudoAtoms.kfun_mono
#print axioms MeynTweedie.PseudoAtoms.kfun_add
#print axioms MeynTweedie.PseudoAtoms.kfun_const_mul
#print axioms MeynTweedie.PseudoAtoms.kfun_comp
#print axioms MeynTweedie.PseudoAtoms.kfun_pow_succ
#print axioms MeynTweedie.PseudoAtoms.measure_kernel_apply
#print axioms MeynTweedie.PseudoAtoms.measure_kernel_assoc
#print axioms MeynTweedie.PseudoAtoms.lintegral_kfun
#print axioms MeynTweedie.PseudoAtoms.isProbabilityMeasure_measure_kernel
#print axioms MeynTweedie.PseudoAtoms.dirac_kernel
#print axioms MeynTweedie.PseudoAtoms.kfunR
#print axioms MeynTweedie.PseudoAtoms.measurable_kfunR
#print axioms MeynTweedie.PseudoAtoms.abs_kfunR_le
#print axioms MeynTweedie.PseudoAtoms.indKernel
#print axioms MeynTweedie.PseudoAtoms.indKernel_apply
#print axioms MeynTweedie.PseudoAtoms.comp_indKernel_apply
#print axioms MeynTweedie.PseudoAtoms.isSubstochasticKernel_comp_indKernel
#print axioms MeynTweedie.PseudoAtoms.potKernel
#print axioms MeynTweedie.PseudoAtoms.potKernel_apply
#print axioms MeynTweedie.PseudoAtoms.shift
#print axioms MeynTweedie.PseudoAtoms.measurable_shift
#print axioms MeynTweedie.PseudoAtoms.shift_zero
#print axioms MeynTweedie.PseudoAtoms.shift_shift
#print axioms MeynTweedie.PseudoAtoms.shift_apply
#print axioms MeynTweedie.PseudoAtoms.integral_measure_comp
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_map_coord
#print axioms MeynTweedie.PseudoAtoms.pathKernel_map_coord
#print axioms MeynTweedie.PseudoAtoms.pathKernel_coord_mem
#print axioms MeynTweedie.PseudoAtoms.pathKernel_coord_chapmanKolmogorov
#print axioms MeynTweedie.PseudoAtoms.markov_measure
#print axioms MeynTweedie.PseudoAtoms.markov_lintegral
#print axioms MeynTweedie.PseudoAtoms.markov_lintegral_mul
#print axioms MeynTweedie.PseudoAtoms.markov_lintegral_univ
#print axioms MeynTweedie.PseudoAtoms.markov_setIntegral
#print axioms MeynTweedie.PseudoAtoms.stronglyMeasurable_expect_coord
#print axioms MeynTweedie.PseudoAtoms.integrable_expect_coord
#print axioms MeynTweedie.PseudoAtoms.markov_property
#print axioms MeynTweedie.PseudoAtoms.integrable_shift_of_bdd
#print axioms MeynTweedie.PseudoAtoms.markov_property_bdd
#print axioms MeynTweedie.PseudoAtoms.proposition_3_4_3
#print axioms MeynTweedie.PseudoAtoms.isMarkovChain_of_step
#print axioms MeynTweedie.PseudoAtoms.skeletonFilt
#print axioms MeynTweedie.PseudoAtoms.skeleton_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.iSup_natFilt
#print axioms MeynTweedie.PseudoAtoms.setOf_le_eq_biUnion
#print axioms MeynTweedie.PseudoAtoms.setOf_ne_top_eq_iUnion
#print axioms MeynTweedie.PseudoAtoms.measurableSet_ne_top
#print axioms MeynTweedie.PseudoAtoms.measurableSet_stoppedField_iff
#print axioms MeynTweedie.PseudoAtoms.measurableSet_stoppedField_ne_top
#print axioms MeynTweedie.PseudoAtoms.stoppedState
#print axioms MeynTweedie.PseudoAtoms.shiftAt
#print axioms MeynTweedie.PseudoAtoms.stoppedState_of_eq
#print axioms MeynTweedie.PseudoAtoms.shiftAt_of_eq
#print axioms MeynTweedie.PseudoAtoms.measurable_of_stopping_pieces
#print axioms MeynTweedie.PseudoAtoms.measurable_stoppedState
#print axioms MeynTweedie.PseudoAtoms.measurable_shiftAt
#print axioms MeynTweedie.PseudoAtoms.measurable_stoppedField_indicator
#print axioms MeynTweedie.PseudoAtoms.inter_ne_top_eq_iUnion
#print axioms MeynTweedie.PseudoAtoms.pairwise_disjoint_inter_eq
#print axioms MeynTweedie.PseudoAtoms.strong_markov_lintegral
#print axioms MeynTweedie.PseudoAtoms.strong_markov_lintegral_mul
#print axioms MeynTweedie.PseudoAtoms.strong_markov_measure
#print axioms MeynTweedie.PseudoAtoms.strong_markov_setIntegral
#print axioms MeynTweedie.PseudoAtoms.strong_markov_property
#print axioms MeynTweedie.PseudoAtoms.StrongMarkovProperty
#print axioms MeynTweedie.PseudoAtoms.proposition_3_4_6
#print axioms MeynTweedie.PseudoAtoms.occTime
#print axioms MeynTweedie.PseudoAtoms.firstReturn
#print axioms MeynTweedie.PseudoAtoms.firstHit
#print axioms MeynTweedie.PseudoAtoms.returnTimeK
#print axioms MeynTweedie.PseudoAtoms.hitProb
#print axioms MeynTweedie.PseudoAtoms.returnTimeK_one
#print axioms MeynTweedie.PseudoAtoms.returnTimeK_succ_of_eq
#print axioms MeynTweedie.PseudoAtoms.returnTimeK_succ_of_top
#print axioms MeynTweedie.PseudoAtoms.firstReturn_ne_top_iff
#print axioms MeynTweedie.PseudoAtoms.le_firstReturn_iff
#print axioms MeynTweedie.PseudoAtoms.one_le_firstReturn
#print axioms MeynTweedie.PseudoAtoms.firstReturn_eq_iff
#print axioms MeynTweedie.PseudoAtoms.le_firstReturn_succ_iff
#print axioms MeynTweedie.PseudoAtoms.firstHit_eq_zero_iff
#print axioms MeynTweedie.PseudoAtoms.firstHit_eq_firstReturn
#print axioms MeynTweedie.PseudoAtoms.adapted_coord
#print axioms MeynTweedie.PseudoAtoms.proposition_3_4_4
#print axioms MeynTweedie.PseudoAtoms.isStoppingTime_returnTimeK
#print axioms MeynTweedie.PseudoAtoms.measurableSet_firstReturn_ne_top
#print axioms MeynTweedie.PseudoAtoms.measurableSet_firstReturn_eq
#print axioms MeynTweedie.PseudoAtoms.measurableSet_le_firstReturn
#print axioms MeynTweedie.PseudoAtoms.measurable_occTime
#print axioms MeynTweedie.PseudoAtoms.measurable_hitProb
#print axioms MeynTweedie.PseudoAtoms.potKernel_eq_lintegral_occTime
#print axioms MeynTweedie.PseudoAtoms.pathKernel_first_step
#print axioms MeynTweedie.PseudoAtoms.tabooKernel
#print axioms MeynTweedie.PseudoAtoms.comp_indKernel_eq_restrict
#print axioms MeynTweedie.PseudoAtoms.tabooKernel_zero
#print axioms MeynTweedie.PseudoAtoms.tabooKernel_succ_apply
#print axioms MeynTweedie.PseudoAtoms.tabooProb
#print axioms MeynTweedie.PseudoAtoms.tabooProb_one
#print axioms MeynTweedie.PseudoAtoms.tabooProb_succ
#print axioms MeynTweedie.PseudoAtoms.tabooProb_eq_tabooKernel
#print axioms MeynTweedie.PseudoAtoms.firstReturn_eq_tabooProb
#print axioms MeynTweedie.PseudoAtoms.proposition_3_4_5_i
#print axioms MeynTweedie.PseudoAtoms.proposition_3_4_5_i_succ
#print axioms MeynTweedie.PseudoAtoms.firstReturn_eq_tabooKernel
#print axioms MeynTweedie.PseudoAtoms.nestedTaboo
#print axioms MeynTweedie.PseudoAtoms.firstReturn_eq_nestedTaboo
#print axioms MeynTweedie.PseudoAtoms.proposition_3_4_5_ii
#print axioms MeynTweedie.PseudoAtoms.hitProb_eq_tsum
#print axioms MeynTweedie.PseudoAtoms.hitProb_first_step
#print axioms MeynTweedie.PseudoAtoms.tabooPotKernel
#print axioms MeynTweedie.PseudoAtoms.tabooPotKernel_apply
#print axioms MeynTweedie.PseudoAtoms.tabooPotKernel_self
#print axioms MeynTweedie.PseudoAtoms.IsTransitionMatrix
#print axioms MeynTweedie.PseudoAtoms.matPow
#print axioms MeynTweedie.PseudoAtoms.matKernel
#print axioms MeynTweedie.PseudoAtoms.matKernel_singleton
#print axioms MeynTweedie.PseudoAtoms.matKernel_apply
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_matKernel
#print axioms MeynTweedie.PseudoAtoms.lintegral_matKernel
#print axioms MeynTweedie.PseudoAtoms.matKernel_pow_singleton
#print axioms MeynTweedie.PseudoAtoms.matKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.isTransitionMatrix_matPow
#print axioms MeynTweedie.PseudoAtoms.cylFn_singletons
#print axioms MeynTweedie.PseudoAtoms.theorem_3_2_1_fdd
#print axioms MeynTweedie.PseudoAtoms.IsMarkovChain.fdd_points
#print axioms MeynTweedie.PseudoAtoms.theorem_3_2_1
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_inter_initial
#print axioms MeynTweedie.PseudoAtoms.pathMeasure_initial_coord
#print axioms MeynTweedie.PseudoAtoms.firstReturn_ne_top_eq_iUnion
#print axioms MeynTweedie.PseudoAtoms.pow_le_hitProb
#print axioms MeynTweedie.PseudoAtoms.hitProb_pos_iff
#print axioms MeynTweedie.PseudoAtoms.hitProb_le_one
#print axioms MeynTweedie.PseudoAtoms.potKernel_pos_iff
#print axioms MeynTweedie.PseudoAtoms.pow_add_pos_iff
#print axioms MeynTweedie.PseudoAtoms.measurableSet_pow_pos
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbing
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbing.pow_apply
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbing.pow_compl
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbing.hitProb_compl
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbing.hitProb_eq_zero
#print axioms MeynTweedie.PseudoAtoms.restrictKernel
#print axioms MeynTweedie.PseudoAtoms.restrictKernel_apply
#print axioms MeynTweedie.PseudoAtoms.restrictKernel_apply_eq
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_restrictKernel
#print axioms MeynTweedie.PseudoAtoms.lintegral_restrictKernel
#print axioms MeynTweedie.PseudoAtoms.restrictKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.Leads
#print axioms MeynTweedie.PseudoAtoms.leads_iff_exists_pow
#print axioms MeynTweedie.PseudoAtoms.pow_add_singleton_ge
#print axioms MeynTweedie.PseudoAtoms.Leads.trans
#print axioms MeynTweedie.PseudoAtoms.Leads.refl
#print axioms MeynTweedie.PseudoAtoms.Communicates
#print axioms MeynTweedie.PseudoAtoms.proposition_4_1_1
#print axioms MeynTweedie.PseudoAtoms.commClass
#print axioms MeynTweedie.PseudoAtoms.mem_commClass_self
#print axioms MeynTweedie.PseudoAtoms.iUnion_commClass
#print axioms MeynTweedie.PseudoAtoms.commClass_eq_or_disjoint
#print axioms MeynTweedie.PseudoAtoms.commClass_eq_iff
#print axioms MeynTweedie.PseudoAtoms.IsIrreducibleChain
#print axioms MeynTweedie.PseudoAtoms.isIrreducibleChain_iff
#print axioms MeynTweedie.PseudoAtoms.nonAbsorbingPart
#print axioms MeynTweedie.PseudoAtoms.commClass_subset_nonAbsorbingPart
#print axioms MeynTweedie.PseudoAtoms.decomposition_4_5
#print axioms MeynTweedie.PseudoAtoms.decomposition_4_5_disjoint
#print axioms MeynTweedie.PseudoAtoms.measurableSet_of_countable
#print axioms MeynTweedie.PseudoAtoms.exists_singleton_pos_of_pos
#print axioms MeynTweedie.PseudoAtoms.not_isAbsorbing_commClass_iff
#print axioms MeynTweedie.PseudoAtoms.proposition_4_1_2
#print axioms MeynTweedie.PseudoAtoms.IsPhiIrreducible
#print axioms MeynTweedie.PseudoAtoms.resolventHalf
#print axioms MeynTweedie.PseudoAtoms.resolventHalf_apply
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_resolventHalf
#print axioms MeynTweedie.PseudoAtoms.resolventHalf_pos_iff
#print axioms MeynTweedie.PseudoAtoms.resolventHalf_eq_zero_iff
#print axioms MeynTweedie.PseudoAtoms.resolventHalf_equiv
#print axioms MeynTweedie.PseudoAtoms.hitProb_pos_of_compl
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_1
#print axioms MeynTweedie.PseudoAtoms.IsPhiIrreducible.mono
#print axioms MeynTweedie.PseudoAtoms.IsPhiIrreducible.restrict
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_zero
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_dirac_iff
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_dirac_of_leads
#print axioms MeynTweedie.PseudoAtoms.isIrreducibleChain_iff_count
#print axioms MeynTweedie.PseudoAtoms.exists_measure_pos_of_iUnion
#print axioms MeynTweedie.PseudoAtoms.setOf_resolventHalf_pos
#print axioms MeynTweedie.PseudoAtoms.setOf_hitProb_pos
#print axioms MeynTweedie.PseudoAtoms.measurableSet_hitProb_pos
#print axioms MeynTweedie.PseudoAtoms.exists_finite_equiv_of_ac
#print axioms MeynTweedie.PseudoAtoms.exists_prob_equiv
#print axioms MeynTweedie.PseudoAtoms.maxIrrMeasure
#print axioms MeynTweedie.PseudoAtoms.maxIrrMeasure_apply
#print axioms MeynTweedie.PseudoAtoms.maxIrrMeasure_univ
#print axioms MeynTweedie.PseudoAtoms.isProbabilityMeasure_maxIrrMeasure
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_maxIrrMeasure
#print axioms MeynTweedie.PseudoAtoms.ac_maxIrrMeasure
#print axioms MeynTweedie.PseudoAtoms.maxIrrMeasure_hitSet_null
#print axioms MeynTweedie.PseudoAtoms.maxIrrMeasure_comp_pow_le
#print axioms MeynTweedie.PseudoAtoms.IsMaximalIrreducibility
#print axioms MeynTweedie.PseudoAtoms.isMaximalIrreducibility_maxIrrMeasure
#print axioms MeynTweedie.PseudoAtoms.IsMaximalIrreducibility.isPhiIrreducible_iff
#print axioms MeynTweedie.PseudoAtoms.IsMaximalIrreducibility.equiv
#print axioms MeynTweedie.PseudoAtoms.IsMaximalIrreducibility.of_equiv
#print axioms MeynTweedie.PseudoAtoms.IsMaximalIrreducibility.hitSet_null
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_2
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_2_maximal
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_2_zero_counterexample
#print axioms MeynTweedie.PseudoAtoms.posSets
#print axioms MeynTweedie.PseudoAtoms.posSets_eq_of_maximal
#print axioms MeynTweedie.PseudoAtoms.IsFull
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_3_i
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_3_i_counterexample
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_3_ii
#print axioms MeynTweedie.PseudoAtoms.theorem_4_0_1
#print axioms MeynTweedie.PseudoAtoms.theorem_4_0_1_unique
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbingIrreducibleSet
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_4
#print axioms MeynTweedie.PseudoAtoms.proposition_4_2_4_nonzero
#print axioms MeynTweedie.PseudoAtoms.isMaximalIrreducibility_count
#print axioms MeynTweedie.PseudoAtoms.IsAccessibleFrom
#print axioms MeynTweedie.PseudoAtoms.UnifAccessible
#print axioms MeynTweedie.PseudoAtoms.UnifAccessible.isAccessibleFrom
#print axioms MeynTweedie.PseudoAtoms.stoppedState_firstReturn_mem
#print axioms MeynTweedie.PseudoAtoms.hitProb_ge_mul
#print axioms MeynTweedie.PseudoAtoms.lemma_4_2_5
#print axioms MeynTweedie.PseudoAtoms.hitSet
#print axioms MeynTweedie.PseudoAtoms.hitSetLevel
#print axioms MeynTweedie.PseudoAtoms.noHitSet
#print axioms MeynTweedie.PseudoAtoms.noHitSet_eq_compl
#print axioms MeynTweedie.PseudoAtoms.measurableSet_hitSetLevel
#print axioms MeynTweedie.PseudoAtoms.lemma_4_2_6_bound
#print axioms MeynTweedie.PseudoAtoms.lemma_4_2_6
#print axioms MeynTweedie.PseudoAtoms.countable_cover_unifAccessible
#print axioms MeynTweedie.PseudoAtoms.IsAtom
#print axioms MeynTweedie.PseudoAtoms.isAtom_singleton
#print axioms MeynTweedie.PseudoAtoms.IsAccessibleAtom
#print axioms MeynTweedie.PseudoAtoms.IsMaximalIrreducibility.pos_iff_hitProb_pos
#print axioms MeynTweedie.PseudoAtoms.pow_succ_ge_of_atom
#print axioms MeynTweedie.PseudoAtoms.exists_pow_comp_pos
#print axioms MeynTweedie.PseudoAtoms.hitProb_pos_of_exists_pow
#print axioms MeynTweedie.PseudoAtoms.proposition_5_1_1
#print axioms MeynTweedie.PseudoAtoms.hitProb_atom_eq
#print axioms MeynTweedie.PseudoAtoms.proposition_5_1_2
#print axioms MeynTweedie.PseudoAtoms.fwdRecMatrix
#print axioms MeynTweedie.PseudoAtoms.isTransitionMatrix_fwdRecMatrix
#print axioms MeynTweedie.PseudoAtoms.ptail
#print axioms MeynTweedie.PseudoAtoms.ptail_eq
#print axioms MeynTweedie.PseudoAtoms.ptail_ne_zero_iff
#print axioms MeynTweedie.PseudoAtoms.bwdRecMatrix
#print axioms MeynTweedie.PseudoAtoms.bwdRecMatrix_rowSum
#print axioms MeynTweedie.PseudoAtoms.ptail_ne_zero_of_bwdRecMatrix
#print axioms MeynTweedie.PseudoAtoms.bwdRecMatrix_zero
#print axioms MeynTweedie.PseudoAtoms.halfHalf
#print axioms MeynTweedie.PseudoAtoms.bwdRecMatrix_display_counterexample
#print axioms MeynTweedie.PseudoAtoms.rwMatrix
#print axioms MeynTweedie.PseudoAtoms.isTransitionMatrix_rwMatrix
#print axioms MeynTweedie.PseudoAtoms.rwMatrix_translate
#print axioms MeynTweedie.PseudoAtoms.rw_step_law
#print axioms MeynTweedie.PseudoAtoms.rwhlMatrix
#print axioms MeynTweedie.PseudoAtoms.isTransitionMatrix_rwhlMatrix
#print axioms MeynTweedie.PseudoAtoms.storage_increment_singleton
#print axioms MeynTweedie.PseudoAtoms.storage_increment_counterexample
#print axioms MeynTweedie.PseudoAtoms.poissonWeight
#print axioms MeynTweedie.PseudoAtoms.poissonWeight_eq
#print axioms MeynTweedie.PseudoAtoms.tsum_poissonWeight
#print axioms MeynTweedie.PseudoAtoms.giM1Matrix
#print axioms MeynTweedie.PseudoAtoms.giM1Increment
#print axioms MeynTweedie.PseudoAtoms.giM1Matrix_eq_rwhl
#print axioms MeynTweedie.PseudoAtoms.tsum_giM1Increment
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_1
#print axioms MeynTweedie.PseudoAtoms.mG1Matrix
#print axioms MeynTweedie.PseudoAtoms.isTransitionMatrix_mG1Matrix
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_2
#print axioms MeynTweedie.PseudoAtoms.arMatrix
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_3
#print axioms MeynTweedie.PseudoAtoms.matKernel_pow_one_singleton
#print axioms MeynTweedie.PseudoAtoms.leads_of_pos
#print axioms MeynTweedie.PseudoAtoms.isAbsorbing_matKernel_iff
#print axioms MeynTweedie.PseudoAtoms.IsAbsorbing.mem_of_leads
#print axioms MeynTweedie.PseudoAtoms.Leads.step
#print axioms MeynTweedie.PseudoAtoms.rwhl_zero_ge
#print axioms MeynTweedie.PseudoAtoms.rwhl_pow_zero_ge
#print axioms MeynTweedie.PseudoAtoms.rwhl_hitProb_zero_pos
#print axioms MeynTweedie.PseudoAtoms.rwhl_hitProb_zero_eq_zero
#print axioms MeynTweedie.PseudoAtoms.diracZeroInt
#print axioms MeynTweedie.PseudoAtoms.rwhl_dichotomy_counterexample
#print axioms MeynTweedie.PseudoAtoms.rwhl_even_increments
#print axioms MeynTweedie.PseudoAtoms.fwdRec_isAbsorbing
#print axioms MeynTweedie.PseudoAtoms.fwdRec_leads_down
#print axioms MeynTweedie.PseudoAtoms.fwdRec_pow_down
#print axioms MeynTweedie.PseudoAtoms.fwdRec_communicates
#print axioms MeynTweedie.PseudoAtoms.giM1_isIrreducibleChain
#print axioms MeynTweedie.PseudoAtoms.poissonWeight_ne_zero
#print axioms MeynTweedie.PseudoAtoms.giM1_poisson_isIrreducibleChain
#print axioms MeynTweedie.PseudoAtoms.poissonWeight_dirac_zero
#print axioms MeynTweedie.PseudoAtoms.giM1_dirac_counterexample
#print axioms MeynTweedie.PseudoAtoms.mG1_isIrreducibleChain
#print axioms MeynTweedie.PseudoAtoms.mG1_poisson_isIrreducibleChain
#print axioms MeynTweedie.PseudoAtoms.mG1_dirac_counterexample
#print axioms MeynTweedie.PseudoAtoms.rwSupportGroup
#print axioms MeynTweedie.PseudoAtoms.rw_closure_eq_zmultiples
#print axioms MeynTweedie.PseudoAtoms.rw_coset_isAbsorbing
#print axioms MeynTweedie.PseudoAtoms.rw_leads_add
#print axioms MeynTweedie.PseudoAtoms.rw_monoid_eq_group
#print axioms MeynTweedie.PseudoAtoms.rw_commClass_eq
#print axioms MeynTweedie.PseudoAtoms.rw_commClass_finite
#print axioms MeynTweedie.PseudoAtoms.ratClass
#print axioms MeynTweedie.PseudoAtoms.ratWalk_isAbsorbing
#print axioms MeynTweedie.PseudoAtoms.ratWalk_commClass_eq
#print axioms MeynTweedie.PseudoAtoms.ratWalk_commClass_infinite
#print axioms MeynTweedie.PseudoAtoms.Minorization
#print axioms MeynTweedie.PseudoAtoms.Minorization.mk
#print axioms MeynTweedie.PseudoAtoms.Minorization.C
#print axioms MeynTweedie.PseudoAtoms.Minorization.δ
#print axioms MeynTweedie.PseudoAtoms.Minorization.ν
#print axioms MeynTweedie.PseudoAtoms.Minorization.measurableSet_C
#print axioms MeynTweedie.PseudoAtoms.Minorization.δ_pos
#print axioms MeynTweedie.PseudoAtoms.Minorization.δ_lt_one
#print axioms MeynTweedie.PseudoAtoms.Minorization.isProbabilityMeasure_ν
#print axioms MeynTweedie.PseudoAtoms.Minorization.le
#print axioms MeynTweedie.PseudoAtoms.Minorization.IsConcentrated
#print axioms MeynTweedie.PseudoAtoms.Minorization.δ_ne_top
#print axioms MeynTweedie.PseudoAtoms.Minorization.one_sub_δ_ne_zero
#print axioms MeynTweedie.PseudoAtoms.Minorization.isFiniteMeasure_smul_ν
#print axioms MeynTweedie.PseudoAtoms.Minorization.le_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.ofLe
#print axioms MeynTweedie.PseudoAtoms.Minorization.ofLe_C
#print axioms MeynTweedie.PseudoAtoms.Minorization.ofLe_isConcentrated
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitProb
#print axioms MeynTweedie.PseudoAtoms.Minorization.measurable_splitProb
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitProb_le
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitProb_le_one
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitProb_of_mem
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitProb_of_notMem
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitMeas
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitMeas_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitK
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitK_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.isMarkovKernel_splitK
#print axioms MeynTweedie.PseudoAtoms.Minorization.lintegral_splitK
#print axioms MeynTweedie.PseudoAtoms.Minorization.split
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.lintegral_split
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_apply_false
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_apply_true
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_bottom
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_fst_preimage
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_map_fst
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_univ
#print axioms MeynTweedie.PseudoAtoms.Minorization.isProbabilityMeasure_split
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_add
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_smul
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_sub
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_restrict_fst
#print axioms MeynTweedie.PseudoAtoms.Minorization.residMeas
#print axioms MeynTweedie.PseudoAtoms.Minorization.residMeas_apply_of_mem
#print axioms MeynTweedie.PseudoAtoms.Minorization.residMeas_of_notMem
#print axioms MeynTweedie.PseudoAtoms.Minorization.resid
#print axioms MeynTweedie.PseudoAtoms.Minorization.resid_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.isMarkovKernel_resid
#print axioms MeynTweedie.PseudoAtoms.Minorization.baseMeas
#print axioms MeynTweedie.PseudoAtoms.Minorization.baseK
#print axioms MeynTweedie.PseudoAtoms.Minorization.baseK_apply_false
#print axioms MeynTweedie.PseudoAtoms.Minorization.baseK_apply_true
#print axioms MeynTweedie.PseudoAtoms.Minorization.isMarkovKernel_baseK
#print axioms MeynTweedie.PseudoAtoms.Minorization.baseK_comp_splitK
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.isMarkovKernel_splitKernel
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_apply_false_of_notMem
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_apply_false_of_mem
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_apply_true
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_comp_splitKernel
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_comp_splitKernel_pow
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_pow_succ
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_pow_succ_apply
#print axioms MeynTweedie.PseudoAtoms.Minorization.theorem_5_1_3_i
#print axioms MeynTweedie.PseudoAtoms.Minorization.isAtom_bottom
#print axioms MeynTweedie.PseudoAtoms.Minorization.checkAlpha
#print axioms MeynTweedie.PseudoAtoms.Minorization.measurableSet_checkAlpha
#print axioms MeynTweedie.PseudoAtoms.Minorization.isAtom_checkAlpha
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_bottom_compl
#print axioms MeynTweedie.PseudoAtoms.Minorization.splitKernel_pow_bottom_compl
#print axioms MeynTweedie.PseudoAtoms.Minorization.lintegral_cylFn_split
#print axioms MeynTweedie.PseudoAtoms.Minorization.theorem_5_1_3_i_path
#print axioms MeynTweedie.PseudoAtoms.Minorization.isMarkovChain_split_fst
#print axioms MeynTweedie.PseudoAtoms.Minorization.lintegral_split_fst
#print axioms MeynTweedie.PseudoAtoms.Minorization.lintegral_split_coord
#print axioms MeynTweedie.PseudoAtoms.Minorization.one_sub_mul_le_split_false
#print axioms MeynTweedie.PseudoAtoms.Minorization.subset_sections
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_pos_cases
#print axioms MeynTweedie.PseudoAtoms.Minorization.isPhiIrreducible_of_split
#print axioms MeynTweedie.PseudoAtoms.Minorization.isPhiIrreducible_split
#print axioms MeynTweedie.PseudoAtoms.Minorization.isPhiIrreducible_split_iff
#print axioms MeynTweedie.PseudoAtoms.Minorization.theorem_5_1_3_ii
#print axioms MeynTweedie.PseudoAtoms.Minorization.isMaximalIrreducibility_split
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet
#print axioms MeynTweedie.PseudoAtoms.IsSmall
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.le_apply
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.mono
#print axioms MeynTweedie.PseudoAtoms.smul_measure_ne_zero
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.smul
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.measure_univ_le
#print axioms MeynTweedie.PseudoAtoms.isSmallSet_of_atom
#print axioms MeynTweedie.PseudoAtoms.pow_add_ge_of_le
#print axioms MeynTweedie.PseudoAtoms.smul_le_pow_add_of_le
#print axioms MeynTweedie.PseudoAtoms.comp_le_comp
#print axioms MeynTweedie.PseudoAtoms.proposition_5_2_4_i
#print axioms MeynTweedie.PseudoAtoms.proposition_5_2_4_iii
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.minorization
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.minorization_C
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.minorization_isConcentrated
#print axioms MeynTweedie.PseudoAtoms.transDensity
#print axioms MeynTweedie.PseudoAtoms.measurable_transDensity
#print axioms MeynTweedie.PseudoAtoms.setLIntegral_transDensity_le
#print axioms MeynTweedie.PseudoAtoms.lintegral_transDensity_mul_le
#print axioms MeynTweedie.PseudoAtoms.theorem_5_2_1_density
#print axioms MeynTweedie.PseudoAtoms.ae_exists_transDensity_pos
#print axioms MeynTweedie.PseudoAtoms.measure_inter_le_add_symmDiff
#print axioms MeynTweedie.PseudoAtoms.eq_zero_of_forall_lt_five_inv
#print axioms MeynTweedie.PseudoAtoms.exists_rect_of_not_ae_zero
#print axioms MeynTweedie.PseudoAtoms.densLevel
#print axioms MeynTweedie.PseudoAtoms.measurableSet_densLevel
#print axioms MeynTweedie.PseudoAtoms.exists_densLevel_not_ae_zero
#print axioms MeynTweedie.PseudoAtoms.theorem_5_2_1
#print axioms MeynTweedie.PseudoAtoms.theorem_5_2_1_density_ge
#print axioms MeynTweedie.PseudoAtoms.theorem_5_2_2
#print axioms MeynTweedie.PseudoAtoms.theorem_5_2_3
#print axioms MeynTweedie.PseudoAtoms.smul_pow_le_resolvent
#print axioms MeynTweedie.PseudoAtoms.theorem_5_2_3_resolvent
#print axioms MeynTweedie.PseudoAtoms.proposition_5_2_4_ii
#print axioms MeynTweedie.PseudoAtoms.IsAddClosed
#print axioms MeynTweedie.PseudoAtoms.setGcd
#print axioms MeynTweedie.PseudoAtoms.IsAddClosed.succ_mul_mem
#print axioms MeynTweedie.PseudoAtoms.IsAddClosed.mul_mem_zero
#print axioms MeynTweedie.PseudoAtoms.IsAddClosed.add_mem_of_zero
#print axioms MeynTweedie.PseudoAtoms.exists_gcd_witness
#print axioms MeynTweedie.PseudoAtoms.setGcd_spec
#print axioms MeynTweedie.PseudoAtoms.setGcd_dvd
#print axioms MeynTweedie.PseudoAtoms.dvd_setGcd
#print axioms MeynTweedie.PseudoAtoms.setGcd_pos
#print axioms MeynTweedie.PseudoAtoms.lemma_D_7_4
#print axioms MeynTweedie.PseudoAtoms.returnSet
#print axioms MeynTweedie.PseudoAtoms.periodAt
#print axioms MeynTweedie.PseudoAtoms.pow_apply_eq_one_of_step
#print axioms MeynTweedie.PseudoAtoms.returnSet_isAddClosed
#print axioms MeynTweedie.PseudoAtoms.periodAt_dvd
#print axioms MeynTweedie.PseudoAtoms.exists_pow_pos_of_communicates
#print axioms MeynTweedie.PseudoAtoms.periodAt_dvd_of_communicates
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_1
#print axioms MeynTweedie.PseudoAtoms.exists_return_pow_pos
#print axioms MeynTweedie.PseudoAtoms.cyclicClass
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_2
#print axioms MeynTweedie.PseudoAtoms.IsAperiodicCountable
#print axioms MeynTweedie.PseudoAtoms.IsStronglyAperiodicCountable
#print axioms MeynTweedie.PseudoAtoms.IsStronglyAperiodicCountable.isAperiodic
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_3
#print axioms MeynTweedie.PseudoAtoms.cycleChain
#print axioms MeynTweedie.PseudoAtoms.cycleChain_pow
#print axioms MeynTweedie.PseudoAtoms.cycleChain_pow_self
#print axioms MeynTweedie.PseudoAtoms.periodAt_cycleChain
#print axioms MeynTweedie.PseudoAtoms.IsCycle
#print axioms MeynTweedie.PseudoAtoms.IsCycle.mk
#print axioms MeynTweedie.PseudoAtoms.IsCycle.measurableSet
#print axioms MeynTweedie.PseudoAtoms.IsCycle.disjoint
#print axioms MeynTweedie.PseudoAtoms.IsCycle.step
#print axioms MeynTweedie.PseudoAtoms.IsCycle.null_compl
#print axioms MeynTweedie.PseudoAtoms.IsCycle.pow_apply
#print axioms MeynTweedie.PseudoAtoms.IsCycle.pow_apply_eq_zero
#print axioms MeynTweedie.PseudoAtoms.smallTimes
#print axioms MeynTweedie.PseudoAtoms.smul_measure_le_smul
#print axioms MeynTweedie.PseudoAtoms.smallTimes_isAddClosed
#print axioms MeynTweedie.PseudoAtoms.mem_smallTimes_of_isSmallSet
#print axioms MeynTweedie.PseudoAtoms.isSmallSet_of_mem_smallTimes
#print axioms MeynTweedie.PseudoAtoms.IsSmallSet.isPhiIrreducible
#print axioms MeynTweedie.PseudoAtoms.smul_le_comp_of_le
#print axioms MeynTweedie.PseudoAtoms.mem_smallTimes_of_return
#print axioms MeynTweedie.PseudoAtoms.cycleSet
#print axioms MeynTweedie.PseudoAtoms.cycleSet_eq_iUnion
#print axioms MeynTweedie.PseudoAtoms.measurableSet_cycleSet
#print axioms MeynTweedie.PseudoAtoms.iUnion_cycleSet
#print axioms MeynTweedie.PseudoAtoms.measure_cycleSet_inter
#print axioms MeynTweedie.PseudoAtoms.exists_isCycle_gcd
#print axioms MeynTweedie.PseudoAtoms.exists_measure_pos_of_iUnion'
#print axioms MeynTweedie.PseudoAtoms.exists_class_of_isCycle
#print axioms MeynTweedie.PseudoAtoms.dvd_gcd_of_isCycle
#print axioms MeynTweedie.PseudoAtoms.isCycle_subset_ae
#print axioms MeynTweedie.PseudoAtoms.theorem_5_4_4_unique
#print axioms MeynTweedie.PseudoAtoms.theorem_5_4_4
#print axioms MeynTweedie.PseudoAtoms.exists_isSmallSet_mul_gcd
#print axioms MeynTweedie.PseudoAtoms.exists_class_subset_ae
#print axioms MeynTweedie.PseudoAtoms.IsPeriod
#print axioms MeynTweedie.PseudoAtoms.IsAperiodic
#print axioms MeynTweedie.PseudoAtoms.IsStronglyAperiodic
#print axioms MeynTweedie.PseudoAtoms.IsPeriod.unique
#print axioms MeynTweedie.PseudoAtoms.isPeriod_gcd
#print axioms MeynTweedie.PseudoAtoms.IsPeriod.eq_gcd
#print axioms MeynTweedie.PseudoAtoms.exists_isPeriod
#print axioms MeynTweedie.PseudoAtoms.smallTimes_smul
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_of_pow_skeleton
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_5_i
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_5_ii
#print axioms MeynTweedie.PseudoAtoms.exists_forall_mem_smallTimes_of_aperiodic
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_5_iii
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_6
#print axioms MeynTweedie.PseudoAtoms.measure_setOf_eq_one
#print axioms MeynTweedie.PseudoAtoms.IsCycle.measure_pos
#print axioms MeynTweedie.PseudoAtoms.zmod_phase_succ
#print axioms MeynTweedie.PseudoAtoms.zmod_phase_inj
#print axioms MeynTweedie.PseudoAtoms.zmod_phase_exists
#print axioms MeynTweedie.PseudoAtoms.liftPiece
#print axioms MeynTweedie.PseudoAtoms.liftClass
#print axioms MeynTweedie.PseudoAtoms.prob_inter_eq_one
#print axioms MeynTweedie.PseudoAtoms.mem_liftClass
#print axioms MeynTweedie.PseudoAtoms.measure_liftPiece_compl
#print axioms MeynTweedie.PseudoAtoms.isCycle_liftClass
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_6_aperiodic
#print axioms MeynTweedie.PseudoAtoms.fwdRecMeas
#print axioms MeynTweedie.PseudoAtoms.fwdRecKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_fwdRecKernel
#print axioms MeynTweedie.PseudoAtoms.fwdRec_pow_le
#print axioms MeynTweedie.PseudoAtoms.fwdRec_pow_self
#print axioms MeynTweedie.PseudoAtoms.fwdRec_pow_ge
#print axioms MeynTweedie.PseudoAtoms.fwdRec_pow_succ_zero
#print axioms MeynTweedie.PseudoAtoms.fwdRec_return_pos
#print axioms MeynTweedie.PseudoAtoms.fwdRec_return_decomp
#print axioms MeynTweedie.PseudoAtoms.periodAt_fwdRec
#print axioms MeynTweedie.PseudoAtoms.controlMap
#print axioms MeynTweedie.PseudoAtoms.controlMap_zero
#print axioms MeynTweedie.PseudoAtoms.controlMap_succ
#print axioms MeynTweedie.PseudoAtoms.controlMap_one
#print axioms MeynTweedie.PseudoAtoms.controlMap_succ_cons
#print axioms MeynTweedie.PseudoAtoms.orbit
#print axioms MeynTweedie.PseudoAtoms.orbit_zero
#print axioms MeynTweedie.PseudoAtoms.orbit_succ
#print axioms MeynTweedie.PseudoAtoms.orbit_eq_controlMap
#print axioms MeynTweedie.PseudoAtoms.recursionKernel
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_apply
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_apply'
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_recursionKernel
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_comp_noise
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_const_noise
#print axioms MeynTweedie.PseudoAtoms.measurable_controlMap
#print axioms MeynTweedie.PseudoAtoms.measurable_controlMap_right
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_pow_apply'
#print axioms MeynTweedie.PseudoAtoms.infinitePi_map_shift
#print axioms MeynTweedie.PseudoAtoms.law_orbit
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_eq_lintegral_indicator
#print axioms MeynTweedie.PseudoAtoms.kfun_recursionKernel
#print axioms MeynTweedie.PseudoAtoms.kfunR_recursionKernel
#print axioms MeynTweedie.PseudoAtoms.eq_3_44
#print axioms MeynTweedie.PseudoAtoms.recursionKernel_pow_succ_apply
#print axioms MeynTweedie.PseudoAtoms.histMap
#print axioms MeynTweedie.PseudoAtoms.measurable_histMap
#print axioms MeynTweedie.PseudoAtoms.canonPath
#print axioms MeynTweedie.PseudoAtoms.canonPath_zero
#print axioms MeynTweedie.PseudoAtoms.canonPath_succ
#print axioms MeynTweedie.PseudoAtoms.measurable_canonPath
#print axioms MeynTweedie.PseudoAtoms.histFilt
#print axioms MeynTweedie.PseudoAtoms.infinitePi_map_fin
#print axioms MeynTweedie.PseudoAtoms.pi_map_init_last
#print axioms MeynTweedie.PseudoAtoms.law_hist_next
#print axioms MeynTweedie.PseudoAtoms.canon_step
#print axioms MeynTweedie.PseudoAtoms.isMarkovChain_canonPath
#print axioms MeynTweedie.PseudoAtoms.recursion_eq_controlMap
#print axioms MeynTweedie.PseudoAtoms.isMarkovChain_of_recursion
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise.mk
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise.measurable
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise.law
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise.iIndep
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise.indep
#print axioms MeynTweedie.PseudoAtoms.IsIIDNoise.map_eq
#print axioms MeynTweedie.PseudoAtoms.isMarkovChain_of_iid
#print axioms MeynTweedie.PseudoAtoms.IsMarkovChain.map_eq
#print axioms MeynTweedie.PseudoAtoms.truncSeq
#print axioms MeynTweedie.PseudoAtoms.tailSeq
#print axioms MeynTweedie.PseudoAtoms.measurable_truncSeq
#print axioms MeynTweedie.PseudoAtoms.measurable_tailSeq
#print axioms MeynTweedie.PseudoAtoms.iIndep_coords
#print axioms MeynTweedie.PseudoAtoms.indepFun_truncSeq_tailSeq
#print axioms MeynTweedie.PseudoAtoms.infinitePi_map_tailSeq
#print axioms MeynTweedie.PseudoAtoms.infinitePi_map_trunc_tail
#print axioms MeynTweedie.PseudoAtoms.lintegral_cond_eq
#print axioms MeynTweedie.PseudoAtoms.measurable_lintegral_cond
#print axioms MeynTweedie.PseudoAtoms.mul_lintegral_cond
#print axioms MeynTweedie.PseudoAtoms.lintegral_regeneration
#print axioms MeynTweedie.PseudoAtoms.setLIntegral_preimage_eq
#print axioms MeynTweedie.PseudoAtoms.pastFilt
#print axioms MeynTweedie.PseudoAtoms.isMarkovChain_of_regeneration
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel
#print axioms MeynTweedie.PseudoAtoms.measurable_add_step
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel_apply
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel_apply'
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_randomWalkKernel
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel_real_apply_Iic
#print axioms MeynTweedie.PseudoAtoms.controlMap_add
#print axioms MeynTweedie.PseudoAtoms.orbit_randomWalk
#print axioms MeynTweedie.PseudoAtoms.convPow
#print axioms MeynTweedie.PseudoAtoms.measurable_sum_fin
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.IsSpreadOut
#print axioms MeynTweedie.PseudoAtoms.halfLineStep
#print axioms MeynTweedie.PseudoAtoms.measurable_halfLineStep
#print axioms MeynTweedie.PseudoAtoms.halfLineWalkKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_halfLineWalkKernel
#print axioms MeynTweedie.PseudoAtoms.halfLineWalkKernel_apply'
#print axioms MeynTweedie.PseudoAtoms.halfLineWalkKernel_apply_zero
#print axioms MeynTweedie.PseudoAtoms.halfLineWalkKernel_apply_Iic
#print axioms MeynTweedie.PseudoAtoms.halfLineWalkKernel_apply_Ioi
#print axioms MeynTweedie.PseudoAtoms.halfLineOrbit
#print axioms MeynTweedie.PseudoAtoms.partialSum
#print axioms MeynTweedie.PseudoAtoms.halfLineOrbit_succ_coe
#print axioms MeynTweedie.PseudoAtoms.halfLineOrbit_eq_of_nonneg
#print axioms MeynTweedie.PseudoAtoms.halfLineOrbit_succ_of_eq_zero
#print axioms MeynTweedie.PseudoAtoms.halfLineOrbit_eq_lindley
#print axioms MeynTweedie.PseudoAtoms.reflectStep
#print axioms MeynTweedie.PseudoAtoms.reflectedWalkKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_reflectedWalkKernel
#print axioms MeynTweedie.PseudoAtoms.reflectedWalkKernel_apply_pos
#print axioms MeynTweedie.PseudoAtoms.reflectedWalkKernel_apply_zero
#print axioms MeynTweedie.PseudoAtoms.not_down_of_eq_2_28
#print axioms MeynTweedie.PseudoAtoms.twoPointLaw
#print axioms MeynTweedie.PseudoAtoms.reflectedWalk_2_28_fails
#print axioms MeynTweedie.PseudoAtoms.birthDeathKernel
#print axioms MeynTweedie.PseudoAtoms.birthDeathKernel_apply
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_birthDeathKernel
#print axioms MeynTweedie.PseudoAtoms.birthDeathKernel_apply_succ
#print axioms MeynTweedie.PseudoAtoms.birthDeathKernel_apply_pred
#print axioms MeynTweedie.PseudoAtoms.lindleyStep
#print axioms MeynTweedie.PseudoAtoms.measurable_lindleyStep
#print axioms MeynTweedie.PseudoAtoms.waitingTimeKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_waitingTimeKernel
#print axioms MeynTweedie.PseudoAtoms.waitingTimeKernel_eq_halfLineWalk
#print axioms MeynTweedie.PseudoAtoms.giM1Step
#print axioms MeynTweedie.PseudoAtoms.giM1Kernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_giM1Kernel
#print axioms MeynTweedie.PseudoAtoms.giM1Kernel_apply'
#print axioms MeynTweedie.PseudoAtoms.giM1Kernel_apply_up
#print axioms MeynTweedie.PseudoAtoms.giM1Kernel_apply_le
#print axioms MeynTweedie.PseudoAtoms.giM1Kernel_apply_zero
#print axioms MeynTweedie.PseudoAtoms.giM1Kernel_not_2_28
#print axioms MeynTweedie.PseudoAtoms.mG1Step
#print axioms MeynTweedie.PseudoAtoms.mG1Kernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_mG1Kernel
#print axioms MeynTweedie.PseudoAtoms.mG1Kernel_apply
#print axioms MeynTweedie.PseudoAtoms.mG1Kernel_zero
#print axioms MeynTweedie.PseudoAtoms.expMeasure_Ioi
#print axioms MeynTweedie.PseudoAtoms.expMeasure_memoryless
#print axioms MeynTweedie.PseudoAtoms.expMeasure_prod_lt
#print axioms MeynTweedie.PseudoAtoms.dirac_not_memoryless
#print axioms MeynTweedie.PseudoAtoms.storageStep
#print axioms MeynTweedie.PseudoAtoms.measurable_storageStep
#print axioms MeynTweedie.PseudoAtoms.storageKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_storageKernel
#print axioms MeynTweedie.PseudoAtoms.storageKernel_eq_halfLineWalk
#print axioms MeynTweedie.PseudoAtoms.releaseLaw_Iic
#print axioms MeynTweedie.PseudoAtoms.storageKernel_one
#print axioms MeynTweedie.PseudoAtoms.storage_mean_increment
#print axioms MeynTweedie.PseudoAtoms.releaseTime
#print axioms MeynTweedie.PseudoAtoms.continuous_releaseTime
#print axioms MeynTweedie.PseudoAtoms.releaseTime_strictMono
#print axioms MeynTweedie.PseudoAtoms.releaseTime_strictMonoOn
#print axioms MeynTweedie.PseudoAtoms.releaseTime_bijOn
#print axioms MeynTweedie.PseudoAtoms.releaseTime_one_add_sq
#print axioms MeynTweedie.PseudoAtoms.releaseTime_not_surjective
#print axioms MeynTweedie.PseudoAtoms.inputKernel
#print axioms MeynTweedie.PseudoAtoms.inputKernel_apply
#print axioms MeynTweedie.PseudoAtoms.contentKernel
#print axioms MeynTweedie.PseudoAtoms.contentPreInputKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_contentKernel
#print axioms MeynTweedie.PseudoAtoms.contentRelease_Iic
#print axioms MeynTweedie.PseudoAtoms.contentKernel_apply'
#print axioms MeynTweedie.PseudoAtoms.contentKernel_ne_storageKernel
#print axioms MeynTweedie.PseudoAtoms.contentPreInputKernel_eq_storageKernel
#print axioms MeynTweedie.PseudoAtoms.renewalKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_renewalKernel
#print axioms MeynTweedie.PseudoAtoms.renewalKernel_apply_singleton
#print axioms MeynTweedie.PseudoAtoms.renewalKernel_apply_Ioi
#print axioms MeynTweedie.PseudoAtoms.le_renewal
#print axioms MeynTweedie.PseudoAtoms.seqConv
#print axioms MeynTweedie.PseudoAtoms.seqConv_eq_sum_range
#print axioms MeynTweedie.PseudoAtoms.seqConv_comm
#print axioms MeynTweedie.PseudoAtoms.seqConvPow
#print axioms MeynTweedie.PseudoAtoms.mk_coeff_eq
#print axioms MeynTweedie.PseudoAtoms.mk_seqConv
#print axioms MeynTweedie.PseudoAtoms.mk_seqConvPow
#print axioms MeynTweedie.PseudoAtoms.seqConvPow_succ
#print axioms MeynTweedie.PseudoAtoms.bind_renewalKernel_singleton
#print axioms MeynTweedie.PseudoAtoms.renewal_law
#print axioms MeynTweedie.PseudoAtoms.renewal_law_one
#print axioms MeynTweedie.PseudoAtoms.fwdStep
#print axioms MeynTweedie.PseudoAtoms.forwardKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_forwardKernel
#print axioms MeynTweedie.PseudoAtoms.forwardKernel_of_one_lt
#print axioms MeynTweedie.PseudoAtoms.forwardKernel_one
#print axioms MeynTweedie.PseudoAtoms.hazard
#print axioms MeynTweedie.PseudoAtoms.hazard_le_one
#print axioms MeynTweedie.PseudoAtoms.backwardKernel
#print axioms MeynTweedie.PseudoAtoms.backwardKernel_apply
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_backwardKernel
#print axioms MeynTweedie.PseudoAtoms.backwardKernel_apply_zero
#print axioms MeynTweedie.PseudoAtoms.backwardKernel_apply_succ
#print axioms MeynTweedie.PseudoAtoms.fwdTime
#print axioms MeynTweedie.PseudoAtoms.bwdTime
#print axioms MeynTweedie.PseudoAtoms.fwdTime_set_nonempty
#print axioms MeynTweedie.PseudoAtoms.one_le_fwdTime
#print axioms MeynTweedie.PseudoAtoms.fwdTime_succ_of_one_lt
#print axioms MeynTweedie.PseudoAtoms.fwdTime_succ_of_eq_one
#print axioms MeynTweedie.PseudoAtoms.bwdTime_set_empty
#print axioms MeynTweedie.PseudoAtoms.bwdTime_set_empty_example
#print axioms MeynTweedie.PseudoAtoms.bwdTime_succ_of_renewal
#print axioms MeynTweedie.PseudoAtoms.bwdTime_succ_of_not_renewal
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts
#print axioms MeynTweedie.PseudoAtoms.bwdTimeCts
#print axioms MeynTweedie.PseudoAtoms.fwdSkeleton
#print axioms MeynTweedie.PseudoAtoms.bwdSkeleton
#print axioms MeynTweedie.PseudoAtoms.linear_controlMap
#print axioms MeynTweedie.PseudoAtoms.orbit_linear
#print axioms MeynTweedie.PseudoAtoms.lssKernel
#print axioms MeynTweedie.PseudoAtoms.measurable_lssStep
#print axioms MeynTweedie.PseudoAtoms.lssKernel_apply'
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_lssKernel
#print axioms MeynTweedie.PseudoAtoms.clm_pow_apply
#print axioms MeynTweedie.PseudoAtoms.orbit_lss
#print axioms MeynTweedie.PseudoAtoms.lssKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.measurable_mulVec
#print axioms MeynTweedie.PseudoAtoms.lssMatrixKernel
#print axioms MeynTweedie.PseudoAtoms.measurable_lssMatrixStep
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_lssMatrixKernel
#print axioms MeynTweedie.PseudoAtoms.mulVecHom
#print axioms MeynTweedie.PseudoAtoms.coe_mulVecHom
#print axioms MeynTweedie.PseudoAtoms.matrix_pow_mulVec
#print axioms MeynTweedie.PseudoAtoms.orbit_lssMatrix
#print axioms MeynTweedie.PseudoAtoms.lssMatrixKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.lcmTrajectory
#print axioms MeynTweedie.PseudoAtoms.IsControllable
#print axioms MeynTweedie.PseudoAtoms.lcmTrajectory_eq
#print axioms MeynTweedie.PseudoAtoms.ar1Kernel
#print axioms MeynTweedie.PseudoAtoms.measurable_ar1Step
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_ar1Kernel
#print axioms MeynTweedie.PseudoAtoms.ar1Kernel_apply'
#print axioms MeynTweedie.PseudoAtoms.ar1Kernel_eq_lssKernel
#print axioms MeynTweedie.PseudoAtoms.ar1Kernel_one
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel_eq_lssKernel
#print axioms MeynTweedie.PseudoAtoms.orbit_ar1
#print axioms MeynTweedie.PseudoAtoms.shiftIn
#print axioms MeynTweedie.PseudoAtoms.shiftIn_apply_zero
#print axioms MeynTweedie.PseudoAtoms.shiftIn_apply_succ
#print axioms MeynTweedie.PseudoAtoms.measurable_shiftIn
#print axioms MeynTweedie.PseudoAtoms.shiftIn_add
#print axioms MeynTweedie.PseudoAtoms.arStep
#print axioms MeynTweedie.PseudoAtoms.measurable_arStep
#print axioms MeynTweedie.PseudoAtoms.arKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_arKernel
#print axioms MeynTweedie.PseudoAtoms.companion
#print axioms MeynTweedie.PseudoAtoms.firstUnit
#print axioms MeynTweedie.PseudoAtoms.arStep_eq_companion
#print axioms MeynTweedie.PseudoAtoms.arKernel_eq_lssMatrixKernel
#print axioms MeynTweedie.PseudoAtoms.arVec
#print axioms MeynTweedie.PseudoAtoms.arVec_succ
#print axioms MeynTweedie.PseudoAtoms.armaStep
#print axioms MeynTweedie.PseudoAtoms.measurable_armaStep
#print axioms MeynTweedie.PseudoAtoms.armaKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_armaKernel
#print axioms MeynTweedie.PseudoAtoms.arma_of_ar
#print axioms MeynTweedie.PseudoAtoms.fig11F
#print axioms MeynTweedie.PseudoAtoms.fig11F_eq
#print axioms MeynTweedie.PseudoAtoms.sqNorm2
#print axioms MeynTweedie.PseudoAtoms.fig11_sqNorm_mulVec
#print axioms MeynTweedie.PseudoAtoms.fig11_tendsto_zero
#print axioms MeynTweedie.PseudoAtoms.fig11_inv_tendsto_atTop
#print axioms MeynTweedie.PseudoAtoms.countEvent
#print axioms MeynTweedie.PseudoAtoms.measurableSet_countEvent
#print axioms MeynTweedie.PseudoAtoms.cons_mem_countEvent
#print axioms MeynTweedie.PseudoAtoms.pi_finSucc_eq_lintegral
#print axioms MeynTweedie.PseudoAtoms.poissonCount
#print axioms MeynTweedie.PseudoAtoms.measurable_poissonCount
#print axioms MeynTweedie.PseudoAtoms.poissonCount_of_nonneg
#print axioms MeynTweedie.PseudoAtoms.poissonCount_of_neg
#print axioms MeynTweedie.PseudoAtoms.lintegral_poissonCount
#print axioms MeynTweedie.PseudoAtoms.eq_3_18
#print axioms MeynTweedie.PseudoAtoms.eq_3_15
#print axioms MeynTweedie.PseudoAtoms.eq_3_18_counterexample
#print axioms MeynTweedie.PseudoAtoms.eq_3_14
#print axioms MeynTweedie.PseudoAtoms.eq_3_19
#print axioms MeynTweedie.PseudoAtoms.matKernel_rwMatrix
#print axioms MeynTweedie.PseudoAtoms.matKernel_rwhlMatrix
#print axioms MeynTweedie.PseudoAtoms.measure_Ici_succ_eq_tsum
#print axioms MeynTweedie.PseudoAtoms.matKernel_giM1Matrix
#print axioms MeynTweedie.PseudoAtoms.matKernel_mG1Matrix
#print axioms MeynTweedie.PseudoAtoms.matKernel_arMatrix
#print axioms MeynTweedie.PseudoAtoms.randomWalkInt_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.rwhl_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_1_of_recursion
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_2_of_recursion
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_1_derived
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_2_derived
#print axioms MeynTweedie.PseudoAtoms.proposition_3_3_3_of_recursion
#print axioms MeynTweedie.PseudoAtoms.ar1_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.lssMatrix_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.waitingTime_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.randomWalkReal_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.randomWalkKernel_apply_image
#print axioms MeynTweedie.PseudoAtoms.eq_3_35
#print axioms MeynTweedie.PseudoAtoms.eq_3_36
#print axioms MeynTweedie.PseudoAtoms.halfLineWalk_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.eq_3_37
#print axioms MeynTweedie.PseudoAtoms.eq_3_37_div
#print axioms MeynTweedie.PseudoAtoms.eq_3_37_counterexample
#print axioms MeynTweedie.PseudoAtoms.storage_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.renewalMeasure
#print axioms MeynTweedie.PseudoAtoms.isProbabilityMeasure_convPow
#print axioms MeynTweedie.PseudoAtoms.sFinite_renewalMeasure
#print axioms MeynTweedie.PseudoAtoms.conv_apply_eq_lintegral
#print axioms MeynTweedie.PseudoAtoms.image_sub_const_eq_setOf
#print axioms MeynTweedie.PseudoAtoms.eq_3_38
#print axioms MeynTweedie.PseudoAtoms.renewalReal_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.renewalReal_map_eq
#print axioms MeynTweedie.PseudoAtoms.renewal_expected_count
#print axioms MeynTweedie.PseudoAtoms.renewal_expected_count_undelayed
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts_set_eq
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts_add_of_lt
#print axioms MeynTweedie.PseudoAtoms.fwdSkeleton_succ_of_lt
#print axioms MeynTweedie.PseudoAtoms.bwdTimeCts_add_of_no_renewal
#print axioms MeynTweedie.PseudoAtoms.pi_dirac_const
#print axioms MeynTweedie.PseudoAtoms.convPow_dirac
#print axioms MeynTweedie.PseudoAtoms.setLIntegral_renewalMeasure_dirac_one
#print axioms MeynTweedie.PseudoAtoms.eq_3_39_printed
#print axioms MeynTweedie.PseudoAtoms.eq_3_39_corrected
#print axioms MeynTweedie.PseudoAtoms.eq_3_39_counterexample
#print axioms MeynTweedie.PseudoAtoms.ladderRow
#print axioms MeynTweedie.PseudoAtoms.ladderChainKernel
#print axioms MeynTweedie.PseudoAtoms.ladderChainKernel_apply
#print axioms MeynTweedie.PseudoAtoms.map_prodMk_apply_prod
#print axioms MeynTweedie.PseudoAtoms.ladderRow_apply_prod
#print axioms MeynTweedie.PseudoAtoms.eq_3_40_zero
#print axioms MeynTweedie.PseudoAtoms.eq_3_40_mid
#print axioms MeynTweedie.PseudoAtoms.eq_3_40_up
#print axioms MeynTweedie.PseudoAtoms.ladderChainKernel_translate
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_ladderChainKernel
#print axioms MeynTweedie.PseudoAtoms.resEpoch
#print axioms MeynTweedie.PseudoAtoms.measurable_resEpoch
#print axioms MeynTweedie.PseudoAtoms.gig1Set
#print axioms MeynTweedie.PseudoAtoms.measurableSet_gig1Set
#print axioms MeynTweedie.PseudoAtoms.ladderP
#print axioms MeynTweedie.PseudoAtoms.gig1LambdaMeasure
#print axioms MeynTweedie.PseudoAtoms.gig1LambdaMeasure_apply
#print axioms MeynTweedie.PseudoAtoms.gig1Lambda
#print axioms MeynTweedie.PseudoAtoms.eq_3_42
#print axioms MeynTweedie.PseudoAtoms.gig1LambdaStar
#print axioms MeynTweedie.PseudoAtoms.eq_3_43
#print axioms MeynTweedie.PseudoAtoms.gig1Ladder
#print axioms MeynTweedie.PseudoAtoms.ennreal_sum_add_tsum_nat_add
#print axioms MeynTweedie.PseudoAtoms.gig1Ladder_rowSum
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_gig1Ladder
#print axioms MeynTweedie.PseudoAtoms.clamp01
#print axioms MeynTweedie.PseudoAtoms.continuous_clamp01
#print axioms MeynTweedie.PseudoAtoms.clamp01_le
#print axioms MeynTweedie.PseudoAtoms.clamp01_nonneg
#print axioms MeynTweedie.PseudoAtoms.norm_clamp01_le
#print axioms MeynTweedie.PseudoAtoms.tendsto_partialSum_atTop_ae
#print axioms MeynTweedie.PseudoAtoms.resEpoch_mono
#print axioms MeynTweedie.PseudoAtoms.tsum_indicator_resEpoch_eq_one
#print axioms MeynTweedie.PseudoAtoms.gig1Lambda_tsum_univ
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_gig1Ladder_of_pos
#print axioms MeynTweedie.PseudoAtoms.natSInf_eq_iff
#print axioms MeynTweedie.PseudoAtoms.measurableSet_natSInf_eq
#print axioms MeynTweedie.PseudoAtoms.measurable_fwdTimeCts
#print axioms MeynTweedie.PseudoAtoms.resEpoch_succ_eq
#print axioms MeynTweedie.PseudoAtoms.resEpoch_truncSeq_of_le
#print axioms MeynTweedie.PseudoAtoms.resEpoch_truncSeq_of_ge
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts_truncSeq
#print axioms MeynTweedie.PseudoAtoms.fwdSkelStep
#print axioms MeynTweedie.PseudoAtoms.measurable_fwdSkelStep
#print axioms MeynTweedie.PseudoAtoms.fwdSkelKernel
#print axioms MeynTweedie.PseudoAtoms.fwdSkel
#print axioms MeynTweedie.PseudoAtoms.measurable_fwdSkel
#print axioms MeynTweedie.PseudoAtoms.fwdIndex
#print axioms MeynTweedie.PseudoAtoms.measurableSet_fwdIndex_eq
#print axioms MeynTweedie.PseudoAtoms.exists_resEpoch_gt
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts_eq_resEpoch
#print axioms MeynTweedie.PseudoAtoms.fwdSkel_succ
#print axioms MeynTweedie.PseudoAtoms.prod_map_trunc_tail
#print axioms MeynTweedie.PseudoAtoms.ae_good_prod
#print axioms MeynTweedie.PseudoAtoms.fwdSkeleton_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.infinitePi_map_partialSum_next
#print axioms MeynTweedie.PseudoAtoms.fwdSkelKernel_of_lt
#print axioms MeynTweedie.PseudoAtoms.indicator_fwdTimeCts_eq_tsum
#print axioms MeynTweedie.PseudoAtoms.convPow_Iio_zero
#print axioms MeynTweedie.PseudoAtoms.lintegral_partialSum_pair
#print axioms MeynTweedie.PseudoAtoms.eq_3_39
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts_zero_of_pos
#print axioms MeynTweedie.PseudoAtoms.fwdSkeleton_isMarkovChain_delayed
#print axioms MeynTweedie.PseudoAtoms.fwdSkeleton_isMarkovChain_undelayed
#print axioms MeynTweedie.PseudoAtoms.measurable_bwdTimeCts
#print axioms MeynTweedie.PseudoAtoms.bwdTimeCts_truncSeq
#print axioms MeynTweedie.PseudoAtoms.bwdTimeCts_eq_resEpoch
#print axioms MeynTweedie.PseudoAtoms.bwdTimeCts_truncSeq_of_le
#print axioms MeynTweedie.PseudoAtoms.bwdSkelStep
#print axioms MeynTweedie.PseudoAtoms.measurable_bwdSkelStep
#print axioms MeynTweedie.PseudoAtoms.bwdSkel
#print axioms MeynTweedie.PseudoAtoms.measurable_bwdSkel
#print axioms MeynTweedie.PseudoAtoms.bwdIndex
#print axioms MeynTweedie.PseudoAtoms.measurableSet_bwdIndex_eq
#print axioms MeynTweedie.PseudoAtoms.bwdIndex_spec
#print axioms MeynTweedie.PseudoAtoms.bwdSkel_eq
#print axioms MeynTweedie.PseudoAtoms.bwdSkel_succ
#print axioms MeynTweedie.PseudoAtoms.bwdSkelKernel
#print axioms MeynTweedie.PseudoAtoms.bwdSkel_zero_ae
#print axioms MeynTweedie.PseudoAtoms.bwdSkeleton_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.bwdTimeCts_first
#print axioms MeynTweedie.PseudoAtoms.bwdSkelStep_of_gt
#print axioms MeynTweedie.PseudoAtoms.bwdSkelStep_lt
#print axioms MeynTweedie.PseudoAtoms.bwdSkelStep_split
#print axioms MeynTweedie.PseudoAtoms.infinitePi_measure_head
#print axioms MeynTweedie.PseudoAtoms.bwdSkelKernel_apply_add
#print axioms MeynTweedie.PseudoAtoms.bwdInner
#print axioms MeynTweedie.PseudoAtoms.indicator_bwdTimeCts_eq_tsum
#print axioms MeynTweedie.PseudoAtoms.lintegral_partialSum_pair_bwd
#print axioms MeynTweedie.PseudoAtoms.bwd_inner
#print axioms MeynTweedie.PseudoAtoms.infinitePi_map_head_tail
#print axioms MeynTweedie.PseudoAtoms.bwdSkelKernel_apply_of_subset
#print axioms MeynTweedie.PseudoAtoms.halfOneTwo
#print axioms MeynTweedie.PseudoAtoms.halfOneTwo_apply
#print axioms MeynTweedie.PseudoAtoms.isProbabilityMeasure_halfOneTwo
#print axioms MeynTweedie.PseudoAtoms.lintegral_halfOneTwo
#print axioms MeynTweedie.PseudoAtoms.convPow_eq_map
#print axioms MeynTweedie.PseudoAtoms.bwd_display_counterexample
#print axioms MeynTweedie.PseudoAtoms.map_prod_prod_rearrange
#print axioms MeynTweedie.PseudoAtoms.arrT
#print axioms MeynTweedie.PseudoAtoms.depT
#print axioms MeynTweedie.PseudoAtoms.inService
#print axioms MeynTweedie.PseudoAtoms.queueN
#print axioms MeynTweedie.PseudoAtoms.queueR
#print axioms MeynTweedie.PseudoAtoms.arrT_succ
#print axioms MeynTweedie.PseudoAtoms.arrT_mono
#print axioms MeynTweedie.PseudoAtoms.arrT_lt_depT
#print axioms MeynTweedie.PseudoAtoms.depT_lt_succ
#print axioms MeynTweedie.PseudoAtoms.depT_mono
#print axioms MeynTweedie.PseudoAtoms.inService_spec
#print axioms MeynTweedie.PseudoAtoms.queueN_eq
#print axioms MeynTweedie.PseudoAtoms.inService_mono
#print axioms MeynTweedie.PseudoAtoms.depT_chain
#print axioms MeynTweedie.PseudoAtoms.numDone
#print axioms MeynTweedie.PseudoAtoms.gig1Step
#print axioms MeynTweedie.PseudoAtoms.gig1_step_eq
#print axioms MeynTweedie.PseudoAtoms.measurable_comp_index
#print axioms MeynTweedie.PseudoAtoms.measurable_arrT
#print axioms MeynTweedie.PseudoAtoms.measurable_depT
#print axioms MeynTweedie.PseudoAtoms.measurableSet_inService_eq
#print axioms MeynTweedie.PseudoAtoms.measurable_inService
#print axioms MeynTweedie.PseudoAtoms.measurable_queueN
#print axioms MeynTweedie.PseudoAtoms.measurable_queueR
#print axioms MeynTweedie.PseudoAtoms.measurable_numDone
#print axioms MeynTweedie.PseudoAtoms.measurable_gig1Step
#print axioms MeynTweedie.PseudoAtoms.arrT_truncSeq
#print axioms MeynTweedie.PseudoAtoms.depT_truncSeq
#print axioms MeynTweedie.PseudoAtoms.inService_truncSeq
#print axioms MeynTweedie.PseudoAtoms.inService_eq_iff_truncSeq
#print axioms MeynTweedie.PseudoAtoms.measure_ext_nat_prod
#print axioms MeynTweedie.PseudoAtoms.gig1Step0
#print axioms MeynTweedie.PseudoAtoms.numDone_le_of_lt
#print axioms MeynTweedie.PseudoAtoms.numDone_eq_iff
#print axioms MeynTweedie.PseudoAtoms.tsum_indicator_tail_eq
#print axioms MeynTweedie.PseudoAtoms.measurable_gig1Step0
#print axioms MeynTweedie.PseudoAtoms.gig1Step0_fst_le
#print axioms MeynTweedie.PseudoAtoms.gig1Step0_mem_zero_iff
#print axioms MeynTweedie.PseudoAtoms.gig1Step0_mem_iff
#print axioms MeynTweedie.PseudoAtoms.ae_good_gig1
#print axioms MeynTweedie.PseudoAtoms.gig1Ladder_eq_map
#print axioms MeynTweedie.PseudoAtoms.gig1_law_past_future
#print axioms MeynTweedie.PseudoAtoms.ae_good_queue
#print axioms MeynTweedie.PseudoAtoms.gig1_isMarkovChain
#print axioms MeynTweedie.PseudoAtoms.gig1Lambda_zero_univ
#print axioms MeynTweedie.PseudoAtoms.gig1Lambda_tail_univ
#print axioms MeynTweedie.PseudoAtoms.gig1Ladder_bottom
#print axioms MeynTweedie.PseudoAtoms.proposition_5_3_2_gig1
#print axioms MeynTweedie.PseudoAtoms.proposition_5_3_2_queue
#print axioms MeynTweedie.PseudoAtoms.gig1Lambda_zero_counterexample
#print axioms MeynTweedie.PseudoAtoms.gig1Ladder_bottom_counterexample
#print axioms MeynTweedie.PseudoAtoms.ctrbMap
#print axioms MeynTweedie.PseudoAtoms.ctrbMap_apply
#print axioms MeynTweedie.PseudoAtoms.ctrbMatrix
#print axioms MeynTweedie.PseudoAtoms.ctrbMatrix_mulVec
#print axioms MeynTweedie.PseudoAtoms.range_ctrbMatrix
#print axioms MeynTweedie.PseudoAtoms.rank_ctrbMatrix_eq_iff
#print axioms MeynTweedie.PseudoAtoms.lcmTrajectory_eq_ctrbMap
#print axioms MeynTweedie.PseudoAtoms.IsCtrbRank
#print axioms MeynTweedie.PseudoAtoms.reach_of_range_eq_top
#print axioms MeynTweedie.PseudoAtoms.proposition_4_4_1
#print axioms MeynTweedie.PseudoAtoms.pow_mul_mulVec_mem_range
#print axioms MeynTweedie.PseudoAtoms.pow_dim_eq_sum
#print axioms MeynTweedie.PseudoAtoms.pow_mul_mulVec_mem_range_n
#print axioms MeynTweedie.PseudoAtoms.range_ctrbMap_le_n
#print axioms MeynTweedie.PseudoAtoms.range_ctrbMap_mono
#print axioms MeynTweedie.PseudoAtoms.isControllable_iff_rank
#print axioms MeynTweedie.PseudoAtoms.isControllable_iff_exists_rank
#print axioms MeynTweedie.PseudoAtoms.range_ctrbMap_eq_top
#print axioms MeynTweedie.PseudoAtoms.firstUnit_mulVec
#print axioms MeynTweedie.PseudoAtoms.companion_mulVec_of_ne_zero
#print axioms MeynTweedie.PseudoAtoms.companion_mulVec_zero
#print axioms MeynTweedie.PseudoAtoms.firstVec
#print axioms MeynTweedie.PseudoAtoms.companion_pow_firstUnit_triangular
#print axioms MeynTweedie.PseudoAtoms.companionEta
#print axioms MeynTweedie.PseudoAtoms.companion_eta_rec
#print axioms MeynTweedie.PseudoAtoms.proposition_4_4_2
#print axioms MeynTweedie.PseudoAtoms.gramian
#print axioms MeynTweedie.PseudoAtoms.gramian_eq
#print axioms MeynTweedie.PseudoAtoms.rank_gramian
#print axioms MeynTweedie.PseudoAtoms.isControllable_iff_gramian
#print axioms MeynTweedie.PseudoAtoms.ctrbSubspace_absorbing_step
#print axioms MeynTweedie.PseudoAtoms.gramian_series_counterexample
#print axioms MeynTweedie.PseudoAtoms.pi_absolutelyContinuous
#print axioms MeynTweedie.PseudoAtoms.measurable_ctrbMap
#print axioms MeynTweedie.PseudoAtoms.ctrbLaw
#print axioms MeynTweedie.PseudoAtoms.lss_pow_eq
#print axioms MeynTweedie.PseudoAtoms.ctrbLaw_equiv
#print axioms MeynTweedie.PseudoAtoms.lss_pow_equiv
#print axioms MeynTweedie.PseudoAtoms.lss_isPhiIrreducible
#print axioms MeynTweedie.PseudoAtoms.lss_isMaximalIrreducibility
#print axioms MeynTweedie.PseudoAtoms.translateCM
#print axioms MeynTweedie.PseudoAtoms.lss_lowerSemicontinuous
#print axioms MeynTweedie.PseudoAtoms.lss_unifAccessible
#print axioms MeynTweedie.PseudoAtoms.proposition_4_4_3
#print axioms MeynTweedie.PseudoAtoms.stdGaussian_equiv_volume
#print axioms MeynTweedie.PseudoAtoms.proposition_4_4_3_gaussian
#print axioms MeynTweedie.PseudoAtoms.ctrbSubspace_isAbsorbing
#print axioms MeynTweedie.PseudoAtoms.density_4_18_counterexample
#print axioms MeynTweedie.PseudoAtoms.exists_pow_pos_of_reach
#print axioms MeynTweedie.PseudoAtoms.not_isPhiIrreducible_of_disjoint_absorbing
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_of_skeleton
#print axioms MeynTweedie.PseudoAtoms.halfLine_pow_zero_ge
#print axioms MeynTweedie.PseudoAtoms.exists_Iio_neg_pos
#print axioms MeynTweedie.PseudoAtoms.halfLine_hitProb_zero_eq_zero
#print axioms MeynTweedie.PseudoAtoms.proposition_4_3_1
#print axioms MeynTweedie.PseudoAtoms.proposition_4_3_1_compact
#print axioms MeynTweedie.PseudoAtoms.halfLine_maximal
#print axioms MeynTweedie.PseudoAtoms.isPhiIrreducible_of_local_density
#print axioms MeynTweedie.PseudoAtoms.le_of_density
#print axioms MeynTweedie.PseudoAtoms.ar1_isPhiIrreducible_of_density
#print axioms MeynTweedie.PseudoAtoms.randomWalk_isPhiIrreducible_of_density
#print axioms MeynTweedie.PseudoAtoms.randomWalk_isPhiIrreducible_Icc
#print axioms MeynTweedie.PseudoAtoms.randomWalk_step_ge
#print axioms MeynTweedie.PseudoAtoms.randomWalk_isPhiIrreducible_of_convPow
#print axioms MeynTweedie.PseudoAtoms.ratCoset
#print axioms MeynTweedie.PseudoAtoms.randomWalk_rational
#print axioms MeynTweedie.PseudoAtoms.ar1_uniform_isPhiIrreducible
#print axioms MeynTweedie.PseudoAtoms.ar1_abs_lt_step
#print axioms MeynTweedie.PseudoAtoms.ar1_explosive_not_irreducible
#print axioms MeynTweedie.PseudoAtoms.isAccessibleAtom_singleton_countable
#print axioms MeynTweedie.PseudoAtoms.halfLine_isAccessibleAtom_zero
#print axioms MeynTweedie.PseudoAtoms.map_add_left_inj
#print axioms MeynTweedie.PseudoAtoms.randomWalk_not_isAccessibleAtom
#print axioms MeynTweedie.PseudoAtoms.halfLine_isSmallSet_Iic
#print axioms MeynTweedie.PseudoAtoms.halfLine_isSmall_of_isCompact
#print axioms MeynTweedie.PseudoAtoms.randomWalk_isSmallSet_Icc
#print axioms MeynTweedie.PseudoAtoms.ar1_isSmallSet_of_density
#print axioms MeynTweedie.PseudoAtoms.gaussianReal_density_ge
#print axioms MeynTweedie.PseudoAtoms.ar1_gaussian_isSmall_of_isCompact
#print axioms MeynTweedie.PseudoAtoms.proposition_5_3_2
#print axioms MeynTweedie.PseudoAtoms.exists_preimage_ge_of_surjective
#print axioms MeynTweedie.PseudoAtoms.pi_fin_mono
#print axioms MeynTweedie.PseudoAtoms.pi_smul_restrict
#print axioms MeynTweedie.PseudoAtoms.gaussianReal_ge_restrict
#print axioms MeynTweedie.PseudoAtoms.gaussianPi_ge_restrict
#print axioms MeynTweedie.PseudoAtoms.pi_ge_restrict
#print axioms MeynTweedie.PseudoAtoms.lss_isSmallSet_of_isCompact
#print axioms MeynTweedie.PseudoAtoms.lss_gaussian_isSmallSet_of_isCompact
#print axioms MeynTweedie.PseudoAtoms.lss_gaussian_isSmall_of_isCompact
#print axioms MeynTweedie.PseudoAtoms.IsSamplingDist
#print axioms MeynTweedie.PseudoAtoms.diracDist
#print axioms MeynTweedie.PseudoAtoms.isSamplingDist_diracDist
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_diracDist
#print axioms MeynTweedie.PseudoAtoms.geomDist
#print axioms MeynTweedie.PseudoAtoms.isSamplingDist_geomDist
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_geomDist
#print axioms MeynTweedie.PseudoAtoms.uniformDist
#print axioms MeynTweedie.PseudoAtoms.uniformDist_eq_indicator
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_uniformDist_apply
#print axioms MeynTweedie.PseudoAtoms.isSamplingDist_uniformDist
#print axioms MeynTweedie.PseudoAtoms.tsum_mul_uniformDist_ne_top
#print axioms MeynTweedie.PseudoAtoms.mixDist
#print axioms MeynTweedie.PseudoAtoms.isSamplingDist_mixDist
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_mixDist_apply
#print axioms MeynTweedie.PseudoAtoms.sampleConv
#print axioms MeynTweedie.PseudoAtoms.tsum_sum_antidiagonal
#print axioms MeynTweedie.PseudoAtoms.isSamplingDist_sampleConv
#print axioms MeynTweedie.PseudoAtoms.lemma_5_5_2_i
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_sampleConv
#print axioms MeynTweedie.PseudoAtoms.SampledAccessible
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_le_hitProb
#print axioms MeynTweedie.PseudoAtoms.lemma_5_5_1
#print axioms MeynTweedie.PseudoAtoms.lemma_5_5_1_firstHit
#print axioms MeynTweedie.PseudoAtoms.toTrueKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_toTrueKernel
#print axioms MeynTweedie.PseudoAtoms.lemma_5_5_1_counterexample
#print axioms MeynTweedie.PseudoAtoms.lemma_5_5_2_ii
#print axioms MeynTweedie.PseudoAtoms.lemma_5_5_2_iii
#print axioms MeynTweedie.PseudoAtoms.IsPetiteSet
#print axioms MeynTweedie.PseudoAtoms.IsPetite
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_3
#print axioms MeynTweedie.PseudoAtoms.smul_le_comp_of_le_on
#print axioms MeynTweedie.PseudoAtoms.lintegral_pos_of_pos
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_4_i
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_4_ii
#print axioms MeynTweedie.PseudoAtoms.sampledKernel_geomDist_half
#print axioms MeynTweedie.PseudoAtoms.isSamplingDist_geomDist_half
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_5_i
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_5_ii
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_5_iii
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_5_iii_cover
#print axioms MeynTweedie.PseudoAtoms.exists_tail_le
#print axioms MeynTweedie.PseudoAtoms.le_sum_head
#print axioms MeynTweedie.PseudoAtoms.half_min_spec
#print axioms MeynTweedie.PseudoAtoms.exists_sum_Icc_pow_ge
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_6_i
#print axioms MeynTweedie.PseudoAtoms.theorem_5_5_7
#print axioms MeynTweedie.PseudoAtoms.exists_lebesgue_minorant
#print axioms MeynTweedie.PseudoAtoms.selfConv
#print axioms MeynTweedie.PseudoAtoms.selfConv_eq_lintegral
#print axioms MeynTweedie.PseudoAtoms.lintegral_selfConv
#print axioms MeynTweedie.PseudoAtoms.eventually_lt_selfConv
#print axioms MeynTweedie.PseudoAtoms.randomWalk_pow_two_mul_ge
#print axioms MeynTweedie.PseudoAtoms.proposition_5_3_1
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_fwdSkelKernel
#print axioms MeynTweedie.PseudoAtoms.fwdSkelKernel_pow_apply
#print axioms MeynTweedie.PseudoAtoms.fwdTimeCts_eq_of_window
#print axioms MeynTweedie.PseudoAtoms.exists_convPow_minorant
#print axioms MeynTweedie.PseudoAtoms.fwdSkel_pow_ge
#print axioms MeynTweedie.PseudoAtoms.proposition_5_3_3
#print axioms MeynTweedie.PseudoAtoms.proposition_5_4_7
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_comp_sampledKernel
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_dirac_of_notMem
#print axioms MeynTweedie.PseudoAtoms.Minorization.sampledKernel_split_false_of_notMem
#print axioms MeynTweedie.PseudoAtoms.Minorization.split_ne_zero
#print axioms MeynTweedie.PseudoAtoms.Minorization.proposition_5_5_6_ii_average
#print axioms MeynTweedie.PseudoAtoms.Minorization.proposition_5_5_6_ii
#print axioms MeynTweedie.PseudoAtoms.ladderMeas
#print axioms MeynTweedie.PseudoAtoms.ladderKernel
#print axioms MeynTweedie.PseudoAtoms.isMarkovKernel_ladderKernel
#print axioms MeynTweedie.PseudoAtoms.ladderMinorization
#print axioms MeynTweedie.PseudoAtoms.ladder_isStronglyAperiodic
#print axioms MeynTweedie.PseudoAtoms.ladder_resid_even
#print axioms MeynTweedie.PseudoAtoms.ladder_split_dirac_odd
#print axioms MeynTweedie.PseudoAtoms.ladder_splitKernel_even
#print axioms MeynTweedie.PseudoAtoms.ladder_splitKernel_odd
#print axioms MeynTweedie.PseudoAtoms.ladder_splitKernel_pow
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_6_ii_counterexample
#print axioms MeynTweedie.PseudoAtoms.ladderKernel_odd
#print axioms MeynTweedie.PseudoAtoms.ladderKernel_even_zero
#print axioms MeynTweedie.PseudoAtoms.ladder_pow_odd
#print axioms MeynTweedie.PseudoAtoms.ladder_reaches_zero
#print axioms MeynTweedie.PseudoAtoms.ladder_isPhiIrreducible_dirac
#print axioms MeynTweedie.PseudoAtoms.ladder_isAbsorbing_zero_one
#print axioms MeynTweedie.PseudoAtoms.ladder_reaches_one
#print axioms MeynTweedie.PseudoAtoms.ladder_isMaximalIrreducibility
#print axioms MeynTweedie.PseudoAtoms.proposition_5_5_6_ii_counterexample_irreducible
#print axioms MeynTweedie.PseudoAtoms.IsCountableStateSpace
#print axioms MeynTweedie.PseudoAtoms.IsGeneralStateSpace
#print axioms MeynTweedie.PseudoAtoms.IsTopologicalStateSpace
#print axioms MeynTweedie.PseudoAtoms.IsCountableStateSpace.isGeneral
#print axioms MeynTweedie.PseudoAtoms.IsTopologicalStateSpace.isGeneral
