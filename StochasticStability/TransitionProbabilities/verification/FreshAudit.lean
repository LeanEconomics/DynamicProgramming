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
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Poisson.Basic
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
import Mathlib.Probability.Process.HittingTime
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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Random recursions as transition kernels

Copied from the `MarkovModels` project (`MarkovModels/Recursion.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition kernels of random recursions (MT §3.5.5)

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Regeneration at random indices

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

**See also.** The derivations that these matrices are the laws of the chains built from i.i.d.
noise (random walk, GI/M/1, M/G/1, AR(1)) are in `SpecificKernels`
(`randomWalkInt_isMarkovChain`, `proposition_3_3_1_derived`, `proposition_3_3_2_derived`,
`proposition_3_3_3_of_recursion`); the Poisson counts (3.14)–(3.18) are in `PoissonCounts`.
-/

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Random walks

Copied from the `MarkovModels` project (`MarkovModels/RandomWalk.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Countable-space models

Copied from the `MarkovModels` project (`MarkovModels/CountableModels.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GI/G/1, GI/M/1 and M/G/1 queues

Copied from the `MarkovModels` project (`MarkovModels/Queues.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Storage models

Copied from the `MarkovModels` project (`MarkovModels/Storage.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Renewal processes and recurrence time chains

Copied from the `MarkovModels` project (`MarkovModels/Renewal.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear models

Copied from the `MarkovModels` project (`MarkovModels/LinearModels.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Poisson counts of exponential services (MT (3.14)–(3.19))

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Kernels of the specific models (MT §§3.3 and 3.5.1–3.5.3)

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ladder chains and the GI/G/1 queue (MT §3.5.4)

Meyn and Tweedie, §3.5.4, pp. 70–71.

* `ladderKernel Λ Λ*`: the ladder chain (3.40) on `ℤ₊ × ℝ`, with row `i` putting `Λ*ᵢ(x, ·)` on
  rung `0` and `Λ_{i−j+1}(x, ·)` on rungs `j = 1, …, i + 1`: `eq_3_40_zero`, `eq_3_40_mid`,
  `eq_3_40_up`. It is translation invariant above rung `0` and skip-free to the right
  (`ladderKernel_translate`, the matrix display of p. 71), and it is a Markov kernel when every
  row has mass one (`isMarkovKernel_ladderKernel`).
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

namespace MeynTweedie.TransitionProbabilities

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- Row `i` of the ladder chain (3.40): mass `Λ*ᵢ(x, ·)` on rung `0` and `Λ_{i+1−j}(x, ·)` on
rung `j = 1, …, i + 1` (written with `k = i + 1 − j ∈ {0, …, i}`). -/
noncomputable def ladderRow (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) : Kernel ℝ (ℕ × ℝ) :=
  (Λs i).map (Prod.mk 0) + Kernel.sum fun k : Fin (i + 1) => (Λ k).map (Prod.mk (i + 1 - k))

/-- The ladder chain on `ℤ₊ × ℝ` (MT (3.40), p. 70) built from substochastic kernels
`Λₖ`, `Λ*ᵢ` on `ℝ`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)` for `1 ≤ j ≤ i + 1`,
`P(i, x; 0 × A) = Λ*ᵢ(x, A)` and `0` above rung `i + 1`. -/
noncomputable def ladderKernel (Λ Λs : ℕ → Kernel ℝ ℝ) : Kernel (ℕ × ℝ) (ℕ × ℝ) where
  toFun p := ladderRow Λ Λs p.1 p.2
  measurable' := measurable_from_prod_countable_right fun i => (ladderRow Λ Λs i).measurable

/-- The ladder kernel at `(i, x)` is row `i` at `x`. -/
theorem ladderKernel_apply (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) :
    ladderKernel Λ Λs (i, x) = ladderRow Λ Λs i x := rfl

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
    (hA : MeasurableSet A) : ladderKernel Λ Λs (i, x) ({0} ×ˢ A) = Λs i x A := by
  rw [ladderKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [ite_true]
  rw [Finset.sum_eq_zero fun k _ => ?_, add_zero]
  have : (k : ℕ) ≤ i := Nat.lt_succ_iff.1 k.2
  simp only [ite_eq_right_iff]
  intro h
  omega

/-- (3.40), rungs `1, …, i + 1`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)`. -/
theorem eq_3_40_mid (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i + 1) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderKernel Λ Λs (i, x) ({j} ×ˢ A) = Λ (i + 1 - j) x A := by
  rw [ladderKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
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
    {A : Set ℝ} (hA : MeasurableSet A) : ladderKernel Λ Λs (i, x) ({j} ×ˢ A) = 0 := by
  rw [ladderKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [show j ≠ 0 by omega, ite_false, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [ite_eq_right_iff]
  intro h
  omega

/-- Translation invariance away from rung `0` (MT p. 71): `P(i + 1, x; (j + 1) × A) =
P(i, x; j × A)` for `j ≥ 1`, as in the matrix display of p. 71. -/
theorem ladderKernel_translate (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hj : 1 ≤ j) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderKernel Λ Λs (i + 1, x) ({j + 1} ×ˢ A) = ladderKernel Λ Λs (i, x) ({j} ×ˢ A) := by
  by_cases hji : j ≤ i + 1
  · rw [eq_3_40_mid Λ Λs (by omega) (by omega) x hA, eq_3_40_mid Λ Λs hj hji x hA]
    rw [show i + 1 + 1 - (j + 1) = i + 1 - j by omega]
  · rw [eq_3_40_up Λ Λs (by omega) x hA, eq_3_40_up Λ Λs (by omega) x hA]

/-- The ladder chain is a Markov kernel when each row has total mass one,
`Λ*ᵢ(x, ℝ) + Σ_{k ≤ i} Λₖ(x, ℝ) = 1`. -/
theorem isMarkovKernel_ladderKernel (Λ Λs : ℕ → Kernel ℝ ℝ)
    (h : ∀ i x, Λs i x univ + ∑ k ∈ Finset.range (i + 1), Λ k x univ = 1) :
    IsMarkovKernel (ladderKernel Λ Λs) := by
  refine ⟨fun p => ⟨?_⟩⟩
  obtain ⟨i, x⟩ := p
  rw [ladderKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
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
  ladderKernel (gig1Lambda H G) (gig1LambdaStar H G)

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
  isMarkovKernel_ladderKernel _ _ fun i x => by rw [gig1Ladder_rowSum, h]

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The forward and backward recurrence time skeletons (MT §3.5.3)

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GI/G/1 queue as a ladder chain (MT §3.5.4)

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

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

namespace MeynTweedie.TransitionProbabilities

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

end MeynTweedie.TransitionProbabilities

set_option linter.style.longLine false
#print axioms MeynTweedie.TransitionProbabilities.trajKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_trajKernel
#print axioms MeynTweedie.TransitionProbabilities.pathKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_pathKernel
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure
#print axioms MeynTweedie.TransitionProbabilities.isProbabilityMeasure_pathMeasure
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_eq_comp
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_dirac
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_map_zero
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_zero_mem
#print axioms MeynTweedie.TransitionProbabilities.ae_pathKernel_zero
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_inter_zero
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_map_zero
#print axioms MeynTweedie.TransitionProbabilities.natFilt
#print axioms MeynTweedie.TransitionProbabilities.measurable_coord_natFilt
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_coord_natFilt
#print axioms MeynTweedie.TransitionProbabilities.setLIntegral_succ
#print axioms MeynTweedie.TransitionProbabilities.cylFn
#print axioms MeynTweedie.TransitionProbabilities.measurable_cylFn
#print axioms MeynTweedie.TransitionProbabilities.boxSet
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_boxSet
#print axioms MeynTweedie.TransitionProbabilities.measure_inter_shift_box
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_boxSet
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_boxSet
#print axioms MeynTweedie.TransitionProbabilities.IsMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.IsMarkovChain.mk
#print axioms MeynTweedie.TransitionProbabilities.IsMarkovChain.measurable
#print axioms MeynTweedie.TransitionProbabilities.IsMarkovChain.fdd
#print axioms MeynTweedie.TransitionProbabilities.theorem_3_4_1
#print axioms MeynTweedie.TransitionProbabilities.generateFrom_boxSets
#print axioms MeynTweedie.TransitionProbabilities.isPiSystem_boxSets
#print axioms MeynTweedie.TransitionProbabilities.theorem_3_4_1_unique
#print axioms MeynTweedie.TransitionProbabilities.law_eq_pathMeasure
#print axioms MeynTweedie.TransitionProbabilities.IsSubstochasticKernel
#print axioms MeynTweedie.TransitionProbabilities.isSubstochasticKernel_of_markov
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_pow
#print axioms MeynTweedie.TransitionProbabilities.pow_zero_apply
#print axioms MeynTweedie.TransitionProbabilities.pow_succ_apply
#print axioms MeynTweedie.TransitionProbabilities.pow_succ_apply'
#print axioms MeynTweedie.TransitionProbabilities.theorem_3_4_2
#print axioms MeynTweedie.TransitionProbabilities.pow_add_eq
#print axioms MeynTweedie.TransitionProbabilities.skeleton
#print axioms MeynTweedie.TransitionProbabilities.skeleton_pow
#print axioms MeynTweedie.TransitionProbabilities.sampledKernel
#print axioms MeynTweedie.TransitionProbabilities.sampledKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_sampledKernel
#print axioms MeynTweedie.TransitionProbabilities.resolvent
#print axioms MeynTweedie.TransitionProbabilities.resolvent_apply
#print axioms MeynTweedie.TransitionProbabilities.tsum_geometric_weights
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_resolvent
#print axioms MeynTweedie.TransitionProbabilities.kfun
#print axioms MeynTweedie.TransitionProbabilities.measurable_kfun
#print axioms MeynTweedie.TransitionProbabilities.kfun_indicator
#print axioms MeynTweedie.TransitionProbabilities.kfun_one
#print axioms MeynTweedie.TransitionProbabilities.kfun_mono
#print axioms MeynTweedie.TransitionProbabilities.kfun_add
#print axioms MeynTweedie.TransitionProbabilities.kfun_const_mul
#print axioms MeynTweedie.TransitionProbabilities.kfun_comp
#print axioms MeynTweedie.TransitionProbabilities.kfun_pow_succ
#print axioms MeynTweedie.TransitionProbabilities.measure_kernel_apply
#print axioms MeynTweedie.TransitionProbabilities.measure_kernel_assoc
#print axioms MeynTweedie.TransitionProbabilities.lintegral_kfun
#print axioms MeynTweedie.TransitionProbabilities.isProbabilityMeasure_measure_kernel
#print axioms MeynTweedie.TransitionProbabilities.dirac_kernel
#print axioms MeynTweedie.TransitionProbabilities.kfunR
#print axioms MeynTweedie.TransitionProbabilities.measurable_kfunR
#print axioms MeynTweedie.TransitionProbabilities.abs_kfunR_le
#print axioms MeynTweedie.TransitionProbabilities.indKernel
#print axioms MeynTweedie.TransitionProbabilities.indKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.comp_indKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.isSubstochasticKernel_comp_indKernel
#print axioms MeynTweedie.TransitionProbabilities.potKernel
#print axioms MeynTweedie.TransitionProbabilities.potKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.shift
#print axioms MeynTweedie.TransitionProbabilities.measurable_shift
#print axioms MeynTweedie.TransitionProbabilities.shift_zero
#print axioms MeynTweedie.TransitionProbabilities.shift_shift
#print axioms MeynTweedie.TransitionProbabilities.shift_apply
#print axioms MeynTweedie.TransitionProbabilities.integral_measure_comp
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_map_coord
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_map_coord
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_coord_mem
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_coord_chapmanKolmogorov
#print axioms MeynTweedie.TransitionProbabilities.markov_measure
#print axioms MeynTweedie.TransitionProbabilities.markov_lintegral
#print axioms MeynTweedie.TransitionProbabilities.markov_lintegral_mul
#print axioms MeynTweedie.TransitionProbabilities.markov_lintegral_univ
#print axioms MeynTweedie.TransitionProbabilities.markov_setIntegral
#print axioms MeynTweedie.TransitionProbabilities.stronglyMeasurable_expect_coord
#print axioms MeynTweedie.TransitionProbabilities.integrable_expect_coord
#print axioms MeynTweedie.TransitionProbabilities.markov_property
#print axioms MeynTweedie.TransitionProbabilities.integrable_shift_of_bdd
#print axioms MeynTweedie.TransitionProbabilities.markov_property_bdd
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_4_3
#print axioms MeynTweedie.TransitionProbabilities.isMarkovChain_of_step
#print axioms MeynTweedie.TransitionProbabilities.skeletonFilt
#print axioms MeynTweedie.TransitionProbabilities.skeleton_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.IsTransitionMatrix
#print axioms MeynTweedie.TransitionProbabilities.matPow
#print axioms MeynTweedie.TransitionProbabilities.matKernel
#print axioms MeynTweedie.TransitionProbabilities.matKernel_singleton
#print axioms MeynTweedie.TransitionProbabilities.matKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_matKernel
#print axioms MeynTweedie.TransitionProbabilities.lintegral_matKernel
#print axioms MeynTweedie.TransitionProbabilities.matKernel_pow_singleton
#print axioms MeynTweedie.TransitionProbabilities.matKernel_pow_apply
#print axioms MeynTweedie.TransitionProbabilities.isTransitionMatrix_matPow
#print axioms MeynTweedie.TransitionProbabilities.cylFn_singletons
#print axioms MeynTweedie.TransitionProbabilities.theorem_3_2_1_fdd
#print axioms MeynTweedie.TransitionProbabilities.IsMarkovChain.fdd_points
#print axioms MeynTweedie.TransitionProbabilities.theorem_3_2_1
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_inter_initial
#print axioms MeynTweedie.TransitionProbabilities.pathMeasure_initial_coord
#print axioms MeynTweedie.TransitionProbabilities.controlMap
#print axioms MeynTweedie.TransitionProbabilities.controlMap_zero
#print axioms MeynTweedie.TransitionProbabilities.controlMap_succ
#print axioms MeynTweedie.TransitionProbabilities.controlMap_one
#print axioms MeynTweedie.TransitionProbabilities.controlMap_succ_cons
#print axioms MeynTweedie.TransitionProbabilities.orbit
#print axioms MeynTweedie.TransitionProbabilities.orbit_zero
#print axioms MeynTweedie.TransitionProbabilities.orbit_succ
#print axioms MeynTweedie.TransitionProbabilities.orbit_eq_controlMap
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_recursionKernel
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_comp_noise
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_const_noise
#print axioms MeynTweedie.TransitionProbabilities.measurable_controlMap
#print axioms MeynTweedie.TransitionProbabilities.measurable_controlMap_right
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_pow_apply
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_pow_apply'
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_map_shift
#print axioms MeynTweedie.TransitionProbabilities.law_orbit
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_eq_lintegral_indicator
#print axioms MeynTweedie.TransitionProbabilities.kfun_recursionKernel
#print axioms MeynTweedie.TransitionProbabilities.kfunR_recursionKernel
#print axioms MeynTweedie.TransitionProbabilities.eq_3_44
#print axioms MeynTweedie.TransitionProbabilities.recursionKernel_pow_succ_apply
#print axioms MeynTweedie.TransitionProbabilities.histMap
#print axioms MeynTweedie.TransitionProbabilities.measurable_histMap
#print axioms MeynTweedie.TransitionProbabilities.canonPath
#print axioms MeynTweedie.TransitionProbabilities.canonPath_zero
#print axioms MeynTweedie.TransitionProbabilities.canonPath_succ
#print axioms MeynTweedie.TransitionProbabilities.measurable_canonPath
#print axioms MeynTweedie.TransitionProbabilities.histFilt
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_map_fin
#print axioms MeynTweedie.TransitionProbabilities.pi_map_init_last
#print axioms MeynTweedie.TransitionProbabilities.law_hist_next
#print axioms MeynTweedie.TransitionProbabilities.canon_step
#print axioms MeynTweedie.TransitionProbabilities.isMarkovChain_canonPath
#print axioms MeynTweedie.TransitionProbabilities.recursion_eq_controlMap
#print axioms MeynTweedie.TransitionProbabilities.isMarkovChain_of_recursion
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise.mk
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise.measurable
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise.law
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise.iIndep
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise.indep
#print axioms MeynTweedie.TransitionProbabilities.IsIIDNoise.map_eq
#print axioms MeynTweedie.TransitionProbabilities.isMarkovChain_of_iid
#print axioms MeynTweedie.TransitionProbabilities.IsMarkovChain.map_eq
#print axioms MeynTweedie.TransitionProbabilities.truncSeq
#print axioms MeynTweedie.TransitionProbabilities.tailSeq
#print axioms MeynTweedie.TransitionProbabilities.measurable_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.measurable_tailSeq
#print axioms MeynTweedie.TransitionProbabilities.iIndep_coords
#print axioms MeynTweedie.TransitionProbabilities.indepFun_truncSeq_tailSeq
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_map_tailSeq
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_map_trunc_tail
#print axioms MeynTweedie.TransitionProbabilities.lintegral_cond_eq
#print axioms MeynTweedie.TransitionProbabilities.measurable_lintegral_cond
#print axioms MeynTweedie.TransitionProbabilities.mul_lintegral_cond
#print axioms MeynTweedie.TransitionProbabilities.lintegral_regeneration
#print axioms MeynTweedie.TransitionProbabilities.setLIntegral_preimage_eq
#print axioms MeynTweedie.TransitionProbabilities.pastFilt
#print axioms MeynTweedie.TransitionProbabilities.isMarkovChain_of_regeneration
#print axioms MeynTweedie.TransitionProbabilities.fwdRecMatrix
#print axioms MeynTweedie.TransitionProbabilities.isTransitionMatrix_fwdRecMatrix
#print axioms MeynTweedie.TransitionProbabilities.ptail
#print axioms MeynTweedie.TransitionProbabilities.ptail_eq
#print axioms MeynTweedie.TransitionProbabilities.ptail_ne_zero_iff
#print axioms MeynTweedie.TransitionProbabilities.bwdRecMatrix
#print axioms MeynTweedie.TransitionProbabilities.bwdRecMatrix_rowSum
#print axioms MeynTweedie.TransitionProbabilities.ptail_ne_zero_of_bwdRecMatrix
#print axioms MeynTweedie.TransitionProbabilities.bwdRecMatrix_zero
#print axioms MeynTweedie.TransitionProbabilities.halfHalf
#print axioms MeynTweedie.TransitionProbabilities.bwdRecMatrix_display_counterexample
#print axioms MeynTweedie.TransitionProbabilities.rwMatrix
#print axioms MeynTweedie.TransitionProbabilities.isTransitionMatrix_rwMatrix
#print axioms MeynTweedie.TransitionProbabilities.rwMatrix_translate
#print axioms MeynTweedie.TransitionProbabilities.rw_step_law
#print axioms MeynTweedie.TransitionProbabilities.rwhlMatrix
#print axioms MeynTweedie.TransitionProbabilities.isTransitionMatrix_rwhlMatrix
#print axioms MeynTweedie.TransitionProbabilities.storage_increment_singleton
#print axioms MeynTweedie.TransitionProbabilities.storage_increment_counterexample
#print axioms MeynTweedie.TransitionProbabilities.poissonWeight
#print axioms MeynTweedie.TransitionProbabilities.poissonWeight_eq
#print axioms MeynTweedie.TransitionProbabilities.tsum_poissonWeight
#print axioms MeynTweedie.TransitionProbabilities.giM1Matrix
#print axioms MeynTweedie.TransitionProbabilities.giM1Increment
#print axioms MeynTweedie.TransitionProbabilities.giM1Matrix_eq_rwhl
#print axioms MeynTweedie.TransitionProbabilities.tsum_giM1Increment
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_1
#print axioms MeynTweedie.TransitionProbabilities.mG1Matrix
#print axioms MeynTweedie.TransitionProbabilities.isTransitionMatrix_mG1Matrix
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_2
#print axioms MeynTweedie.TransitionProbabilities.arMatrix
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_3
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel
#print axioms MeynTweedie.TransitionProbabilities.measurable_add_step
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_randomWalkKernel
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel_real_apply_Iic
#print axioms MeynTweedie.TransitionProbabilities.controlMap_add
#print axioms MeynTweedie.TransitionProbabilities.orbit_randomWalk
#print axioms MeynTweedie.TransitionProbabilities.convPow
#print axioms MeynTweedie.TransitionProbabilities.measurable_sum_fin
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel_pow_apply
#print axioms MeynTweedie.TransitionProbabilities.IsSpreadOut
#print axioms MeynTweedie.TransitionProbabilities.halfLineStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_halfLineStep
#print axioms MeynTweedie.TransitionProbabilities.halfLineWalkKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_halfLineWalkKernel
#print axioms MeynTweedie.TransitionProbabilities.halfLineWalkKernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.halfLineWalkKernel_apply_zero
#print axioms MeynTweedie.TransitionProbabilities.halfLineWalkKernel_apply_Iic
#print axioms MeynTweedie.TransitionProbabilities.halfLineWalkKernel_apply_Ioi
#print axioms MeynTweedie.TransitionProbabilities.halfLineOrbit
#print axioms MeynTweedie.TransitionProbabilities.partialSum
#print axioms MeynTweedie.TransitionProbabilities.halfLineOrbit_succ_coe
#print axioms MeynTweedie.TransitionProbabilities.halfLineOrbit_eq_of_nonneg
#print axioms MeynTweedie.TransitionProbabilities.halfLineOrbit_succ_of_eq_zero
#print axioms MeynTweedie.TransitionProbabilities.halfLineOrbit_eq_lindley
#print axioms MeynTweedie.TransitionProbabilities.reflectStep
#print axioms MeynTweedie.TransitionProbabilities.reflectedWalkKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_reflectedWalkKernel
#print axioms MeynTweedie.TransitionProbabilities.reflectedWalkKernel_apply_pos
#print axioms MeynTweedie.TransitionProbabilities.reflectedWalkKernel_apply_zero
#print axioms MeynTweedie.TransitionProbabilities.not_down_of_eq_2_28
#print axioms MeynTweedie.TransitionProbabilities.twoPointLaw
#print axioms MeynTweedie.TransitionProbabilities.reflectedWalk_2_28_fails
#print axioms MeynTweedie.TransitionProbabilities.birthDeathKernel
#print axioms MeynTweedie.TransitionProbabilities.birthDeathKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_birthDeathKernel
#print axioms MeynTweedie.TransitionProbabilities.birthDeathKernel_apply_succ
#print axioms MeynTweedie.TransitionProbabilities.birthDeathKernel_apply_pred
#print axioms MeynTweedie.TransitionProbabilities.lindleyStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_lindleyStep
#print axioms MeynTweedie.TransitionProbabilities.waitingTimeKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_waitingTimeKernel
#print axioms MeynTweedie.TransitionProbabilities.waitingTimeKernel_eq_halfLineWalk
#print axioms MeynTweedie.TransitionProbabilities.giM1Step
#print axioms MeynTweedie.TransitionProbabilities.giM1Kernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_giM1Kernel
#print axioms MeynTweedie.TransitionProbabilities.giM1Kernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.giM1Kernel_apply_up
#print axioms MeynTweedie.TransitionProbabilities.giM1Kernel_apply_le
#print axioms MeynTweedie.TransitionProbabilities.giM1Kernel_apply_zero
#print axioms MeynTweedie.TransitionProbabilities.giM1Kernel_not_2_28
#print axioms MeynTweedie.TransitionProbabilities.mG1Step
#print axioms MeynTweedie.TransitionProbabilities.mG1Kernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_mG1Kernel
#print axioms MeynTweedie.TransitionProbabilities.mG1Kernel_apply
#print axioms MeynTweedie.TransitionProbabilities.mG1Kernel_zero
#print axioms MeynTweedie.TransitionProbabilities.expMeasure_Ioi
#print axioms MeynTweedie.TransitionProbabilities.expMeasure_memoryless
#print axioms MeynTweedie.TransitionProbabilities.expMeasure_prod_lt
#print axioms MeynTweedie.TransitionProbabilities.dirac_not_memoryless
#print axioms MeynTweedie.TransitionProbabilities.storageStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_storageStep
#print axioms MeynTweedie.TransitionProbabilities.storageKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_storageKernel
#print axioms MeynTweedie.TransitionProbabilities.storageKernel_eq_halfLineWalk
#print axioms MeynTweedie.TransitionProbabilities.releaseLaw_Iic
#print axioms MeynTweedie.TransitionProbabilities.storageKernel_one
#print axioms MeynTweedie.TransitionProbabilities.storage_mean_increment
#print axioms MeynTweedie.TransitionProbabilities.releaseTime
#print axioms MeynTweedie.TransitionProbabilities.continuous_releaseTime
#print axioms MeynTweedie.TransitionProbabilities.releaseTime_strictMono
#print axioms MeynTweedie.TransitionProbabilities.releaseTime_strictMonoOn
#print axioms MeynTweedie.TransitionProbabilities.releaseTime_bijOn
#print axioms MeynTweedie.TransitionProbabilities.releaseTime_one_add_sq
#print axioms MeynTweedie.TransitionProbabilities.releaseTime_not_surjective
#print axioms MeynTweedie.TransitionProbabilities.inputKernel
#print axioms MeynTweedie.TransitionProbabilities.inputKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.contentKernel
#print axioms MeynTweedie.TransitionProbabilities.contentPreInputKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_contentKernel
#print axioms MeynTweedie.TransitionProbabilities.contentRelease_Iic
#print axioms MeynTweedie.TransitionProbabilities.contentKernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.contentKernel_ne_storageKernel
#print axioms MeynTweedie.TransitionProbabilities.contentPreInputKernel_eq_storageKernel
#print axioms MeynTweedie.TransitionProbabilities.renewalKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_renewalKernel
#print axioms MeynTweedie.TransitionProbabilities.renewalKernel_apply_singleton
#print axioms MeynTweedie.TransitionProbabilities.renewalKernel_apply_Ioi
#print axioms MeynTweedie.TransitionProbabilities.le_renewal
#print axioms MeynTweedie.TransitionProbabilities.seqConv
#print axioms MeynTweedie.TransitionProbabilities.seqConv_eq_sum_range
#print axioms MeynTweedie.TransitionProbabilities.seqConv_comm
#print axioms MeynTweedie.TransitionProbabilities.seqConvPow
#print axioms MeynTweedie.TransitionProbabilities.mk_coeff_eq
#print axioms MeynTweedie.TransitionProbabilities.mk_seqConv
#print axioms MeynTweedie.TransitionProbabilities.mk_seqConvPow
#print axioms MeynTweedie.TransitionProbabilities.seqConvPow_succ
#print axioms MeynTweedie.TransitionProbabilities.bind_renewalKernel_singleton
#print axioms MeynTweedie.TransitionProbabilities.renewal_law
#print axioms MeynTweedie.TransitionProbabilities.renewal_law_one
#print axioms MeynTweedie.TransitionProbabilities.fwdStep
#print axioms MeynTweedie.TransitionProbabilities.forwardKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_forwardKernel
#print axioms MeynTweedie.TransitionProbabilities.forwardKernel_of_one_lt
#print axioms MeynTweedie.TransitionProbabilities.forwardKernel_one
#print axioms MeynTweedie.TransitionProbabilities.hazard
#print axioms MeynTweedie.TransitionProbabilities.hazard_le_one
#print axioms MeynTweedie.TransitionProbabilities.backwardKernel
#print axioms MeynTweedie.TransitionProbabilities.backwardKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_backwardKernel
#print axioms MeynTweedie.TransitionProbabilities.backwardKernel_apply_zero
#print axioms MeynTweedie.TransitionProbabilities.backwardKernel_apply_succ
#print axioms MeynTweedie.TransitionProbabilities.fwdTime
#print axioms MeynTweedie.TransitionProbabilities.bwdTime
#print axioms MeynTweedie.TransitionProbabilities.fwdTime_set_nonempty
#print axioms MeynTweedie.TransitionProbabilities.one_le_fwdTime
#print axioms MeynTweedie.TransitionProbabilities.fwdTime_succ_of_one_lt
#print axioms MeynTweedie.TransitionProbabilities.fwdTime_succ_of_eq_one
#print axioms MeynTweedie.TransitionProbabilities.bwdTime_set_empty
#print axioms MeynTweedie.TransitionProbabilities.bwdTime_set_empty_example
#print axioms MeynTweedie.TransitionProbabilities.bwdTime_succ_of_renewal
#print axioms MeynTweedie.TransitionProbabilities.bwdTime_succ_of_not_renewal
#print axioms MeynTweedie.TransitionProbabilities.fwdTimeCts
#print axioms MeynTweedie.TransitionProbabilities.bwdTimeCts
#print axioms MeynTweedie.TransitionProbabilities.fwdSkeleton
#print axioms MeynTweedie.TransitionProbabilities.bwdSkeleton
#print axioms MeynTweedie.TransitionProbabilities.linear_controlMap
#print axioms MeynTweedie.TransitionProbabilities.orbit_linear
#print axioms MeynTweedie.TransitionProbabilities.lssKernel
#print axioms MeynTweedie.TransitionProbabilities.measurable_lssStep
#print axioms MeynTweedie.TransitionProbabilities.lssKernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_lssKernel
#print axioms MeynTweedie.TransitionProbabilities.clm_pow_apply
#print axioms MeynTweedie.TransitionProbabilities.orbit_lss
#print axioms MeynTweedie.TransitionProbabilities.lssKernel_pow_apply
#print axioms MeynTweedie.TransitionProbabilities.measurable_mulVec
#print axioms MeynTweedie.TransitionProbabilities.lssMatrixKernel
#print axioms MeynTweedie.TransitionProbabilities.measurable_lssMatrixStep
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_lssMatrixKernel
#print axioms MeynTweedie.TransitionProbabilities.mulVecHom
#print axioms MeynTweedie.TransitionProbabilities.coe_mulVecHom
#print axioms MeynTweedie.TransitionProbabilities.matrix_pow_mulVec
#print axioms MeynTweedie.TransitionProbabilities.orbit_lssMatrix
#print axioms MeynTweedie.TransitionProbabilities.lssMatrixKernel_pow_apply
#print axioms MeynTweedie.TransitionProbabilities.lcmTrajectory
#print axioms MeynTweedie.TransitionProbabilities.IsControllable
#print axioms MeynTweedie.TransitionProbabilities.lcmTrajectory_eq
#print axioms MeynTweedie.TransitionProbabilities.ar1Kernel
#print axioms MeynTweedie.TransitionProbabilities.measurable_ar1Step
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_ar1Kernel
#print axioms MeynTweedie.TransitionProbabilities.ar1Kernel_apply'
#print axioms MeynTweedie.TransitionProbabilities.ar1Kernel_eq_lssKernel
#print axioms MeynTweedie.TransitionProbabilities.ar1Kernel_one
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel_eq_lssKernel
#print axioms MeynTweedie.TransitionProbabilities.orbit_ar1
#print axioms MeynTweedie.TransitionProbabilities.shiftIn
#print axioms MeynTweedie.TransitionProbabilities.shiftIn_apply_zero
#print axioms MeynTweedie.TransitionProbabilities.shiftIn_apply_succ
#print axioms MeynTweedie.TransitionProbabilities.measurable_shiftIn
#print axioms MeynTweedie.TransitionProbabilities.shiftIn_add
#print axioms MeynTweedie.TransitionProbabilities.arStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_arStep
#print axioms MeynTweedie.TransitionProbabilities.arKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_arKernel
#print axioms MeynTweedie.TransitionProbabilities.companion
#print axioms MeynTweedie.TransitionProbabilities.firstUnit
#print axioms MeynTweedie.TransitionProbabilities.arStep_eq_companion
#print axioms MeynTweedie.TransitionProbabilities.arKernel_eq_lssMatrixKernel
#print axioms MeynTweedie.TransitionProbabilities.arVec
#print axioms MeynTweedie.TransitionProbabilities.arVec_succ
#print axioms MeynTweedie.TransitionProbabilities.armaStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_armaStep
#print axioms MeynTweedie.TransitionProbabilities.armaKernel
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_armaKernel
#print axioms MeynTweedie.TransitionProbabilities.arma_of_ar
#print axioms MeynTweedie.TransitionProbabilities.fig11F
#print axioms MeynTweedie.TransitionProbabilities.fig11F_eq
#print axioms MeynTweedie.TransitionProbabilities.sqNorm2
#print axioms MeynTweedie.TransitionProbabilities.fig11_sqNorm_mulVec
#print axioms MeynTweedie.TransitionProbabilities.fig11_tendsto_zero
#print axioms MeynTweedie.TransitionProbabilities.fig11_inv_tendsto_atTop
#print axioms MeynTweedie.TransitionProbabilities.countEvent
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_countEvent
#print axioms MeynTweedie.TransitionProbabilities.cons_mem_countEvent
#print axioms MeynTweedie.TransitionProbabilities.pi_finSucc_eq_lintegral
#print axioms MeynTweedie.TransitionProbabilities.poissonCount
#print axioms MeynTweedie.TransitionProbabilities.measurable_poissonCount
#print axioms MeynTweedie.TransitionProbabilities.poissonCount_of_nonneg
#print axioms MeynTweedie.TransitionProbabilities.poissonCount_of_neg
#print axioms MeynTweedie.TransitionProbabilities.lintegral_poissonCount
#print axioms MeynTweedie.TransitionProbabilities.eq_3_18
#print axioms MeynTweedie.TransitionProbabilities.eq_3_15
#print axioms MeynTweedie.TransitionProbabilities.eq_3_18_counterexample
#print axioms MeynTweedie.TransitionProbabilities.eq_3_14
#print axioms MeynTweedie.TransitionProbabilities.eq_3_19
#print axioms MeynTweedie.TransitionProbabilities.matKernel_rwMatrix
#print axioms MeynTweedie.TransitionProbabilities.matKernel_rwhlMatrix
#print axioms MeynTweedie.TransitionProbabilities.measure_Ici_succ_eq_tsum
#print axioms MeynTweedie.TransitionProbabilities.matKernel_giM1Matrix
#print axioms MeynTweedie.TransitionProbabilities.matKernel_mG1Matrix
#print axioms MeynTweedie.TransitionProbabilities.matKernel_arMatrix
#print axioms MeynTweedie.TransitionProbabilities.randomWalkInt_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.rwhl_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_1_of_recursion
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_2_of_recursion
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_1_derived
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_2_derived
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_3_3_of_recursion
#print axioms MeynTweedie.TransitionProbabilities.ar1_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.lssMatrix_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.waitingTime_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.randomWalkReal_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.randomWalkKernel_apply_image
#print axioms MeynTweedie.TransitionProbabilities.eq_3_35
#print axioms MeynTweedie.TransitionProbabilities.eq_3_36
#print axioms MeynTweedie.TransitionProbabilities.halfLineWalk_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.eq_3_37
#print axioms MeynTweedie.TransitionProbabilities.eq_3_37_div
#print axioms MeynTweedie.TransitionProbabilities.eq_3_37_counterexample
#print axioms MeynTweedie.TransitionProbabilities.storage_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.renewalMeasure
#print axioms MeynTweedie.TransitionProbabilities.isProbabilityMeasure_convPow
#print axioms MeynTweedie.TransitionProbabilities.sFinite_renewalMeasure
#print axioms MeynTweedie.TransitionProbabilities.conv_apply_eq_lintegral
#print axioms MeynTweedie.TransitionProbabilities.image_sub_const_eq_setOf
#print axioms MeynTweedie.TransitionProbabilities.eq_3_38
#print axioms MeynTweedie.TransitionProbabilities.renewalReal_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.renewalReal_map_eq
#print axioms MeynTweedie.TransitionProbabilities.renewal_expected_count
#print axioms MeynTweedie.TransitionProbabilities.renewal_expected_count_undelayed
#print axioms MeynTweedie.TransitionProbabilities.fwdTimeCts_set_eq
#print axioms MeynTweedie.TransitionProbabilities.fwdTimeCts_add_of_lt
#print axioms MeynTweedie.TransitionProbabilities.fwdSkeleton_succ_of_lt
#print axioms MeynTweedie.TransitionProbabilities.bwdTimeCts_add_of_no_renewal
#print axioms MeynTweedie.TransitionProbabilities.pi_dirac_const
#print axioms MeynTweedie.TransitionProbabilities.convPow_dirac
#print axioms MeynTweedie.TransitionProbabilities.setLIntegral_renewalMeasure_dirac_one
#print axioms MeynTweedie.TransitionProbabilities.eq_3_39_printed
#print axioms MeynTweedie.TransitionProbabilities.eq_3_39_corrected
#print axioms MeynTweedie.TransitionProbabilities.eq_3_39_counterexample
#print axioms MeynTweedie.TransitionProbabilities.ladderRow
#print axioms MeynTweedie.TransitionProbabilities.ladderKernel
#print axioms MeynTweedie.TransitionProbabilities.ladderKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.map_prodMk_apply_prod
#print axioms MeynTweedie.TransitionProbabilities.ladderRow_apply_prod
#print axioms MeynTweedie.TransitionProbabilities.eq_3_40_zero
#print axioms MeynTweedie.TransitionProbabilities.eq_3_40_mid
#print axioms MeynTweedie.TransitionProbabilities.eq_3_40_up
#print axioms MeynTweedie.TransitionProbabilities.ladderKernel_translate
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_ladderKernel
#print axioms MeynTweedie.TransitionProbabilities.resEpoch
#print axioms MeynTweedie.TransitionProbabilities.measurable_resEpoch
#print axioms MeynTweedie.TransitionProbabilities.gig1Set
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_gig1Set
#print axioms MeynTweedie.TransitionProbabilities.ladderP
#print axioms MeynTweedie.TransitionProbabilities.gig1LambdaMeasure
#print axioms MeynTweedie.TransitionProbabilities.gig1LambdaMeasure_apply
#print axioms MeynTweedie.TransitionProbabilities.gig1Lambda
#print axioms MeynTweedie.TransitionProbabilities.eq_3_42
#print axioms MeynTweedie.TransitionProbabilities.gig1LambdaStar
#print axioms MeynTweedie.TransitionProbabilities.eq_3_43
#print axioms MeynTweedie.TransitionProbabilities.gig1Ladder
#print axioms MeynTweedie.TransitionProbabilities.ennreal_sum_add_tsum_nat_add
#print axioms MeynTweedie.TransitionProbabilities.gig1Ladder_rowSum
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_gig1Ladder
#print axioms MeynTweedie.TransitionProbabilities.clamp01
#print axioms MeynTweedie.TransitionProbabilities.continuous_clamp01
#print axioms MeynTweedie.TransitionProbabilities.clamp01_le
#print axioms MeynTweedie.TransitionProbabilities.clamp01_nonneg
#print axioms MeynTweedie.TransitionProbabilities.norm_clamp01_le
#print axioms MeynTweedie.TransitionProbabilities.tendsto_partialSum_atTop_ae
#print axioms MeynTweedie.TransitionProbabilities.resEpoch_mono
#print axioms MeynTweedie.TransitionProbabilities.tsum_indicator_resEpoch_eq_one
#print axioms MeynTweedie.TransitionProbabilities.gig1Lambda_tsum_univ
#print axioms MeynTweedie.TransitionProbabilities.isMarkovKernel_gig1Ladder_of_pos
#print axioms MeynTweedie.TransitionProbabilities.natSInf_eq_iff
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_natSInf_eq
#print axioms MeynTweedie.TransitionProbabilities.measurable_fwdTimeCts
#print axioms MeynTweedie.TransitionProbabilities.resEpoch_succ_eq
#print axioms MeynTweedie.TransitionProbabilities.resEpoch_truncSeq_of_le
#print axioms MeynTweedie.TransitionProbabilities.resEpoch_truncSeq_of_ge
#print axioms MeynTweedie.TransitionProbabilities.fwdTimeCts_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.fwdSkelStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_fwdSkelStep
#print axioms MeynTweedie.TransitionProbabilities.fwdSkelKernel
#print axioms MeynTweedie.TransitionProbabilities.fwdSkel
#print axioms MeynTweedie.TransitionProbabilities.measurable_fwdSkel
#print axioms MeynTweedie.TransitionProbabilities.fwdIndex
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_fwdIndex_eq
#print axioms MeynTweedie.TransitionProbabilities.exists_resEpoch_gt
#print axioms MeynTweedie.TransitionProbabilities.fwdTimeCts_eq_resEpoch
#print axioms MeynTweedie.TransitionProbabilities.fwdSkel_succ
#print axioms MeynTweedie.TransitionProbabilities.prod_map_trunc_tail
#print axioms MeynTweedie.TransitionProbabilities.ae_good_prod
#print axioms MeynTweedie.TransitionProbabilities.fwdSkeleton_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_map_partialSum_next
#print axioms MeynTweedie.TransitionProbabilities.fwdSkelKernel_of_lt
#print axioms MeynTweedie.TransitionProbabilities.indicator_fwdTimeCts_eq_tsum
#print axioms MeynTweedie.TransitionProbabilities.convPow_Iio_zero
#print axioms MeynTweedie.TransitionProbabilities.lintegral_partialSum_pair
#print axioms MeynTweedie.TransitionProbabilities.eq_3_39
#print axioms MeynTweedie.TransitionProbabilities.fwdTimeCts_zero_of_pos
#print axioms MeynTweedie.TransitionProbabilities.fwdSkeleton_isMarkovChain_delayed
#print axioms MeynTweedie.TransitionProbabilities.fwdSkeleton_isMarkovChain_undelayed
#print axioms MeynTweedie.TransitionProbabilities.measurable_bwdTimeCts
#print axioms MeynTweedie.TransitionProbabilities.bwdTimeCts_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.bwdTimeCts_eq_resEpoch
#print axioms MeynTweedie.TransitionProbabilities.bwdTimeCts_truncSeq_of_le
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelStep
#print axioms MeynTweedie.TransitionProbabilities.measurable_bwdSkelStep
#print axioms MeynTweedie.TransitionProbabilities.bwdSkel
#print axioms MeynTweedie.TransitionProbabilities.measurable_bwdSkel
#print axioms MeynTweedie.TransitionProbabilities.bwdIndex
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_bwdIndex_eq
#print axioms MeynTweedie.TransitionProbabilities.bwdIndex_spec
#print axioms MeynTweedie.TransitionProbabilities.bwdSkel_eq
#print axioms MeynTweedie.TransitionProbabilities.bwdSkel_succ
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelKernel
#print axioms MeynTweedie.TransitionProbabilities.bwdSkel_zero_ae
#print axioms MeynTweedie.TransitionProbabilities.bwdSkeleton_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.bwdTimeCts_first
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelStep_of_gt
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelStep_lt
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelStep_split
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_measure_head
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelKernel_apply_add
#print axioms MeynTweedie.TransitionProbabilities.bwdInner
#print axioms MeynTweedie.TransitionProbabilities.indicator_bwdTimeCts_eq_tsum
#print axioms MeynTweedie.TransitionProbabilities.lintegral_partialSum_pair_bwd
#print axioms MeynTweedie.TransitionProbabilities.bwd_inner
#print axioms MeynTweedie.TransitionProbabilities.infinitePi_map_head_tail
#print axioms MeynTweedie.TransitionProbabilities.bwdSkelKernel_apply_of_subset
#print axioms MeynTweedie.TransitionProbabilities.halfOneTwo
#print axioms MeynTweedie.TransitionProbabilities.halfOneTwo_apply
#print axioms MeynTweedie.TransitionProbabilities.isProbabilityMeasure_halfOneTwo
#print axioms MeynTweedie.TransitionProbabilities.lintegral_halfOneTwo
#print axioms MeynTweedie.TransitionProbabilities.convPow_eq_map
#print axioms MeynTweedie.TransitionProbabilities.bwd_display_counterexample
#print axioms MeynTweedie.TransitionProbabilities.map_prod_prod_rearrange
#print axioms MeynTweedie.TransitionProbabilities.arrT
#print axioms MeynTweedie.TransitionProbabilities.depT
#print axioms MeynTweedie.TransitionProbabilities.inService
#print axioms MeynTweedie.TransitionProbabilities.queueN
#print axioms MeynTweedie.TransitionProbabilities.queueR
#print axioms MeynTweedie.TransitionProbabilities.arrT_succ
#print axioms MeynTweedie.TransitionProbabilities.arrT_mono
#print axioms MeynTweedie.TransitionProbabilities.arrT_lt_depT
#print axioms MeynTweedie.TransitionProbabilities.depT_lt_succ
#print axioms MeynTweedie.TransitionProbabilities.depT_mono
#print axioms MeynTweedie.TransitionProbabilities.inService_spec
#print axioms MeynTweedie.TransitionProbabilities.queueN_eq
#print axioms MeynTweedie.TransitionProbabilities.inService_mono
#print axioms MeynTweedie.TransitionProbabilities.depT_chain
#print axioms MeynTweedie.TransitionProbabilities.numDone
#print axioms MeynTweedie.TransitionProbabilities.gig1Step
#print axioms MeynTweedie.TransitionProbabilities.gig1_step_eq
#print axioms MeynTweedie.TransitionProbabilities.measurable_comp_index
#print axioms MeynTweedie.TransitionProbabilities.measurable_arrT
#print axioms MeynTweedie.TransitionProbabilities.measurable_depT
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_inService_eq
#print axioms MeynTweedie.TransitionProbabilities.measurable_inService
#print axioms MeynTweedie.TransitionProbabilities.measurable_queueN
#print axioms MeynTweedie.TransitionProbabilities.measurable_queueR
#print axioms MeynTweedie.TransitionProbabilities.measurable_numDone
#print axioms MeynTweedie.TransitionProbabilities.measurable_gig1Step
#print axioms MeynTweedie.TransitionProbabilities.arrT_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.depT_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.inService_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.inService_eq_iff_truncSeq
#print axioms MeynTweedie.TransitionProbabilities.measure_ext_nat_prod
#print axioms MeynTweedie.TransitionProbabilities.gig1Step0
#print axioms MeynTweedie.TransitionProbabilities.numDone_le_of_lt
#print axioms MeynTweedie.TransitionProbabilities.numDone_eq_iff
#print axioms MeynTweedie.TransitionProbabilities.tsum_indicator_tail_eq
#print axioms MeynTweedie.TransitionProbabilities.measurable_gig1Step0
#print axioms MeynTweedie.TransitionProbabilities.gig1Step0_fst_le
#print axioms MeynTweedie.TransitionProbabilities.gig1Step0_mem_zero_iff
#print axioms MeynTweedie.TransitionProbabilities.gig1Step0_mem_iff
#print axioms MeynTweedie.TransitionProbabilities.ae_good_gig1
#print axioms MeynTweedie.TransitionProbabilities.gig1Ladder_eq_map
#print axioms MeynTweedie.TransitionProbabilities.gig1_law_past_future
#print axioms MeynTweedie.TransitionProbabilities.ae_good_queue
#print axioms MeynTweedie.TransitionProbabilities.gig1_isMarkovChain
#print axioms MeynTweedie.TransitionProbabilities.iSup_natFilt
#print axioms MeynTweedie.TransitionProbabilities.setOf_le_eq_biUnion
#print axioms MeynTweedie.TransitionProbabilities.setOf_ne_top_eq_iUnion
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_ne_top
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_stoppedField_iff
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_stoppedField_ne_top
#print axioms MeynTweedie.TransitionProbabilities.stoppedState
#print axioms MeynTweedie.TransitionProbabilities.shiftAt
#print axioms MeynTweedie.TransitionProbabilities.stoppedState_of_eq
#print axioms MeynTweedie.TransitionProbabilities.shiftAt_of_eq
#print axioms MeynTweedie.TransitionProbabilities.measurable_of_stopping_pieces
#print axioms MeynTweedie.TransitionProbabilities.measurable_stoppedState
#print axioms MeynTweedie.TransitionProbabilities.measurable_shiftAt
#print axioms MeynTweedie.TransitionProbabilities.measurable_stoppedField_indicator
#print axioms MeynTweedie.TransitionProbabilities.inter_ne_top_eq_iUnion
#print axioms MeynTweedie.TransitionProbabilities.pairwise_disjoint_inter_eq
#print axioms MeynTweedie.TransitionProbabilities.strong_markov_lintegral
#print axioms MeynTweedie.TransitionProbabilities.strong_markov_lintegral_mul
#print axioms MeynTweedie.TransitionProbabilities.strong_markov_measure
#print axioms MeynTweedie.TransitionProbabilities.strong_markov_setIntegral
#print axioms MeynTweedie.TransitionProbabilities.strong_markov_property
#print axioms MeynTweedie.TransitionProbabilities.StrongMarkovProperty
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_4_6
#print axioms MeynTweedie.TransitionProbabilities.occTime
#print axioms MeynTweedie.TransitionProbabilities.firstReturn
#print axioms MeynTweedie.TransitionProbabilities.firstHit
#print axioms MeynTweedie.TransitionProbabilities.returnTimeK
#print axioms MeynTweedie.TransitionProbabilities.hitProb
#print axioms MeynTweedie.TransitionProbabilities.returnTimeK_one
#print axioms MeynTweedie.TransitionProbabilities.returnTimeK_succ_of_eq
#print axioms MeynTweedie.TransitionProbabilities.returnTimeK_succ_of_top
#print axioms MeynTweedie.TransitionProbabilities.firstReturn_ne_top_iff
#print axioms MeynTweedie.TransitionProbabilities.le_firstReturn_iff
#print axioms MeynTweedie.TransitionProbabilities.one_le_firstReturn
#print axioms MeynTweedie.TransitionProbabilities.firstReturn_eq_iff
#print axioms MeynTweedie.TransitionProbabilities.le_firstReturn_succ_iff
#print axioms MeynTweedie.TransitionProbabilities.firstHit_eq_zero_iff
#print axioms MeynTweedie.TransitionProbabilities.firstHit_eq_firstReturn
#print axioms MeynTweedie.TransitionProbabilities.adapted_coord
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_4_4
#print axioms MeynTweedie.TransitionProbabilities.isStoppingTime_returnTimeK
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_firstReturn_ne_top
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_firstReturn_eq
#print axioms MeynTweedie.TransitionProbabilities.measurableSet_le_firstReturn
#print axioms MeynTweedie.TransitionProbabilities.measurable_occTime
#print axioms MeynTweedie.TransitionProbabilities.measurable_hitProb
#print axioms MeynTweedie.TransitionProbabilities.potKernel_eq_lintegral_occTime
#print axioms MeynTweedie.TransitionProbabilities.pathKernel_first_step
#print axioms MeynTweedie.TransitionProbabilities.tabooKernel
#print axioms MeynTweedie.TransitionProbabilities.comp_indKernel_eq_restrict
#print axioms MeynTweedie.TransitionProbabilities.tabooKernel_zero
#print axioms MeynTweedie.TransitionProbabilities.tabooKernel_succ_apply
#print axioms MeynTweedie.TransitionProbabilities.tabooProb
#print axioms MeynTweedie.TransitionProbabilities.tabooProb_one
#print axioms MeynTweedie.TransitionProbabilities.tabooProb_succ
#print axioms MeynTweedie.TransitionProbabilities.tabooProb_eq_tabooKernel
#print axioms MeynTweedie.TransitionProbabilities.firstReturn_eq_tabooProb
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_4_5_i
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_4_5_i_succ
#print axioms MeynTweedie.TransitionProbabilities.firstReturn_eq_tabooKernel
#print axioms MeynTweedie.TransitionProbabilities.nestedTaboo
#print axioms MeynTweedie.TransitionProbabilities.firstReturn_eq_nestedTaboo
#print axioms MeynTweedie.TransitionProbabilities.proposition_3_4_5_ii
#print axioms MeynTweedie.TransitionProbabilities.hitProb_eq_tsum
#print axioms MeynTweedie.TransitionProbabilities.hitProb_first_step
#print axioms MeynTweedie.TransitionProbabilities.tabooPotKernel
#print axioms MeynTweedie.TransitionProbabilities.tabooPotKernel_apply
#print axioms MeynTweedie.TransitionProbabilities.tabooPotKernel_self
#print axioms MeynTweedie.TransitionProbabilities.IsCountableStateSpace
#print axioms MeynTweedie.TransitionProbabilities.IsGeneralStateSpace
#print axioms MeynTweedie.TransitionProbabilities.IsTopologicalStateSpace
#print axioms MeynTweedie.TransitionProbabilities.IsCountableStateSpace.isGeneral
#print axioms MeynTweedie.TransitionProbabilities.IsTopologicalStateSpace.isGeneral
