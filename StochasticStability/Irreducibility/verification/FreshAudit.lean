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
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Cardinality
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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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
`X₀` is again a controllable LSS model, and hence `μ_Leb`-irreducible on `X₀` with Lebesgue
measure on `X₀` maximal, is proved in `LinearRestriction` (`restricted_irreducible`).
-/

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linear state space model restricted to its controllable subspace (MT §4.4.3)

Meyn and Tweedie, §4.4.3, p. 93. When `(F, G)` is not controllable, the range
`X₀ = R[F^{n−1}G | ⋯ | FG | G] = {Σ_{i<n} Fⁱ G wᵢ}` of the controllability matrix
(`ctrbSubspace F G`) is absorbing for LSS(F, G) (`ctrbSubspace_isAbsorbing`), so the chain can be
restricted to `X₀` (Proposition 4.2.4). The book states that the restricted process is again a
linear state space model with a controllable pair `(F₀, G₀)`, and hence, by Proposition 4.4.3, is
`μ_Leb`-irreducible on `X₀`.

Lebesgue measure on `X₀` is taken to be any additive Haar measure `μ₀` on the subspace `X₀`
(any two are proportional; the image of Lebesgue measure under a linear isometry
`EuclideanSpace ℝ (Fin r) ≃ X₀` is one of them).

* `pow_mulVec_mem_ctrbSubspace`: `X₀` is invariant under `F`; `ctrbMap_mem_ctrbSubspace`:
  `C_k u ∈ X₀` for every `k`.
* `ctrbF₀`, `ctrbG₀`: the restricted pair `F₀ = F|_{X₀}`, `G₀ : ℝᵖ → X₀`;
  `restrictKernel_eq_lssKernel`: the restricted chain is the linear state space model
  LSS(F₀, G₀) on `X₀`; `restricted_controllable`: `(F₀, G₀)` is controllable, every state of `X₀`
  being reached from every other in `n` steps.
* `restricted_pow_eq_zero_iff`: for `k ≥ n` and a disturbance law equivalent to Lebesgue measure,
  `P_{X₀}ᵏ(x, B) = 0` iff `μ₀(B) = 0`.
* `restricted_isPhiIrreducible`, `restricted_isMaximalIrreducibility` and the summary
  `restricted_irreducible` (p. 93): the restricted chain is `φ`-irreducible for every `φ ≪ μ₀`,
  and `μ₀` is a maximal irreducibility measure. The Gaussian case (LSS3) is
  `restricted_irreducible_gaussian`.

No controllability hypothesis is needed: when `(F, G)` is controllable, `X₀ = ℝⁿ`.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Matrix

variable {n p : ℕ}

/-- The controllable subspace `X₀`, the range of the controllability matrix `C_n` (MT p. 93). -/
noncomputable abbrev ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range (ctrbMap F G n)

/-- `X₀` is a measurable set. -/
theorem measurableSet_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) : MeasurableSet (ctrbSubspace F G : Set (Fin n → ℝ)) :=
  (Submodule.closed_of_finiteDimensional _).measurableSet

/-- `X₀` is invariant under `F`, hence under every power `Fᵏ`. -/
theorem pow_mulVec_mem_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) {x : Fin n → ℝ} (hx : x ∈ ctrbSubspace F G) (k : ℕ) :
    (F ^ k) *ᵥ x ∈ ctrbSubspace F G := by
  induction k with
  | zero => rwa [pow_zero, one_mulVec]
  | succ k ih =>
    have := ctrbSubspace_absorbing_step F G ih 0
    rwa [mulVec_zero, add_zero, mulVec_mulVec, ← pow_succ'] at this

/-- `C_k u ∈ X₀` for every `k` (Cayley–Hamilton). -/
theorem ctrbMap_mem_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (u : Fin k → Fin p → ℝ) : ctrbMap F G k u ∈ ctrbSubspace F G :=
  range_ctrbMap_le_n F G k ⟨u, rfl⟩

/-- `C_k` as a linear map onto `X₀`. -/
noncomputable def ctrbMap₀ (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : (Fin k → Fin p → ℝ) →ₗ[ℝ] ctrbSubspace F G :=
  (ctrbMap F G k).codRestrict _ (ctrbMap_mem_ctrbSubspace F G k)

/-- For `k ≥ n`, `C_k` maps onto `X₀`. -/
theorem ctrbMap₀_surjective (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {k : ℕ} (hk : n ≤ k) : Function.Surjective (ctrbMap₀ F G k) := by
  rintro ⟨y, hy⟩
  obtain ⟨u, hu⟩ := range_ctrbMap_mono F G hk hy
  exact ⟨u, Subtype.ext hu⟩

/-! ### The restricted pair `(F₀, G₀)` -/

/-- `F₀ = F` restricted to `X₀`. -/
noncomputable def ctrbF₀ (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    ctrbSubspace F G →L[ℝ] ctrbSubspace F G :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin F).restrict fun x hx => by
    simpa using pow_mulVec_mem_ctrbSubspace F G hx 1)

/-- `G₀ = G` viewed as a map into `X₀`. -/
noncomputable def ctrbG₀ (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    (Fin p → ℝ) →L[ℝ] ctrbSubspace F G :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin G).codRestrict _ fun w => by
    have := ctrbSubspace_absorbing_step F G (zero_mem (ctrbSubspace F G)) w
    simpa using this)

/-- `↑(F₀ x + G₀ w) = F x + G w`. -/
theorem coe_ctrbStep (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (x : ctrbSubspace F G) (w : Fin p → ℝ) :
    ((ctrbF₀ F G x + ctrbG₀ F G w : ctrbSubspace F G) : Fin n → ℝ) = F *ᵥ x + G *ᵥ w := rfl

/-- MT p. 93: the chain restricted to the absorbing set `X₀` is the linear state space model
LSS(F₀, G₀) on `X₀`. -/
theorem restrictKernel_eq_lssKernel (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G)) =
      lssKernel Γ (ctrbF₀ F G) (ctrbG₀ F G) := by
  ext x B hB
  have hB' : MeasurableSet (Subtype.val '' B : Set (Fin n → ℝ)) :=
    (MeasurableEmbedding.subtype_coe (measurableSet_ctrbSubspace F G)).measurableSet_image.2 hB
  rw [restrictKernel_apply _ _ x hB, lssMatrixKernel,
    recursionKernel_apply' Γ (measurable_lssMatrixStep F G) _ hB']
  erw [lssKernel_apply' Γ (ctrbF₀ F G) (ctrbG₀ F G) x hB]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨b, hb, hbw⟩
    have : b = ctrbF₀ F G x + ctrbG₀ F G w := Subtype.ext (by rw [coe_ctrbStep]; exact hbw)
    exact this ▸ hb
  · intro h
    exact ⟨_, h, coe_ctrbStep F G x w⟩

/-- The control trajectories of `(F₀, G₀)` are those of `(F, G)` started in `X₀`. -/
theorem coe_controlMap_ctrb (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x₀ : ctrbSubspace F G) (u : Fin k → Fin p → ℝ) :
    ((controlMap (fun q : ctrbSubspace F G × (Fin p → ℝ) => ctrbF₀ F G q.1 + ctrbG₀ F G q.2)
        k x₀ u : ctrbSubspace F G) : Fin n → ℝ) = lcmTrajectory F G k x₀ u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [controlMap_succ, coe_ctrbStep, ih]
    rfl

/-- MT p. 93: the pair `(F₀, G₀)` is controllable: every state of `X₀` is reached from every
initial state in `X₀`, in `n` steps. -/
theorem restricted_controllable (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (x₀ x : ctrbSubspace F G) :
    ∃ u : Fin n → Fin p → ℝ,
      controlMap (fun q : ctrbSubspace F G × (Fin p → ℝ) => ctrbF₀ F G q.1 + ctrbG₀ F G q.2)
        n x₀ u = x := by
  have hmem : (x : Fin n → ℝ) - (F ^ n) *ᵥ x₀ ∈ ctrbSubspace F G :=
    sub_mem x.2 (pow_mulVec_mem_ctrbSubspace F G x₀.2 n)
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, Subtype.ext ?_⟩
  rw [coe_controlMap_ctrb, lcmTrajectory_eq_ctrbMap, hu, add_sub_cancel]

/-! ### Irreducibility of the restricted chain -/

/-- For `k ≥ n` and a disturbance law equivalent to Lebesgue measure, the `k`-step law of the
restricted chain has the same null sets as any Haar measure `μ₀` on `X₀`. -/
theorem restricted_pow_eq_zero_iff (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure] {k : ℕ}
    (hk : n ≤ k) (x : ctrbSubspace F G) {B : Set (ctrbSubspace F G)} (hB : MeasurableSet B) :
    ((restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G)) ^ k) x B = 0 ↔ μ₀ B = 0 := by
  have hX := measurableSet_ctrbSubspace F G
  have := isMarkovKernel_lssMatrixKernel Γ F G
  have hAbs := (ctrbSubspace_isAbsorbing Γ F G).2
  have hB' : MeasurableSet (Subtype.val '' B : Set (Fin n → ℝ)) :=
    (MeasurableEmbedding.subtype_coe hX).measurableSet_image.2 hB
  set c₀ : ctrbSubspace F G := ⟨(F ^ k) *ᵥ x, pow_mulVec_mem_ctrbSubspace F G x.2 k⟩
  set L₀ := ctrbMap₀ F G k
  have hL₀ : Measurable L₀ := L₀.continuous_of_finiteDimensional.measurable
  have hT : MeasurableSet (L₀ ⁻¹' ((fun y => c₀ + y) ⁻¹' B)) :=
    hL₀ ((measurable_const_add c₀) hB)
  have hset : ctrbMap F G k ⁻¹' ((fun y => (F ^ k) *ᵥ (x : Fin n → ℝ) + y) ⁻¹' (Subtype.val '' B)) =
      L₀ ⁻¹' ((fun y => c₀ + y) ⁻¹' B) := by
    ext u
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨b, hb, hbu⟩
      have : b = c₀ + L₀ u := Subtype.ext hbu
      exact this ▸ hb
    · intro h
      exact ⟨_, h, rfl⟩
  rw [restrictKernel_pow_apply _ hX hAbs k x hB, lss_pow_eq]
  erw [Measure.map_apply (measurable_const_add ((F ^ k) *ᵥ (x : Fin n → ℝ))) hB', ctrbLaw,
    Measure.map_apply (measurable_ctrbMap F G k)
      (measurable_const_add ((F ^ k) *ᵥ (x : Fin n → ℝ)) hB'), hset]
  have hpi1 : Measure.pi (fun _ : Fin k => Γ) ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h1 k
  have hpi2 : volume ≪ Measure.pi (fun _ : Fin k => Γ) := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h2 k
  have key := ae_comp_linearMap_mem_iff L₀ (volume : Measure (Fin k → Fin p → ℝ)) μ₀
    (ctrbMap₀_surjective F G hk) ((measurable_const_add c₀) hB).compl
  have key' : volume (L₀ ⁻¹' ((fun y => c₀ + y) ⁻¹' B)) = 0 ↔
      μ₀ ((fun y => c₀ + y) ⁻¹' B) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem]
    simpa using key
  rw [measure_preimage_add] at key'
  exact ⟨fun h => key'.1 (hpi2 h), fun h => hpi1 (key'.2 h)⟩

/-- MT p. 93: the restricted chain is `φ`-irreducible for every `φ ≪ μ₀`. -/
theorem restricted_isPhiIrreducible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure]
    [IsMarkovKernel (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G))]
    {φ : Measure (ctrbSubspace F G)} (hφ : φ ≪ μ₀) :
    IsPhiIrreducible (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G)) φ := by
  intro A hA hpos x
  have hA0 : μ₀ A ≠ 0 := fun h => hpos.ne' (hφ h)
  refine (hitProb_pos_iff _ hA x).2 ⟨n, pos_iff_ne_zero.2 fun h => hA0 ?_⟩
  exact (restricted_pow_eq_zero_iff Γ F G h1 h2 μ₀ (by omega) x hA).1 h

/-- MT p. 93: any Haar measure `μ₀` on `X₀` is a maximal irreducibility measure for the
restricted chain. -/
theorem restricted_isMaximalIrreducibility (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure]
    [IsMarkovKernel (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G))] :
    IsMaximalIrreducibility (restrictKernel (lssMatrixKernel Γ F G)
        (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)) μ₀ := by
  set P : Kernel (ctrbSubspace F G) (ctrbSubspace F G) :=
    restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G)
  refine ⟨NeZero.ne _, restricted_isPhiIrreducible Γ F G h1 h2 μ₀
    Measure.AbsolutelyContinuous.rfl, fun φ' hφ' => Measure.AbsolutelyContinuous.mk
      fun A hA h0 => ?_⟩
  by_contra hcon
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
  exact h3.ne' ((restricted_pow_eq_zero_iff Γ F G h1 h2 μ₀ (k := n + 1 + (m + 1)) (by omega)
    0 hA).2 h0)

/-- **The restricted model** (MT p. 93). For any `(F, G)` and a disturbance law equivalent to
Lebesgue measure, the chain restricted to the absorbing controllable subspace `X₀` is a
transition kernel on `X₀`, equal to LSS(F₀, G₀) with `(F₀, G₀)` controllable; it is
`φ`-irreducible for every `φ ≪ μ₀`, and `μ₀` (Lebesgue measure on `X₀`) is a maximal
irreducibility measure. -/
theorem restricted_irreducible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure] :
    ∃ _ : IsMarkovKernel (restrictKernel (lssMatrixKernel Γ F G)
        (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)),
      (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
          Kernel (ctrbSubspace F G) (ctrbSubspace F G)) =
        lssKernel Γ (ctrbF₀ F G) (ctrbG₀ F G) ∧
      (∀ φ : Measure (ctrbSubspace F G), φ ≪ μ₀ →
        IsPhiIrreducible (restrictKernel (lssMatrixKernel Γ F G)
          (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)) φ) ∧
      IsMaximalIrreducibility (restrictKernel (lssMatrixKernel Γ F G)
        (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)) μ₀ := by
  have hM := isMarkovKernel_restrictKernel (lssMatrixKernel Γ F G)
    (measurableSet_ctrbSubspace F G) (ctrbSubspace_isAbsorbing Γ F G).2
  exact ⟨hM, restrictKernel_eq_lssKernel Γ F G,
    fun φ hφ => restricted_isPhiIrreducible Γ F G h1 h2 μ₀ hφ,
    restricted_isMaximalIrreducibility Γ F G h1 h2 μ₀⟩

/-- The restricted model with Gaussian noise (LSS3), MT p. 93. -/
theorem restricted_irreducible_gaussian (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure] :
    ∃ _ : IsMarkovKernel (restrictKernel (lssMatrixKernel (Measure.pi fun _ : Fin p =>
        gaussianReal 0 1) F G) (measurableSet_ctrbSubspace F G) :
          Kernel (ctrbSubspace F G) (ctrbSubspace F G)),
      (∀ φ : Measure (ctrbSubspace F G), φ ≪ μ₀ →
        IsPhiIrreducible (restrictKernel (lssMatrixKernel (Measure.pi fun _ : Fin p =>
          gaussianReal 0 1) F G) (measurableSet_ctrbSubspace F G) :
            Kernel (ctrbSubspace F G) (ctrbSubspace F G)) φ) ∧
      IsMaximalIrreducibility (restrictKernel (lssMatrixKernel (Measure.pi fun _ : Fin p =>
        gaussianReal 0 1) F G) (measurableSet_ctrbSubspace F G) :
          Kernel (ctrbSubspace F G) (ctrbSubspace F G)) μ₀ := by
  obtain ⟨hM, -, h1, h2⟩ := restricted_irreducible _ F G (stdGaussian_equiv_volume p).1
    (stdGaussian_equiv_volume p).2 μ₀
  exact ⟨hM, h1, h2⟩

end MeynTweedie.Irreducibility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Further claims of Chapter 4

Text claims of MT Chapter 4 not covered by the other modules.

* `ar_isPhiIrreducible` (MT p. 89): the AR(k) model with an innovation law equivalent to
  Lebesgue measure (an everywhere positive density, e.g. Gaussian) is `μ_Leb`-irreducible on
  `ℝᵏ` for any coefficients, with Lebesgue measure maximal and every set of positive measure
  uniformly accessible from every compact set (Propositions 4.4.2, 4.4.3 and the state space
  form (2.1)).
* `range_gramian` (MT p. 93): the range of the controllability Gramian `Σ_k` equals the range of
  `C_k`, not only its rank; `range_gramian_n`: for `k = n` both are `X₀`.
* `isControllable_of_rank_G`, `lss_fullRank_G_irreducible` (MT p. 92): if `p = n` and `G` has full
  rank, `(F, G)` is controllable, so the Gaussian LSS(F, G) is `μ_Leb`-irreducible.
* `finrank_ctrbSubspace` (MT p. 93): `dim X₀ = rank C_n`; `finrank_ctrbSubspace_lt`: if `(F, G)` is
  not controllable, `dim X₀ < n`.
* `countable_absorbing_classes` (MT (4.8), p. 81): on a countable space the decomposition (4.5) is
  a Doeblin decomposition, with countably many absorbing classes. The general-space Doeblin
  decomposition (4.8) is not a precise claim of the book ("`D` in some sense ephemeral") and is
  explicitly not discussed there.
* `unifAccessible_not_refl` (MT p. 86): `⇝` is not reflexive.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal Matrix

/-! ### AR(k) -/

/-- An innovation law on `ℝ` equivalent to Lebesgue measure, viewed on `ℝ¹`, is equivalent to
Lebesgue measure on `ℝ¹`. -/
theorem map_fin_one_equiv (Γ : Measure ℝ) (h1 : Γ ≪ volume) (h2 : volume ≪ Γ) :
    Γ.map (fun w _ => w : ℝ → Fin 1 → ℝ) ≪ volume ∧
      volume ≪ Γ.map (fun w _ => w : ℝ → Fin 1 → ℝ) := by
  have he : (fun w _ => w : ℝ → Fin 1 → ℝ) = ⇑(MeasurableEquiv.funUnique (Fin 1) ℝ).symm := rfl
  have hv : (volume : Measure ℝ).map (MeasurableEquiv.funUnique (Fin 1) ℝ).symm =
      (volume : Measure (Fin 1 → ℝ)) :=
    ((volume_preserving_funUnique (Fin 1) ℝ).symm _).map_eq
  rw [he, ← hv]
  exact ⟨h1.map (MeasurableEquiv.measurable _), h2.map (MeasurableEquiv.measurable _)⟩

/-- MT p. 89 (with Propositions 4.4.2 and 4.4.3): the AR(k) model `Yₙ = Σ αᵢ Yₙ₋ᵢ + Wₙ` in its
state space form on `ℝᵏ`, with an innovation law equivalent to Lebesgue measure, is
`φ`-irreducible for every `φ ≪ μ_Leb` whatever the coefficients `α`; Lebesgue measure is a
maximal irreducibility measure, and `A ⇝ B` for compact `A` and `μ_Leb(B) > 0`. -/
theorem ar_isPhiIrreducible {k : ℕ} (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (α : Fin k → ℝ) :
    ∃ _ : IsMarkovKernel (arKernel Γ α),
      (∀ φ : Measure (Fin k → ℝ), φ ≪ volume → IsPhiIrreducible (arKernel Γ α) φ) ∧
      IsMaximalIrreducibility (arKernel Γ α) volume ∧
      ∀ A B : Set (Fin k → ℝ), IsCompact A → MeasurableSet B → 0 < volume B →
        UnifAccessible (arKernel Γ α) A B := by
  obtain ⟨g1, g2⟩ := map_fin_one_equiv Γ h1 h2
  have hP : IsProbabilityMeasure (Γ.map (fun w _ => w : ℝ → Fin 1 → ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_pi_iff.mpr fun _ => measurable_id).aemeasurable).2 inferInstance
  have heq := arKernel_eq_lssMatrixKernel Γ α
  rw [heq]
  exact proposition_4_4_3 _ (proposition_4_4_2 α).2 g1 g2

/-! ### The Gramian and the controllable subspace -/

variable {n p : ℕ}

/-- MT p. 93: the range of the Gramian `Σ_k = C_k C_kᵀ` equals the range of `C_k`. -/
theorem range_gramian (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    LinearMap.range (gramian F G k).mulVecLin = LinearMap.range (ctrbMap F G k) := by
  rw [← range_ctrbMatrix]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro x ⟨v, rfl⟩
    refine ⟨(ctrbMatrix F G k)ᵀ *ᵥ v, ?_⟩
    simp only [mulVecLin_apply, mulVec_mulVec, gramian_eq]
  · have := rank_gramian F G k
    exact this

/-- MT p. 93: the range of `Σ_n` is the controllable subspace `X₀`. -/
theorem range_gramian_n (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    LinearMap.range (gramian F G n).mulVecLin = ctrbSubspace F G :=
  range_gramian F G n

/-- MT p. 93: `dim X₀ = rank C_n`. -/
theorem finrank_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Module.finrank ℝ (ctrbSubspace F G) = (ctrbMatrix F G n).rank := by
  rw [Matrix.rank, range_ctrbMatrix]

/-- MT p. 93: if `(F, G)` is not controllable, `X₀` has dimension strictly less than `n`. -/
theorem finrank_ctrbSubspace_lt (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (h : ¬ IsControllable F G) : Module.finrank ℝ (ctrbSubspace F G) < n := by
  rw [finrank_ctrbSubspace]
  have hle : (ctrbMatrix F G n).rank ≤ n := by
    rw [← finrank_ctrbSubspace]
    simpa using Submodule.finrank_le (ctrbSubspace F G)
  rw [isControllable_iff_rank] at h
  exact lt_of_le_of_ne hle h

/-- MT p. 92: if `p = n` and `G` has full rank, `(F, G)` is controllable (in one step). -/
theorem isControllable_of_rank_G (F G : Matrix (Fin n) (Fin n) ℝ) (hG : G.rank = n) :
    IsControllable F G := by
  rw [isControllable_iff_exists_rank]
  refine ⟨1, (rank_ctrbMatrix_eq_iff F G 1).2 (eq_top_iff.2 fun x _ => ?_)⟩
  have hG' : LinearMap.range G.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [← Matrix.rank, hG, Module.finrank_fin_fun])
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 hG' x
  refine ⟨fun _ => v, ?_⟩
  rw [ctrbMap_apply, Fin.sum_univ_one]
  simpa using hv

/-- MT p. 92: with `p = n`, `G` of full rank and Gaussian noise, LSS(F, G) is
`μ_Leb`-irreducible, with Lebesgue measure maximal. -/
theorem lss_fullRank_G_irreducible (F G : Matrix (Fin n) (Fin n) ℝ) (hG : G.rank = n) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel (Measure.pi fun _ : Fin n => gaussianReal 0 1) F G),
      (∀ φ : Measure (Fin n → ℝ), φ ≪ volume →
        IsPhiIrreducible (lssMatrixKernel (Measure.pi fun _ : Fin n => gaussianReal 0 1) F G) φ) ∧
      IsMaximalIrreducibility (lssMatrixKernel (Measure.pi fun _ : Fin n => gaussianReal 0 1) F G)
        volume := by
  obtain ⟨hM, h1, h2, -⟩ := proposition_4_4_3_gaussian (isControllable_of_rank_G F G hG)
  exact ⟨hM, h1, h2⟩

/-! ### Countable chains and accessibility -/

/-- MT (4.8), p. 81: on a countable space, (4.5) is a Doeblin decomposition: `X` is the union of
countably many disjoint absorbing communicating classes and the remainder `D`. -/
theorem countable_absorbing_classes {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (P : Kernel X X) [IsMarkovKernel P] :
    (commClass P '' {x | IsAbsorbing P (commClass P x)}).Countable ∧
      (∀ C ∈ commClass P '' {x | IsAbsorbing P (commClass P x)}, IsAbsorbing P C) ∧
      (⋃₀ (commClass P '' {x | IsAbsorbing P (commClass P x)})) ∪ nonAbsorbingPart P = univ := by
  refine ⟨(Set.to_countable _).image _, ?_, ?_⟩
  · rintro C ⟨x, hx, rfl⟩
    exact hx
  · rw [sUnion_image]
    exact decomposition_4_5 P

/-- MT p. 86: `⇝` is not reflexive. For the chain on `Bool` that jumps to `false` and stays
there, `{true}` is not even accessible from itself. -/
theorem unifAccessible_not_refl :
    ∃ _ : IsMarkovKernel (Kernel.const Bool (Measure.dirac false)),
      ¬ UnifAccessible (Kernel.const Bool (Measure.dirac false)) {true} {true} := by
  have hM : IsMarkovKernel (Kernel.const Bool (Measure.dirac false)) := inferInstance
  refine ⟨hM, fun ⟨δ, hδ, h⟩ => ?_⟩
  have h0 : hitProb (Kernel.const Bool (Measure.dirac false)) {true} true = 0 := by
    by_contra hc
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (measurableSet_singleton true) true).1
      (pos_iff_ne_zero.2 hc)
    rw [pow_succ_apply' _ n true (measurableSet_singleton true)] at hn
    simp at hn
  have := h true (mem_singleton true)
  rw [h0] at this
  exact hδ.ne' (nonpos_iff_eq_zero.1 this)

end MeynTweedie.Irreducibility

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
content-dependent release claims are in `StorageIrreducibility`. The AR(k) explosion and
stability heuristics of p. 90 (roots of `A(z)`) are not formalised; they are the subject of the
linear-model results of §4.4.3 and Chapter 7.
-/

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

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

namespace MeynTweedie.Irreducibility

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

end MeynTweedie.Irreducibility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Content-dependent storage models (MT §4.3.2)

Meyn and Tweedie, §4.3.2, p. 88. In the content-dependent storage model the content is released
at rate `r(x)`; a store at level `y` with no further input empties after the time
`R(y) = ∫₀^y r(z)⁻¹ dz` of (2.32), and stays empty afterwards.

The model is taken, as in the `MarkovModels` project, just before inputs (the order input, then
release, `contentPreInputKernel`; see the correction to (CSM2) there): from level `x` an input
`S ∼ H_x` is added, then the store releases for an interarrival time `T ∼ G` to the level
`q([x + S]⁺, T)`. The release function `q` is abstract; the release time enters only through
`q(y, t) = 0` for `t > R(y)`. The definitions `inputKernel` and `contentPreInputKernel` are
copied from `MarkovModels.Storage`.

* `contentPreInput_zero_pos`, `contentPreInput_isPhiIrreducible` (p. 88): if `R(y) < ∞` for every
  level and `P(T > R(y)) > 0` for every `y`, the chain reaches `{0}` in one step from every state
  and is `δ₀`-irreducible.
* `contentPreInput_hitProb_zero` (p. 88): if the store never empties (`q(y, t) > 0` for `y > 0`,
  the case `R(y) = ∞`) and inputs are nonnegative, `{0}` is never reached from `x > 0`, and the
  chain is not `δ₀`-irreducible (`contentPreInput_not_isPhiIrreducible`).

The claim that with `R = ∞` one still gets `μ_Leb`-irreducibility when the interarrival times
have a density is only sketched in the book ("determined by modifying the construction") and is
not formalised. The book's remark that exact conditions for φ-irreducibility are unknown is not a
mathematical claim.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- The input kernel `y ↦ law of [y + S(y)]⁺` with `S(y) ∼ H_y` (copied from
`MarkovModels.Storage`). -/
noncomputable def inputKernel (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  (Kernel.id ×ₖ Hin).map halfLineStep

/-- The input kernel at `y` is the image of `H_y` under `s ↦ [y + s]⁺`. -/
theorem inputKernel_apply (Hin : Kernel ℝ≥0 ℝ) [IsSFiniteKernel Hin] (y : ℝ≥0) :
    inputKernel Hin y = (Hin y).map fun s => Real.toNNReal (y + s) := by
  rw [inputKernel, Kernel.map_apply _ measurable_halfLineStep, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map measurable_halfLineStep measurable_prodMk_left]
  rfl

/-- The input kernel is a Markov kernel. -/
theorem isMarkovKernel_inputKernel (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin] :
    IsMarkovKernel (inputKernel Hin) := by
  unfold inputKernel
  exact Kernel.IsMarkovKernel.map _ measurable_halfLineStep

/-- The content-dependent storage model taken just before inputs: add the input `S ∼ H_x`, then
release for an interarrival time `T ∼ G` (copied from `MarkovModels.Storage`). -/
noncomputable def contentPreInputKernel (G : Measure ℝ) (q : ℝ≥0 × ℝ → ℝ≥0)
    (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel G q ∘ₖ inputKernel Hin

/-- The content-dependent storage model is a Markov kernel. -/
theorem isMarkovKernel_contentPreInputKernel (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin] :
    IsMarkovKernel (contentPreInputKernel G q Hin) := by
  have := isMarkovKernel_recursionKernel G hq
  have := isMarkovKernel_inputKernel Hin
  unfold contentPreInputKernel
  infer_instance

/-- MT p. 88: if a store at level `y` is empty after the release time `R(y) < ∞`
(`q(y, t) = 0` for `t > R(y)`) and `P(T > R(y)) > 0` for every `y`, then from every state the
store is empty before the next input with positive probability. -/
theorem contentPreInput_zero_pos (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    (R : ℝ≥0 → ℝ) (hq0 : ∀ y t, R y < t → q (y, t) = 0) (hG : ∀ y, 0 < G (Ioi (R y)))
    (x : ℝ≥0) : 0 < contentPreInputKernel G q Hin x {0} := by
  have := isMarkovKernel_inputKernel Hin
  rw [contentPreInputKernel, Kernel.comp_apply' _ _ _ (measurableSet_singleton 0),
    lintegral_pos_iff_support (Kernel.measurable_coe _ (measurableSet_singleton 0))]
  have hsupp : Function.support (fun y => recursionKernel G q y {0}) = univ := by
    refine eq_univ_of_forall fun y => ?_
    rw [Function.mem_support, recursionKernel_apply' G hq y (measurableSet_singleton 0)]
    refine (lt_of_lt_of_le (hG y) (measure_mono fun t ht => ?_)).ne'
    exact mem_singleton_iff.2 (hq0 y t ht)
  rw [hsupp, measure_univ]
  exact one_pos

/-- MT p. 88: under the hypotheses of `contentPreInput_zero_pos` the content-dependent storage
model is `δ₀`-irreducible. -/
theorem contentPreInput_isPhiIrreducible (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    (R : ℝ≥0 → ℝ) (hq0 : ∀ y t, R y < t → q (y, t) = 0) (hG : ∀ y, 0 < G (Ioi (R y))) :
    ∃ _ : IsMarkovKernel (contentPreInputKernel G q Hin),
      IsPhiIrreducible (contentPreInputKernel G q Hin) (Measure.dirac 0) := by
  have hM := isMarkovKernel_contentPreInputKernel G hq Hin
  refine ⟨hM, (isPhiIrreducible_dirac_iff _ 0).2 fun x => ?_⟩
  refine (hitProb_pos_iff _ (measurableSet_singleton 0) x).2 ⟨0, ?_⟩
  rw [zero_add, pow_one]
  exact contentPreInput_zero_pos G hq Hin R hq0 hG x

/-- MT p. 88: if the store never empties (`q(y, t) ≠ 0` for `y ≠ 0`, the case `R(y) = ∞`) and the
inputs are nonnegative, the empty state is never reached from a positive level. -/
theorem contentPreInput_hitProb_zero (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    [IsMarkovKernel (contentPreInputKernel G q Hin)]
    (hpos : ∀ y t, y ≠ 0 → q (y, t) ≠ 0) (hin : ∀ y, Hin y (Iio 0) = 0) {x : ℝ≥0}
    (hx : x ≠ 0) : hitProb (contentPreInputKernel G q Hin) {0} x = 0 := by
  have := isMarkovKernel_inputKernel Hin
  have hm : MeasurableSet ({0}ᶜ : Set ℝ≥0) := (measurableSet_singleton 0).compl
  have hAbs : IsAbsorbing (contentPreInputKernel G q Hin) {0}ᶜ := by
    intro y hy
    rw [← prob_compl_eq_zero_iff hm, compl_compl, contentPreInputKernel,
      Kernel.comp_apply' _ _ _ (measurableSet_singleton 0)]
    refine nonpos_iff_eq_zero.1 ?_
    calc ∫⁻ z, recursionKernel G q z {0} ∂inputKernel Hin y
        ≤ ∫⁻ z, ({0} : Set ℝ≥0).indicator 1 z ∂inputKernel Hin y := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z = 0
          · subst hz
            rw [indicator_of_mem (mem_singleton 0), Pi.one_apply]
            have := isMarkovKernel_recursionKernel G hq
            exact prob_le_one
          · rw [recursionKernel_apply' G hq z (measurableSet_singleton 0)]
            have : {t | q (z, t) ∈ ({0} : Set ℝ≥0)} = ∅ :=
              eq_empty_of_forall_notMem fun t ht => hpos z t hz (mem_singleton_iff.1 ht)
            rw [this, measure_empty]
            exact zero_le
      _ = inputKernel Hin y {0} := lintegral_indicator_one (measurableSet_singleton 0)
      _ ≤ 0 := by
          rw [inputKernel_apply, Measure.map_apply (f := fun s => Real.toNNReal (y + s))
            (measurable_halfLineStep.comp measurable_prodMk_left) (measurableSet_singleton 0),
            ← hin y]
          refine measure_mono fun s hs => ?_
          simp only [mem_preimage, mem_singleton_iff, Real.toNNReal_eq_zero] at hs
          have : (0 : ℝ) < y := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hy)
          exact mem_Iio.2 (by change (y : ℝ) + s ≤ 0 at hs; linarith)
  exact hAbs.hitProb_eq_zero hm (Set.disjoint_left.2 fun z hz h0 => hz h0) hx

/-- MT p. 88: with `R = ∞` (the store never empties) and nonnegative inputs, the content-dependent
storage model is not `δ₀`-irreducible. -/
theorem contentPreInput_not_isPhiIrreducible (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    [IsMarkovKernel (contentPreInputKernel G q Hin)]
    (hpos : ∀ y t, y ≠ 0 → q (y, t) ≠ 0) (hin : ∀ y, Hin y (Iio 0) = 0) :
    ¬ IsPhiIrreducible (contentPreInputKernel G q Hin) (Measure.dirac 0) := by
  rw [isPhiIrreducible_dirac_iff]
  intro h
  have := h 1
  rw [contentPreInput_hitProb_zero G hq Hin hpos hin one_ne_zero] at this
  exact lt_irrefl _ this

end MeynTweedie.Irreducibility

set_option linter.style.longLine false
#print axioms MeynTweedie.Irreducibility.trajKernel
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_trajKernel
#print axioms MeynTweedie.Irreducibility.pathKernel
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_pathKernel
#print axioms MeynTweedie.Irreducibility.pathMeasure
#print axioms MeynTweedie.Irreducibility.isProbabilityMeasure_pathMeasure
#print axioms MeynTweedie.Irreducibility.pathMeasure_eq_comp
#print axioms MeynTweedie.Irreducibility.pathMeasure_dirac
#print axioms MeynTweedie.Irreducibility.pathKernel_map_zero
#print axioms MeynTweedie.Irreducibility.pathKernel_zero_mem
#print axioms MeynTweedie.Irreducibility.ae_pathKernel_zero
#print axioms MeynTweedie.Irreducibility.pathMeasure_inter_zero
#print axioms MeynTweedie.Irreducibility.pathMeasure_map_zero
#print axioms MeynTweedie.Irreducibility.natFilt
#print axioms MeynTweedie.Irreducibility.measurable_coord_natFilt
#print axioms MeynTweedie.Irreducibility.measurableSet_coord_natFilt
#print axioms MeynTweedie.Irreducibility.setLIntegral_succ
#print axioms MeynTweedie.Irreducibility.cylFn
#print axioms MeynTweedie.Irreducibility.measurable_cylFn
#print axioms MeynTweedie.Irreducibility.boxSet
#print axioms MeynTweedie.Irreducibility.measurableSet_boxSet
#print axioms MeynTweedie.Irreducibility.measure_inter_shift_box
#print axioms MeynTweedie.Irreducibility.pathKernel_boxSet
#print axioms MeynTweedie.Irreducibility.pathMeasure_boxSet
#print axioms MeynTweedie.Irreducibility.IsMarkovChain
#print axioms MeynTweedie.Irreducibility.IsMarkovChain.mk
#print axioms MeynTweedie.Irreducibility.IsMarkovChain.measurable
#print axioms MeynTweedie.Irreducibility.IsMarkovChain.fdd
#print axioms MeynTweedie.Irreducibility.theorem_3_4_1
#print axioms MeynTweedie.Irreducibility.generateFrom_boxSets
#print axioms MeynTweedie.Irreducibility.isPiSystem_boxSets
#print axioms MeynTweedie.Irreducibility.theorem_3_4_1_unique
#print axioms MeynTweedie.Irreducibility.law_eq_pathMeasure
#print axioms MeynTweedie.Irreducibility.IsSubstochasticKernel
#print axioms MeynTweedie.Irreducibility.isSubstochasticKernel_of_markov
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_pow
#print axioms MeynTweedie.Irreducibility.pow_zero_apply
#print axioms MeynTweedie.Irreducibility.pow_succ_apply
#print axioms MeynTweedie.Irreducibility.pow_succ_apply'
#print axioms MeynTweedie.Irreducibility.theorem_3_4_2
#print axioms MeynTweedie.Irreducibility.pow_add_eq
#print axioms MeynTweedie.Irreducibility.skeleton
#print axioms MeynTweedie.Irreducibility.skeleton_pow
#print axioms MeynTweedie.Irreducibility.sampledKernel
#print axioms MeynTweedie.Irreducibility.sampledKernel_apply
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_sampledKernel
#print axioms MeynTweedie.Irreducibility.resolvent
#print axioms MeynTweedie.Irreducibility.resolvent_apply
#print axioms MeynTweedie.Irreducibility.tsum_geometric_weights
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_resolvent
#print axioms MeynTweedie.Irreducibility.kfun
#print axioms MeynTweedie.Irreducibility.measurable_kfun
#print axioms MeynTweedie.Irreducibility.kfun_indicator
#print axioms MeynTweedie.Irreducibility.kfun_one
#print axioms MeynTweedie.Irreducibility.kfun_mono
#print axioms MeynTweedie.Irreducibility.kfun_add
#print axioms MeynTweedie.Irreducibility.kfun_const_mul
#print axioms MeynTweedie.Irreducibility.kfun_comp
#print axioms MeynTweedie.Irreducibility.kfun_pow_succ
#print axioms MeynTweedie.Irreducibility.measure_kernel_apply
#print axioms MeynTweedie.Irreducibility.measure_kernel_assoc
#print axioms MeynTweedie.Irreducibility.lintegral_kfun
#print axioms MeynTweedie.Irreducibility.isProbabilityMeasure_measure_kernel
#print axioms MeynTweedie.Irreducibility.dirac_kernel
#print axioms MeynTweedie.Irreducibility.kfunR
#print axioms MeynTweedie.Irreducibility.measurable_kfunR
#print axioms MeynTweedie.Irreducibility.abs_kfunR_le
#print axioms MeynTweedie.Irreducibility.indKernel
#print axioms MeynTweedie.Irreducibility.indKernel_apply
#print axioms MeynTweedie.Irreducibility.comp_indKernel_apply
#print axioms MeynTweedie.Irreducibility.isSubstochasticKernel_comp_indKernel
#print axioms MeynTweedie.Irreducibility.potKernel
#print axioms MeynTweedie.Irreducibility.potKernel_apply
#print axioms MeynTweedie.Irreducibility.shift
#print axioms MeynTweedie.Irreducibility.measurable_shift
#print axioms MeynTweedie.Irreducibility.shift_zero
#print axioms MeynTweedie.Irreducibility.shift_shift
#print axioms MeynTweedie.Irreducibility.shift_apply
#print axioms MeynTweedie.Irreducibility.integral_measure_comp
#print axioms MeynTweedie.Irreducibility.pathMeasure_map_coord
#print axioms MeynTweedie.Irreducibility.pathKernel_map_coord
#print axioms MeynTweedie.Irreducibility.pathKernel_coord_mem
#print axioms MeynTweedie.Irreducibility.pathKernel_coord_chapmanKolmogorov
#print axioms MeynTweedie.Irreducibility.markov_measure
#print axioms MeynTweedie.Irreducibility.markov_lintegral
#print axioms MeynTweedie.Irreducibility.markov_lintegral_mul
#print axioms MeynTweedie.Irreducibility.markov_lintegral_univ
#print axioms MeynTweedie.Irreducibility.markov_setIntegral
#print axioms MeynTweedie.Irreducibility.stronglyMeasurable_expect_coord
#print axioms MeynTweedie.Irreducibility.integrable_expect_coord
#print axioms MeynTweedie.Irreducibility.markov_property
#print axioms MeynTweedie.Irreducibility.integrable_shift_of_bdd
#print axioms MeynTweedie.Irreducibility.markov_property_bdd
#print axioms MeynTweedie.Irreducibility.proposition_3_4_3
#print axioms MeynTweedie.Irreducibility.isMarkovChain_of_step
#print axioms MeynTweedie.Irreducibility.skeletonFilt
#print axioms MeynTweedie.Irreducibility.skeleton_isMarkovChain
#print axioms MeynTweedie.Irreducibility.iSup_natFilt
#print axioms MeynTweedie.Irreducibility.setOf_le_eq_biUnion
#print axioms MeynTweedie.Irreducibility.setOf_ne_top_eq_iUnion
#print axioms MeynTweedie.Irreducibility.measurableSet_ne_top
#print axioms MeynTweedie.Irreducibility.measurableSet_stoppedField_iff
#print axioms MeynTweedie.Irreducibility.measurableSet_stoppedField_ne_top
#print axioms MeynTweedie.Irreducibility.stoppedState
#print axioms MeynTweedie.Irreducibility.shiftAt
#print axioms MeynTweedie.Irreducibility.stoppedState_of_eq
#print axioms MeynTweedie.Irreducibility.shiftAt_of_eq
#print axioms MeynTweedie.Irreducibility.measurable_of_stopping_pieces
#print axioms MeynTweedie.Irreducibility.measurable_stoppedState
#print axioms MeynTweedie.Irreducibility.measurable_shiftAt
#print axioms MeynTweedie.Irreducibility.measurable_stoppedField_indicator
#print axioms MeynTweedie.Irreducibility.inter_ne_top_eq_iUnion
#print axioms MeynTweedie.Irreducibility.pairwise_disjoint_inter_eq
#print axioms MeynTweedie.Irreducibility.strong_markov_lintegral
#print axioms MeynTweedie.Irreducibility.strong_markov_lintegral_mul
#print axioms MeynTweedie.Irreducibility.strong_markov_measure
#print axioms MeynTweedie.Irreducibility.strong_markov_setIntegral
#print axioms MeynTweedie.Irreducibility.strong_markov_property
#print axioms MeynTweedie.Irreducibility.StrongMarkovProperty
#print axioms MeynTweedie.Irreducibility.proposition_3_4_6
#print axioms MeynTweedie.Irreducibility.occTime
#print axioms MeynTweedie.Irreducibility.firstReturn
#print axioms MeynTweedie.Irreducibility.firstHit
#print axioms MeynTweedie.Irreducibility.returnTimeK
#print axioms MeynTweedie.Irreducibility.hitProb
#print axioms MeynTweedie.Irreducibility.returnTimeK_one
#print axioms MeynTweedie.Irreducibility.returnTimeK_succ_of_eq
#print axioms MeynTweedie.Irreducibility.returnTimeK_succ_of_top
#print axioms MeynTweedie.Irreducibility.firstReturn_ne_top_iff
#print axioms MeynTweedie.Irreducibility.le_firstReturn_iff
#print axioms MeynTweedie.Irreducibility.one_le_firstReturn
#print axioms MeynTweedie.Irreducibility.firstReturn_eq_iff
#print axioms MeynTweedie.Irreducibility.le_firstReturn_succ_iff
#print axioms MeynTweedie.Irreducibility.firstHit_eq_zero_iff
#print axioms MeynTweedie.Irreducibility.firstHit_eq_firstReturn
#print axioms MeynTweedie.Irreducibility.adapted_coord
#print axioms MeynTweedie.Irreducibility.proposition_3_4_4
#print axioms MeynTweedie.Irreducibility.isStoppingTime_returnTimeK
#print axioms MeynTweedie.Irreducibility.measurableSet_firstReturn_ne_top
#print axioms MeynTweedie.Irreducibility.measurableSet_firstReturn_eq
#print axioms MeynTweedie.Irreducibility.measurableSet_le_firstReturn
#print axioms MeynTweedie.Irreducibility.measurable_occTime
#print axioms MeynTweedie.Irreducibility.measurable_hitProb
#print axioms MeynTweedie.Irreducibility.potKernel_eq_lintegral_occTime
#print axioms MeynTweedie.Irreducibility.pathKernel_first_step
#print axioms MeynTweedie.Irreducibility.tabooKernel
#print axioms MeynTweedie.Irreducibility.comp_indKernel_eq_restrict
#print axioms MeynTweedie.Irreducibility.tabooKernel_zero
#print axioms MeynTweedie.Irreducibility.tabooKernel_succ_apply
#print axioms MeynTweedie.Irreducibility.tabooProb
#print axioms MeynTweedie.Irreducibility.tabooProb_one
#print axioms MeynTweedie.Irreducibility.tabooProb_succ
#print axioms MeynTweedie.Irreducibility.tabooProb_eq_tabooKernel
#print axioms MeynTweedie.Irreducibility.firstReturn_eq_tabooProb
#print axioms MeynTweedie.Irreducibility.proposition_3_4_5_i
#print axioms MeynTweedie.Irreducibility.proposition_3_4_5_i_succ
#print axioms MeynTweedie.Irreducibility.firstReturn_eq_tabooKernel
#print axioms MeynTweedie.Irreducibility.nestedTaboo
#print axioms MeynTweedie.Irreducibility.firstReturn_eq_nestedTaboo
#print axioms MeynTweedie.Irreducibility.proposition_3_4_5_ii
#print axioms MeynTweedie.Irreducibility.hitProb_eq_tsum
#print axioms MeynTweedie.Irreducibility.hitProb_first_step
#print axioms MeynTweedie.Irreducibility.tabooPotKernel
#print axioms MeynTweedie.Irreducibility.tabooPotKernel_apply
#print axioms MeynTweedie.Irreducibility.tabooPotKernel_self
#print axioms MeynTweedie.Irreducibility.IsTransitionMatrix
#print axioms MeynTweedie.Irreducibility.matPow
#print axioms MeynTweedie.Irreducibility.matKernel
#print axioms MeynTweedie.Irreducibility.matKernel_singleton
#print axioms MeynTweedie.Irreducibility.matKernel_apply
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_matKernel
#print axioms MeynTweedie.Irreducibility.lintegral_matKernel
#print axioms MeynTweedie.Irreducibility.matKernel_pow_singleton
#print axioms MeynTweedie.Irreducibility.matKernel_pow_apply
#print axioms MeynTweedie.Irreducibility.isTransitionMatrix_matPow
#print axioms MeynTweedie.Irreducibility.cylFn_singletons
#print axioms MeynTweedie.Irreducibility.theorem_3_2_1_fdd
#print axioms MeynTweedie.Irreducibility.IsMarkovChain.fdd_points
#print axioms MeynTweedie.Irreducibility.theorem_3_2_1
#print axioms MeynTweedie.Irreducibility.pathMeasure_inter_initial
#print axioms MeynTweedie.Irreducibility.pathMeasure_initial_coord
#print axioms MeynTweedie.Irreducibility.firstReturn_ne_top_eq_iUnion
#print axioms MeynTweedie.Irreducibility.pow_le_hitProb
#print axioms MeynTweedie.Irreducibility.hitProb_pos_iff
#print axioms MeynTweedie.Irreducibility.hitProb_le_one
#print axioms MeynTweedie.Irreducibility.potKernel_pos_iff
#print axioms MeynTweedie.Irreducibility.pow_add_pos_iff
#print axioms MeynTweedie.Irreducibility.measurableSet_pow_pos
#print axioms MeynTweedie.Irreducibility.IsAbsorbing
#print axioms MeynTweedie.Irreducibility.IsAbsorbing.pow_apply
#print axioms MeynTweedie.Irreducibility.IsAbsorbing.pow_compl
#print axioms MeynTweedie.Irreducibility.IsAbsorbing.hitProb_compl
#print axioms MeynTweedie.Irreducibility.IsAbsorbing.hitProb_eq_zero
#print axioms MeynTweedie.Irreducibility.restrictKernel
#print axioms MeynTweedie.Irreducibility.restrictKernel_apply
#print axioms MeynTweedie.Irreducibility.restrictKernel_apply_eq
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_restrictKernel
#print axioms MeynTweedie.Irreducibility.lintegral_restrictKernel
#print axioms MeynTweedie.Irreducibility.restrictKernel_pow_apply
#print axioms MeynTweedie.Irreducibility.Leads
#print axioms MeynTweedie.Irreducibility.leads_iff_exists_pow
#print axioms MeynTweedie.Irreducibility.pow_add_singleton_ge
#print axioms MeynTweedie.Irreducibility.Leads.trans
#print axioms MeynTweedie.Irreducibility.Leads.refl
#print axioms MeynTweedie.Irreducibility.Communicates
#print axioms MeynTweedie.Irreducibility.proposition_4_1_1
#print axioms MeynTweedie.Irreducibility.commClass
#print axioms MeynTweedie.Irreducibility.mem_commClass_self
#print axioms MeynTweedie.Irreducibility.iUnion_commClass
#print axioms MeynTweedie.Irreducibility.commClass_eq_or_disjoint
#print axioms MeynTweedie.Irreducibility.commClass_eq_iff
#print axioms MeynTweedie.Irreducibility.IsIrreducibleChain
#print axioms MeynTweedie.Irreducibility.isIrreducibleChain_iff
#print axioms MeynTweedie.Irreducibility.nonAbsorbingPart
#print axioms MeynTweedie.Irreducibility.commClass_subset_nonAbsorbingPart
#print axioms MeynTweedie.Irreducibility.decomposition_4_5
#print axioms MeynTweedie.Irreducibility.decomposition_4_5_disjoint
#print axioms MeynTweedie.Irreducibility.measurableSet_of_countable
#print axioms MeynTweedie.Irreducibility.exists_singleton_pos_of_pos
#print axioms MeynTweedie.Irreducibility.not_isAbsorbing_commClass_iff
#print axioms MeynTweedie.Irreducibility.proposition_4_1_2
#print axioms MeynTweedie.Irreducibility.IsPhiIrreducible
#print axioms MeynTweedie.Irreducibility.resolventHalf
#print axioms MeynTweedie.Irreducibility.resolventHalf_apply
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_resolventHalf
#print axioms MeynTweedie.Irreducibility.resolventHalf_pos_iff
#print axioms MeynTweedie.Irreducibility.resolventHalf_eq_zero_iff
#print axioms MeynTweedie.Irreducibility.resolventHalf_equiv
#print axioms MeynTweedie.Irreducibility.hitProb_pos_of_compl
#print axioms MeynTweedie.Irreducibility.proposition_4_2_1
#print axioms MeynTweedie.Irreducibility.IsPhiIrreducible.mono
#print axioms MeynTweedie.Irreducibility.IsPhiIrreducible.restrict
#print axioms MeynTweedie.Irreducibility.isPhiIrreducible_zero
#print axioms MeynTweedie.Irreducibility.isPhiIrreducible_dirac_iff
#print axioms MeynTweedie.Irreducibility.isPhiIrreducible_dirac_of_leads
#print axioms MeynTweedie.Irreducibility.isIrreducibleChain_iff_count
#print axioms MeynTweedie.Irreducibility.exists_measure_pos_of_iUnion
#print axioms MeynTweedie.Irreducibility.setOf_resolventHalf_pos
#print axioms MeynTweedie.Irreducibility.setOf_hitProb_pos
#print axioms MeynTweedie.Irreducibility.measurableSet_hitProb_pos
#print axioms MeynTweedie.Irreducibility.exists_finite_equiv_of_ac
#print axioms MeynTweedie.Irreducibility.exists_prob_equiv
#print axioms MeynTweedie.Irreducibility.maxIrrMeasure
#print axioms MeynTweedie.Irreducibility.maxIrrMeasure_apply
#print axioms MeynTweedie.Irreducibility.maxIrrMeasure_univ
#print axioms MeynTweedie.Irreducibility.isProbabilityMeasure_maxIrrMeasure
#print axioms MeynTweedie.Irreducibility.isPhiIrreducible_maxIrrMeasure
#print axioms MeynTweedie.Irreducibility.ac_maxIrrMeasure
#print axioms MeynTweedie.Irreducibility.maxIrrMeasure_hitSet_null
#print axioms MeynTweedie.Irreducibility.maxIrrMeasure_comp_pow_le
#print axioms MeynTweedie.Irreducibility.IsMaximalIrreducibility
#print axioms MeynTweedie.Irreducibility.isMaximalIrreducibility_maxIrrMeasure
#print axioms MeynTweedie.Irreducibility.IsMaximalIrreducibility.isPhiIrreducible_iff
#print axioms MeynTweedie.Irreducibility.IsMaximalIrreducibility.equiv
#print axioms MeynTweedie.Irreducibility.IsMaximalIrreducibility.of_equiv
#print axioms MeynTweedie.Irreducibility.IsMaximalIrreducibility.hitSet_null
#print axioms MeynTweedie.Irreducibility.proposition_4_2_2
#print axioms MeynTweedie.Irreducibility.proposition_4_2_2_maximal
#print axioms MeynTweedie.Irreducibility.proposition_4_2_2_zero_counterexample
#print axioms MeynTweedie.Irreducibility.posSets
#print axioms MeynTweedie.Irreducibility.posSets_eq_of_maximal
#print axioms MeynTweedie.Irreducibility.IsFull
#print axioms MeynTweedie.Irreducibility.proposition_4_2_3_i
#print axioms MeynTweedie.Irreducibility.proposition_4_2_3_i_counterexample
#print axioms MeynTweedie.Irreducibility.proposition_4_2_3_ii
#print axioms MeynTweedie.Irreducibility.theorem_4_0_1
#print axioms MeynTweedie.Irreducibility.theorem_4_0_1_unique
#print axioms MeynTweedie.Irreducibility.IsAbsorbingIrreducibleSet
#print axioms MeynTweedie.Irreducibility.proposition_4_2_4
#print axioms MeynTweedie.Irreducibility.proposition_4_2_4_nonzero
#print axioms MeynTweedie.Irreducibility.isMaximalIrreducibility_count
#print axioms MeynTweedie.Irreducibility.IsAccessibleFrom
#print axioms MeynTweedie.Irreducibility.UnifAccessible
#print axioms MeynTweedie.Irreducibility.UnifAccessible.isAccessibleFrom
#print axioms MeynTweedie.Irreducibility.stoppedState_firstReturn_mem
#print axioms MeynTweedie.Irreducibility.hitProb_ge_mul
#print axioms MeynTweedie.Irreducibility.lemma_4_2_5
#print axioms MeynTweedie.Irreducibility.hitSet
#print axioms MeynTweedie.Irreducibility.hitSetLevel
#print axioms MeynTweedie.Irreducibility.noHitSet
#print axioms MeynTweedie.Irreducibility.noHitSet_eq_compl
#print axioms MeynTweedie.Irreducibility.measurableSet_hitSetLevel
#print axioms MeynTweedie.Irreducibility.lemma_4_2_6_bound
#print axioms MeynTweedie.Irreducibility.lemma_4_2_6
#print axioms MeynTweedie.Irreducibility.countable_cover_unifAccessible
#print axioms MeynTweedie.Irreducibility.fwdRecMatrix
#print axioms MeynTweedie.Irreducibility.isTransitionMatrix_fwdRecMatrix
#print axioms MeynTweedie.Irreducibility.ptail
#print axioms MeynTweedie.Irreducibility.ptail_eq
#print axioms MeynTweedie.Irreducibility.ptail_ne_zero_iff
#print axioms MeynTweedie.Irreducibility.bwdRecMatrix
#print axioms MeynTweedie.Irreducibility.bwdRecMatrix_rowSum
#print axioms MeynTweedie.Irreducibility.ptail_ne_zero_of_bwdRecMatrix
#print axioms MeynTweedie.Irreducibility.bwdRecMatrix_zero
#print axioms MeynTweedie.Irreducibility.halfHalf
#print axioms MeynTweedie.Irreducibility.bwdRecMatrix_display_counterexample
#print axioms MeynTweedie.Irreducibility.rwMatrix
#print axioms MeynTweedie.Irreducibility.isTransitionMatrix_rwMatrix
#print axioms MeynTweedie.Irreducibility.rwMatrix_translate
#print axioms MeynTweedie.Irreducibility.rw_step_law
#print axioms MeynTweedie.Irreducibility.rwhlMatrix
#print axioms MeynTweedie.Irreducibility.isTransitionMatrix_rwhlMatrix
#print axioms MeynTweedie.Irreducibility.storage_increment_singleton
#print axioms MeynTweedie.Irreducibility.storage_increment_counterexample
#print axioms MeynTweedie.Irreducibility.poissonWeight
#print axioms MeynTweedie.Irreducibility.poissonWeight_eq
#print axioms MeynTweedie.Irreducibility.tsum_poissonWeight
#print axioms MeynTweedie.Irreducibility.giM1Matrix
#print axioms MeynTweedie.Irreducibility.giM1Increment
#print axioms MeynTweedie.Irreducibility.giM1Matrix_eq_rwhl
#print axioms MeynTweedie.Irreducibility.tsum_giM1Increment
#print axioms MeynTweedie.Irreducibility.proposition_3_3_1
#print axioms MeynTweedie.Irreducibility.mG1Matrix
#print axioms MeynTweedie.Irreducibility.isTransitionMatrix_mG1Matrix
#print axioms MeynTweedie.Irreducibility.proposition_3_3_2
#print axioms MeynTweedie.Irreducibility.arMatrix
#print axioms MeynTweedie.Irreducibility.proposition_3_3_3
#print axioms MeynTweedie.Irreducibility.matKernel_pow_one_singleton
#print axioms MeynTweedie.Irreducibility.leads_of_pos
#print axioms MeynTweedie.Irreducibility.isAbsorbing_matKernel_iff
#print axioms MeynTweedie.Irreducibility.IsAbsorbing.mem_of_leads
#print axioms MeynTweedie.Irreducibility.Leads.step
#print axioms MeynTweedie.Irreducibility.rwhl_zero_ge
#print axioms MeynTweedie.Irreducibility.rwhl_pow_zero_ge
#print axioms MeynTweedie.Irreducibility.rwhl_hitProb_zero_pos
#print axioms MeynTweedie.Irreducibility.rwhl_hitProb_zero_eq_zero
#print axioms MeynTweedie.Irreducibility.diracZeroInt
#print axioms MeynTweedie.Irreducibility.rwhl_dichotomy_counterexample
#print axioms MeynTweedie.Irreducibility.rwhl_even_increments
#print axioms MeynTweedie.Irreducibility.fwdRec_isAbsorbing
#print axioms MeynTweedie.Irreducibility.fwdRec_leads_down
#print axioms MeynTweedie.Irreducibility.fwdRec_pow_down
#print axioms MeynTweedie.Irreducibility.fwdRec_communicates
#print axioms MeynTweedie.Irreducibility.giM1_isIrreducibleChain
#print axioms MeynTweedie.Irreducibility.poissonWeight_ne_zero
#print axioms MeynTweedie.Irreducibility.giM1_poisson_isIrreducibleChain
#print axioms MeynTweedie.Irreducibility.poissonWeight_dirac_zero
#print axioms MeynTweedie.Irreducibility.giM1_dirac_counterexample
#print axioms MeynTweedie.Irreducibility.mG1_isIrreducibleChain
#print axioms MeynTweedie.Irreducibility.mG1_poisson_isIrreducibleChain
#print axioms MeynTweedie.Irreducibility.mG1_dirac_counterexample
#print axioms MeynTweedie.Irreducibility.rwSupportGroup
#print axioms MeynTweedie.Irreducibility.rw_closure_eq_zmultiples
#print axioms MeynTweedie.Irreducibility.rw_coset_isAbsorbing
#print axioms MeynTweedie.Irreducibility.rw_leads_add
#print axioms MeynTweedie.Irreducibility.rw_monoid_eq_group
#print axioms MeynTweedie.Irreducibility.rw_commClass_eq
#print axioms MeynTweedie.Irreducibility.rw_commClass_finite
#print axioms MeynTweedie.Irreducibility.ratClass
#print axioms MeynTweedie.Irreducibility.ratWalk_isAbsorbing
#print axioms MeynTweedie.Irreducibility.ratWalk_commClass_eq
#print axioms MeynTweedie.Irreducibility.ratWalk_commClass_infinite
#print axioms MeynTweedie.Irreducibility.controlMap
#print axioms MeynTweedie.Irreducibility.controlMap_zero
#print axioms MeynTweedie.Irreducibility.controlMap_succ
#print axioms MeynTweedie.Irreducibility.controlMap_one
#print axioms MeynTweedie.Irreducibility.controlMap_succ_cons
#print axioms MeynTweedie.Irreducibility.orbit
#print axioms MeynTweedie.Irreducibility.orbit_zero
#print axioms MeynTweedie.Irreducibility.orbit_succ
#print axioms MeynTweedie.Irreducibility.orbit_eq_controlMap
#print axioms MeynTweedie.Irreducibility.recursionKernel
#print axioms MeynTweedie.Irreducibility.recursionKernel_apply
#print axioms MeynTweedie.Irreducibility.recursionKernel_apply'
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_recursionKernel
#print axioms MeynTweedie.Irreducibility.recursionKernel_comp_noise
#print axioms MeynTweedie.Irreducibility.recursionKernel_const_noise
#print axioms MeynTweedie.Irreducibility.measurable_controlMap
#print axioms MeynTweedie.Irreducibility.measurable_controlMap_right
#print axioms MeynTweedie.Irreducibility.recursionKernel_pow_apply
#print axioms MeynTweedie.Irreducibility.recursionKernel_pow_apply'
#print axioms MeynTweedie.Irreducibility.infinitePi_map_shift
#print axioms MeynTweedie.Irreducibility.law_orbit
#print axioms MeynTweedie.Irreducibility.randomWalkKernel
#print axioms MeynTweedie.Irreducibility.measurable_add_step
#print axioms MeynTweedie.Irreducibility.randomWalkKernel_apply
#print axioms MeynTweedie.Irreducibility.randomWalkKernel_apply'
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_randomWalkKernel
#print axioms MeynTweedie.Irreducibility.randomWalkKernel_real_apply_Iic
#print axioms MeynTweedie.Irreducibility.controlMap_add
#print axioms MeynTweedie.Irreducibility.orbit_randomWalk
#print axioms MeynTweedie.Irreducibility.convPow
#print axioms MeynTweedie.Irreducibility.measurable_sum_fin
#print axioms MeynTweedie.Irreducibility.randomWalkKernel_pow_apply
#print axioms MeynTweedie.Irreducibility.IsSpreadOut
#print axioms MeynTweedie.Irreducibility.halfLineStep
#print axioms MeynTweedie.Irreducibility.measurable_halfLineStep
#print axioms MeynTweedie.Irreducibility.halfLineWalkKernel
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_halfLineWalkKernel
#print axioms MeynTweedie.Irreducibility.halfLineWalkKernel_apply'
#print axioms MeynTweedie.Irreducibility.halfLineWalkKernel_apply_zero
#print axioms MeynTweedie.Irreducibility.halfLineWalkKernel_apply_Iic
#print axioms MeynTweedie.Irreducibility.halfLineWalkKernel_apply_Ioi
#print axioms MeynTweedie.Irreducibility.halfLineOrbit
#print axioms MeynTweedie.Irreducibility.partialSum
#print axioms MeynTweedie.Irreducibility.halfLineOrbit_succ_coe
#print axioms MeynTweedie.Irreducibility.halfLineOrbit_eq_of_nonneg
#print axioms MeynTweedie.Irreducibility.halfLineOrbit_succ_of_eq_zero
#print axioms MeynTweedie.Irreducibility.halfLineOrbit_eq_lindley
#print axioms MeynTweedie.Irreducibility.linear_controlMap
#print axioms MeynTweedie.Irreducibility.orbit_linear
#print axioms MeynTweedie.Irreducibility.lssKernel
#print axioms MeynTweedie.Irreducibility.measurable_lssStep
#print axioms MeynTweedie.Irreducibility.lssKernel_apply'
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_lssKernel
#print axioms MeynTweedie.Irreducibility.clm_pow_apply
#print axioms MeynTweedie.Irreducibility.orbit_lss
#print axioms MeynTweedie.Irreducibility.lssKernel_pow_apply
#print axioms MeynTweedie.Irreducibility.measurable_mulVec
#print axioms MeynTweedie.Irreducibility.lssMatrixKernel
#print axioms MeynTweedie.Irreducibility.measurable_lssMatrixStep
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_lssMatrixKernel
#print axioms MeynTweedie.Irreducibility.mulVecHom
#print axioms MeynTweedie.Irreducibility.coe_mulVecHom
#print axioms MeynTweedie.Irreducibility.matrix_pow_mulVec
#print axioms MeynTweedie.Irreducibility.orbit_lssMatrix
#print axioms MeynTweedie.Irreducibility.lssMatrixKernel_pow_apply
#print axioms MeynTweedie.Irreducibility.lcmTrajectory
#print axioms MeynTweedie.Irreducibility.IsControllable
#print axioms MeynTweedie.Irreducibility.lcmTrajectory_eq
#print axioms MeynTweedie.Irreducibility.ar1Kernel
#print axioms MeynTweedie.Irreducibility.measurable_ar1Step
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_ar1Kernel
#print axioms MeynTweedie.Irreducibility.ar1Kernel_apply'
#print axioms MeynTweedie.Irreducibility.ar1Kernel_eq_lssKernel
#print axioms MeynTweedie.Irreducibility.ar1Kernel_one
#print axioms MeynTweedie.Irreducibility.randomWalkKernel_eq_lssKernel
#print axioms MeynTweedie.Irreducibility.orbit_ar1
#print axioms MeynTweedie.Irreducibility.shiftIn
#print axioms MeynTweedie.Irreducibility.shiftIn_apply_zero
#print axioms MeynTweedie.Irreducibility.shiftIn_apply_succ
#print axioms MeynTweedie.Irreducibility.measurable_shiftIn
#print axioms MeynTweedie.Irreducibility.shiftIn_add
#print axioms MeynTweedie.Irreducibility.arStep
#print axioms MeynTweedie.Irreducibility.measurable_arStep
#print axioms MeynTweedie.Irreducibility.arKernel
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_arKernel
#print axioms MeynTweedie.Irreducibility.companion
#print axioms MeynTweedie.Irreducibility.firstUnit
#print axioms MeynTweedie.Irreducibility.arStep_eq_companion
#print axioms MeynTweedie.Irreducibility.arKernel_eq_lssMatrixKernel
#print axioms MeynTweedie.Irreducibility.arVec
#print axioms MeynTweedie.Irreducibility.arVec_succ
#print axioms MeynTweedie.Irreducibility.armaStep
#print axioms MeynTweedie.Irreducibility.measurable_armaStep
#print axioms MeynTweedie.Irreducibility.armaKernel
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_armaKernel
#print axioms MeynTweedie.Irreducibility.arma_of_ar
#print axioms MeynTweedie.Irreducibility.fig11F
#print axioms MeynTweedie.Irreducibility.fig11F_eq
#print axioms MeynTweedie.Irreducibility.sqNorm2
#print axioms MeynTweedie.Irreducibility.fig11_sqNorm_mulVec
#print axioms MeynTweedie.Irreducibility.fig11_tendsto_zero
#print axioms MeynTweedie.Irreducibility.fig11_inv_tendsto_atTop
#print axioms MeynTweedie.Irreducibility.ctrbMap
#print axioms MeynTweedie.Irreducibility.ctrbMap_apply
#print axioms MeynTweedie.Irreducibility.ctrbMatrix
#print axioms MeynTweedie.Irreducibility.ctrbMatrix_mulVec
#print axioms MeynTweedie.Irreducibility.range_ctrbMatrix
#print axioms MeynTweedie.Irreducibility.rank_ctrbMatrix_eq_iff
#print axioms MeynTweedie.Irreducibility.lcmTrajectory_eq_ctrbMap
#print axioms MeynTweedie.Irreducibility.IsCtrbRank
#print axioms MeynTweedie.Irreducibility.reach_of_range_eq_top
#print axioms MeynTweedie.Irreducibility.proposition_4_4_1
#print axioms MeynTweedie.Irreducibility.pow_mul_mulVec_mem_range
#print axioms MeynTweedie.Irreducibility.pow_dim_eq_sum
#print axioms MeynTweedie.Irreducibility.pow_mul_mulVec_mem_range_n
#print axioms MeynTweedie.Irreducibility.range_ctrbMap_le_n
#print axioms MeynTweedie.Irreducibility.range_ctrbMap_mono
#print axioms MeynTweedie.Irreducibility.isControllable_iff_rank
#print axioms MeynTweedie.Irreducibility.isControllable_iff_exists_rank
#print axioms MeynTweedie.Irreducibility.range_ctrbMap_eq_top
#print axioms MeynTweedie.Irreducibility.firstUnit_mulVec
#print axioms MeynTweedie.Irreducibility.companion_mulVec_of_ne_zero
#print axioms MeynTweedie.Irreducibility.companion_mulVec_zero
#print axioms MeynTweedie.Irreducibility.firstVec
#print axioms MeynTweedie.Irreducibility.companion_pow_firstUnit_triangular
#print axioms MeynTweedie.Irreducibility.companionEta
#print axioms MeynTweedie.Irreducibility.companion_eta_rec
#print axioms MeynTweedie.Irreducibility.proposition_4_4_2
#print axioms MeynTweedie.Irreducibility.gramian
#print axioms MeynTweedie.Irreducibility.gramian_eq
#print axioms MeynTweedie.Irreducibility.rank_gramian
#print axioms MeynTweedie.Irreducibility.isControllable_iff_gramian
#print axioms MeynTweedie.Irreducibility.ctrbSubspace_absorbing_step
#print axioms MeynTweedie.Irreducibility.gramian_series_counterexample
#print axioms MeynTweedie.Irreducibility.pi_absolutelyContinuous
#print axioms MeynTweedie.Irreducibility.measurable_ctrbMap
#print axioms MeynTweedie.Irreducibility.ctrbLaw
#print axioms MeynTweedie.Irreducibility.lss_pow_eq
#print axioms MeynTweedie.Irreducibility.ctrbLaw_equiv
#print axioms MeynTweedie.Irreducibility.lss_pow_equiv
#print axioms MeynTweedie.Irreducibility.lss_isPhiIrreducible
#print axioms MeynTweedie.Irreducibility.lss_isMaximalIrreducibility
#print axioms MeynTweedie.Irreducibility.translateCM
#print axioms MeynTweedie.Irreducibility.lss_lowerSemicontinuous
#print axioms MeynTweedie.Irreducibility.lss_unifAccessible
#print axioms MeynTweedie.Irreducibility.proposition_4_4_3
#print axioms MeynTweedie.Irreducibility.stdGaussian_equiv_volume
#print axioms MeynTweedie.Irreducibility.proposition_4_4_3_gaussian
#print axioms MeynTweedie.Irreducibility.ctrbSubspace_isAbsorbing
#print axioms MeynTweedie.Irreducibility.density_4_18_counterexample
#print axioms MeynTweedie.Irreducibility.ctrbSubspace
#print axioms MeynTweedie.Irreducibility.measurableSet_ctrbSubspace
#print axioms MeynTweedie.Irreducibility.pow_mulVec_mem_ctrbSubspace
#print axioms MeynTweedie.Irreducibility.ctrbMap_mem_ctrbSubspace
#print axioms MeynTweedie.Irreducibility.ctrbMap₀
#print axioms MeynTweedie.Irreducibility.ctrbMap₀_surjective
#print axioms MeynTweedie.Irreducibility.ctrbF₀
#print axioms MeynTweedie.Irreducibility.ctrbG₀
#print axioms MeynTweedie.Irreducibility.coe_ctrbStep
#print axioms MeynTweedie.Irreducibility.restrictKernel_eq_lssKernel
#print axioms MeynTweedie.Irreducibility.coe_controlMap_ctrb
#print axioms MeynTweedie.Irreducibility.restricted_controllable
#print axioms MeynTweedie.Irreducibility.restricted_pow_eq_zero_iff
#print axioms MeynTweedie.Irreducibility.restricted_isPhiIrreducible
#print axioms MeynTweedie.Irreducibility.restricted_isMaximalIrreducibility
#print axioms MeynTweedie.Irreducibility.restricted_irreducible
#print axioms MeynTweedie.Irreducibility.restricted_irreducible_gaussian
#print axioms MeynTweedie.Irreducibility.map_fin_one_equiv
#print axioms MeynTweedie.Irreducibility.ar_isPhiIrreducible
#print axioms MeynTweedie.Irreducibility.range_gramian
#print axioms MeynTweedie.Irreducibility.range_gramian_n
#print axioms MeynTweedie.Irreducibility.finrank_ctrbSubspace
#print axioms MeynTweedie.Irreducibility.finrank_ctrbSubspace_lt
#print axioms MeynTweedie.Irreducibility.isControllable_of_rank_G
#print axioms MeynTweedie.Irreducibility.lss_fullRank_G_irreducible
#print axioms MeynTweedie.Irreducibility.countable_absorbing_classes
#print axioms MeynTweedie.Irreducibility.unifAccessible_not_refl
#print axioms MeynTweedie.Irreducibility.exists_pow_pos_of_reach
#print axioms MeynTweedie.Irreducibility.not_isPhiIrreducible_of_disjoint_absorbing
#print axioms MeynTweedie.Irreducibility.isPhiIrreducible_of_skeleton
#print axioms MeynTweedie.Irreducibility.halfLine_pow_zero_ge
#print axioms MeynTweedie.Irreducibility.exists_Iio_neg_pos
#print axioms MeynTweedie.Irreducibility.halfLine_hitProb_zero_eq_zero
#print axioms MeynTweedie.Irreducibility.proposition_4_3_1
#print axioms MeynTweedie.Irreducibility.proposition_4_3_1_compact
#print axioms MeynTweedie.Irreducibility.halfLine_maximal
#print axioms MeynTweedie.Irreducibility.isPhiIrreducible_of_local_density
#print axioms MeynTweedie.Irreducibility.le_of_density
#print axioms MeynTweedie.Irreducibility.ar1_isPhiIrreducible_of_density
#print axioms MeynTweedie.Irreducibility.randomWalk_isPhiIrreducible_of_density
#print axioms MeynTweedie.Irreducibility.randomWalk_isPhiIrreducible_Icc
#print axioms MeynTweedie.Irreducibility.randomWalk_step_ge
#print axioms MeynTweedie.Irreducibility.randomWalk_isPhiIrreducible_of_convPow
#print axioms MeynTweedie.Irreducibility.ratCoset
#print axioms MeynTweedie.Irreducibility.randomWalk_rational
#print axioms MeynTweedie.Irreducibility.ar1_uniform_isPhiIrreducible
#print axioms MeynTweedie.Irreducibility.ar1_abs_lt_step
#print axioms MeynTweedie.Irreducibility.ar1_explosive_not_irreducible
#print axioms MeynTweedie.Irreducibility.IsCountableStateSpace
#print axioms MeynTweedie.Irreducibility.IsGeneralStateSpace
#print axioms MeynTweedie.Irreducibility.IsTopologicalStateSpace
#print axioms MeynTweedie.Irreducibility.IsCountableStateSpace.isGeneral
#print axioms MeynTweedie.Irreducibility.IsTopologicalStateSpace.isGeneral
#print axioms MeynTweedie.Irreducibility.inputKernel
#print axioms MeynTweedie.Irreducibility.inputKernel_apply
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_inputKernel
#print axioms MeynTweedie.Irreducibility.contentPreInputKernel
#print axioms MeynTweedie.Irreducibility.isMarkovKernel_contentPreInputKernel
#print axioms MeynTweedie.Irreducibility.contentPreInput_zero_pos
#print axioms MeynTweedie.Irreducibility.contentPreInput_isPhiIrreducible
#print axioms MeynTweedie.Irreducibility.contentPreInput_hitProb_zero
#print axioms MeynTweedie.Irreducibility.contentPreInput_not_isPhiIrreducible
