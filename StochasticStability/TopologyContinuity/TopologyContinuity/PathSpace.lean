/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Cylinders

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

namespace MeynTweedie.TopologyContinuity

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

end MeynTweedie.TopologyContinuity
