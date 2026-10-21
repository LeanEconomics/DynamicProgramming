/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure

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

namespace MeynTweedie.DriftRegularity

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

end MeynTweedie.DriftRegularity
