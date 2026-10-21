import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Random recursions as transition kernels

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Random walks

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear models

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonlinear state space models

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Countable-space models

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GI/G/1, GI/M/1 and M/G/1 queues

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Storage models

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Renewal processes and recurrence time chains

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

namespace MeynTweedie.MarkovModels

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

end MeynTweedie.MarkovModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

set_option linter.style.longLine false
#print axioms MeynTweedie.MarkovModels.controlMap
#print axioms MeynTweedie.MarkovModels.controlMap_zero
#print axioms MeynTweedie.MarkovModels.controlMap_succ
#print axioms MeynTweedie.MarkovModels.controlMap_one
#print axioms MeynTweedie.MarkovModels.controlMap_succ_cons
#print axioms MeynTweedie.MarkovModels.orbit
#print axioms MeynTweedie.MarkovModels.orbit_zero
#print axioms MeynTweedie.MarkovModels.orbit_succ
#print axioms MeynTweedie.MarkovModels.orbit_eq_controlMap
#print axioms MeynTweedie.MarkovModels.recursionKernel
#print axioms MeynTweedie.MarkovModels.recursionKernel_apply
#print axioms MeynTweedie.MarkovModels.recursionKernel_apply'
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_recursionKernel
#print axioms MeynTweedie.MarkovModels.recursionKernel_comp_noise
#print axioms MeynTweedie.MarkovModels.recursionKernel_const_noise
#print axioms MeynTweedie.MarkovModels.measurable_controlMap
#print axioms MeynTweedie.MarkovModels.measurable_controlMap_right
#print axioms MeynTweedie.MarkovModels.recursionKernel_pow_apply
#print axioms MeynTweedie.MarkovModels.recursionKernel_pow_apply'
#print axioms MeynTweedie.MarkovModels.infinitePi_map_shift
#print axioms MeynTweedie.MarkovModels.law_orbit
#print axioms MeynTweedie.MarkovModels.randomWalkKernel
#print axioms MeynTweedie.MarkovModels.measurable_add_step
#print axioms MeynTweedie.MarkovModels.randomWalkKernel_apply
#print axioms MeynTweedie.MarkovModels.randomWalkKernel_apply'
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_randomWalkKernel
#print axioms MeynTweedie.MarkovModels.randomWalkKernel_real_apply_Iic
#print axioms MeynTweedie.MarkovModels.controlMap_add
#print axioms MeynTweedie.MarkovModels.orbit_randomWalk
#print axioms MeynTweedie.MarkovModels.convPow
#print axioms MeynTweedie.MarkovModels.measurable_sum_fin
#print axioms MeynTweedie.MarkovModels.randomWalkKernel_pow_apply
#print axioms MeynTweedie.MarkovModels.IsSpreadOut
#print axioms MeynTweedie.MarkovModels.halfLineStep
#print axioms MeynTweedie.MarkovModels.measurable_halfLineStep
#print axioms MeynTweedie.MarkovModels.halfLineWalkKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_halfLineWalkKernel
#print axioms MeynTweedie.MarkovModels.halfLineWalkKernel_apply'
#print axioms MeynTweedie.MarkovModels.halfLineWalkKernel_apply_zero
#print axioms MeynTweedie.MarkovModels.halfLineWalkKernel_apply_Iic
#print axioms MeynTweedie.MarkovModels.halfLineWalkKernel_apply_Ioi
#print axioms MeynTweedie.MarkovModels.halfLineOrbit
#print axioms MeynTweedie.MarkovModels.partialSum
#print axioms MeynTweedie.MarkovModels.halfLineOrbit_succ_coe
#print axioms MeynTweedie.MarkovModels.halfLineOrbit_eq_of_nonneg
#print axioms MeynTweedie.MarkovModels.halfLineOrbit_succ_of_eq_zero
#print axioms MeynTweedie.MarkovModels.halfLineOrbit_eq_lindley
#print axioms MeynTweedie.MarkovModels.linear_controlMap
#print axioms MeynTweedie.MarkovModels.orbit_linear
#print axioms MeynTweedie.MarkovModels.lssKernel
#print axioms MeynTweedie.MarkovModels.measurable_lssStep
#print axioms MeynTweedie.MarkovModels.lssKernel_apply'
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_lssKernel
#print axioms MeynTweedie.MarkovModels.clm_pow_apply
#print axioms MeynTweedie.MarkovModels.orbit_lss
#print axioms MeynTweedie.MarkovModels.lssKernel_pow_apply
#print axioms MeynTweedie.MarkovModels.measurable_mulVec
#print axioms MeynTweedie.MarkovModels.lssMatrixKernel
#print axioms MeynTweedie.MarkovModels.measurable_lssMatrixStep
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_lssMatrixKernel
#print axioms MeynTweedie.MarkovModels.mulVecHom
#print axioms MeynTweedie.MarkovModels.coe_mulVecHom
#print axioms MeynTweedie.MarkovModels.matrix_pow_mulVec
#print axioms MeynTweedie.MarkovModels.orbit_lssMatrix
#print axioms MeynTweedie.MarkovModels.lssMatrixKernel_pow_apply
#print axioms MeynTweedie.MarkovModels.lcmTrajectory
#print axioms MeynTweedie.MarkovModels.IsControllable
#print axioms MeynTweedie.MarkovModels.lcmTrajectory_eq
#print axioms MeynTweedie.MarkovModels.ar1Kernel
#print axioms MeynTweedie.MarkovModels.measurable_ar1Step
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_ar1Kernel
#print axioms MeynTweedie.MarkovModels.ar1Kernel_apply'
#print axioms MeynTweedie.MarkovModels.ar1Kernel_eq_lssKernel
#print axioms MeynTweedie.MarkovModels.ar1Kernel_one
#print axioms MeynTweedie.MarkovModels.randomWalkKernel_eq_lssKernel
#print axioms MeynTweedie.MarkovModels.orbit_ar1
#print axioms MeynTweedie.MarkovModels.shiftIn
#print axioms MeynTweedie.MarkovModels.shiftIn_apply_zero
#print axioms MeynTweedie.MarkovModels.shiftIn_apply_succ
#print axioms MeynTweedie.MarkovModels.measurable_shiftIn
#print axioms MeynTweedie.MarkovModels.shiftIn_add
#print axioms MeynTweedie.MarkovModels.arStep
#print axioms MeynTweedie.MarkovModels.measurable_arStep
#print axioms MeynTweedie.MarkovModels.arKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_arKernel
#print axioms MeynTweedie.MarkovModels.companion
#print axioms MeynTweedie.MarkovModels.firstUnit
#print axioms MeynTweedie.MarkovModels.arStep_eq_companion
#print axioms MeynTweedie.MarkovModels.arKernel_eq_lssMatrixKernel
#print axioms MeynTweedie.MarkovModels.arVec
#print axioms MeynTweedie.MarkovModels.arVec_succ
#print axioms MeynTweedie.MarkovModels.armaStep
#print axioms MeynTweedie.MarkovModels.measurable_armaStep
#print axioms MeynTweedie.MarkovModels.armaKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_armaKernel
#print axioms MeynTweedie.MarkovModels.arma_of_ar
#print axioms MeynTweedie.MarkovModels.fig11F
#print axioms MeynTweedie.MarkovModels.fig11F_eq
#print axioms MeynTweedie.MarkovModels.sqNorm2
#print axioms MeynTweedie.MarkovModels.fig11_sqNorm_mulVec
#print axioms MeynTweedie.MarkovModels.fig11_tendsto_zero
#print axioms MeynTweedie.MarkovModels.fig11_inv_tendsto_atTop
#print axioms MeynTweedie.MarkovModels.nssKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_nssKernel_of_contDiff
#print axioms MeynTweedie.MarkovModels.bilinearStep
#print axioms MeynTweedie.MarkovModels.bilinearStep_eq
#print axioms MeynTweedie.MarkovModels.contDiff_bilinearStep
#print axioms MeynTweedie.MarkovModels.bilinearKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_bilinearKernel
#print axioms MeynTweedie.MarkovModels.bilinearKernel_apply'
#print axioms MeynTweedie.MarkovModels.dblStep
#print axioms MeynTweedie.MarkovModels.dblStep_fst
#print axioms MeynTweedie.MarkovModels.dblStep_snd
#print axioms MeynTweedie.MarkovModels.contDiff_dblStep
#print axioms MeynTweedie.MarkovModels.dblKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_dblKernel
#print axioms MeynTweedie.MarkovModels.dblPrinted
#print axioms MeynTweedie.MarkovModels.dbl_printed_ne
#print axioms MeynTweedie.MarkovModels.narmaStep
#print axioms MeynTweedie.MarkovModels.measurable_narmaStep
#print axioms MeynTweedie.MarkovModels.narmaKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_narmaKernel
#print axioms MeynTweedie.MarkovModels.armaKernel_eq_narmaKernel
#print axioms MeynTweedie.MarkovModels.gumleafMap
#print axioms MeynTweedie.MarkovModels.gumleafMap_of_recursion
#print axioms MeynTweedie.MarkovModels.gumleafNoisyStep
#print axioms MeynTweedie.MarkovModels.measurable_gumleafNoisyStep
#print axioms MeynTweedie.MarkovModels.gumleafKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_gumleafKernel
#print axioms MeynTweedie.MarkovModels.eNorm2
#print axioms MeynTweedie.MarkovModels.eNorm2_smul
#print axioms MeynTweedie.MarkovModels.squash
#print axioms MeynTweedie.MarkovModels.eNorm2_squash
#print axioms MeynTweedie.MarkovModels.eNorm2_squash_lt_one
#print axioms MeynTweedie.MarkovModels.unsquash
#print axioms MeynTweedie.MarkovModels.unsquash_squash
#print axioms MeynTweedie.MarkovModels.squash_unsquash
#print axioms MeynTweedie.MarkovModels.squash_gumleafMap
#print axioms MeynTweedie.MarkovModels.gumleaf_printed_ne
#print axioms MeynTweedie.MarkovModels.setarP
#print axioms MeynTweedie.MarkovModels.setarP_exists
#print axioms MeynTweedie.MarkovModels.setarRegime
#print axioms MeynTweedie.MarkovModels.setarRegime_eq_iff
#print axioms MeynTweedie.MarkovModels.setarRegime_eq_iff_Ioc
#print axioms MeynTweedie.MarkovModels.measurable_setarRegime
#print axioms MeynTweedie.MarkovModels.setarStep
#print axioms MeynTweedie.MarkovModels.measurable_setarStep
#print axioms MeynTweedie.MarkovModels.setarKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_setarKernel
#print axioms MeynTweedie.MarkovModels.setarKernel_apply'
#print axioms MeynTweedie.MarkovModels.setar_not_continuous
#print axioms MeynTweedie.MarkovModels.sacStep
#print axioms MeynTweedie.MarkovModels.measurable_sacStep
#print axioms MeynTweedie.MarkovModels.sacKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_sacKernel
#print axioms MeynTweedie.MarkovModels.sacGaussianKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_sacGaussianKernel
#print axioms MeynTweedie.MarkovModels.sac_closed_loop
#print axioms MeynTweedie.MarkovModels.sacStep_sigma_mem
#print axioms MeynTweedie.MarkovModels.sacKernel_apply_Icc
#print axioms MeynTweedie.MarkovModels.sac_rls
#print axioms MeynTweedie.MarkovModels.rcaStep
#print axioms MeynTweedie.MarkovModels.measurable_rcaStep
#print axioms MeynTweedie.MarkovModels.rcaKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_rcaKernel
#print axioms MeynTweedie.MarkovModels.rcaKernel_dirac_zero
#print axioms MeynTweedie.MarkovModels.reflectStep
#print axioms MeynTweedie.MarkovModels.reflectedWalkKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_reflectedWalkKernel
#print axioms MeynTweedie.MarkovModels.reflectedWalkKernel_apply_pos
#print axioms MeynTweedie.MarkovModels.reflectedWalkKernel_apply_zero
#print axioms MeynTweedie.MarkovModels.not_down_of_eq_2_28
#print axioms MeynTweedie.MarkovModels.twoPointLaw
#print axioms MeynTweedie.MarkovModels.reflectedWalk_2_28_fails
#print axioms MeynTweedie.MarkovModels.birthDeathKernel
#print axioms MeynTweedie.MarkovModels.birthDeathKernel_apply
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_birthDeathKernel
#print axioms MeynTweedie.MarkovModels.birthDeathKernel_apply_succ
#print axioms MeynTweedie.MarkovModels.birthDeathKernel_apply_pred
#print axioms MeynTweedie.MarkovModels.lindleyStep
#print axioms MeynTweedie.MarkovModels.measurable_lindleyStep
#print axioms MeynTweedie.MarkovModels.waitingTimeKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_waitingTimeKernel
#print axioms MeynTweedie.MarkovModels.waitingTimeKernel_eq_halfLineWalk
#print axioms MeynTweedie.MarkovModels.giM1Step
#print axioms MeynTweedie.MarkovModels.giM1Kernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_giM1Kernel
#print axioms MeynTweedie.MarkovModels.giM1Kernel_apply'
#print axioms MeynTweedie.MarkovModels.giM1Kernel_apply_up
#print axioms MeynTweedie.MarkovModels.giM1Kernel_apply_le
#print axioms MeynTweedie.MarkovModels.giM1Kernel_apply_zero
#print axioms MeynTweedie.MarkovModels.giM1Kernel_not_2_28
#print axioms MeynTweedie.MarkovModels.mG1Step
#print axioms MeynTweedie.MarkovModels.mG1Kernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_mG1Kernel
#print axioms MeynTweedie.MarkovModels.mG1Kernel_apply
#print axioms MeynTweedie.MarkovModels.mG1Kernel_zero
#print axioms MeynTweedie.MarkovModels.expMeasure_Ioi
#print axioms MeynTweedie.MarkovModels.expMeasure_memoryless
#print axioms MeynTweedie.MarkovModels.expMeasure_prod_lt
#print axioms MeynTweedie.MarkovModels.dirac_not_memoryless
#print axioms MeynTweedie.MarkovModels.storageStep
#print axioms MeynTweedie.MarkovModels.measurable_storageStep
#print axioms MeynTweedie.MarkovModels.storageKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_storageKernel
#print axioms MeynTweedie.MarkovModels.storageKernel_eq_halfLineWalk
#print axioms MeynTweedie.MarkovModels.releaseLaw_Iic
#print axioms MeynTweedie.MarkovModels.storageKernel_one
#print axioms MeynTweedie.MarkovModels.storage_mean_increment
#print axioms MeynTweedie.MarkovModels.releaseTime
#print axioms MeynTweedie.MarkovModels.continuous_releaseTime
#print axioms MeynTweedie.MarkovModels.releaseTime_strictMono
#print axioms MeynTweedie.MarkovModels.releaseTime_strictMonoOn
#print axioms MeynTweedie.MarkovModels.releaseTime_bijOn
#print axioms MeynTweedie.MarkovModels.releaseTime_one_add_sq
#print axioms MeynTweedie.MarkovModels.releaseTime_not_surjective
#print axioms MeynTweedie.MarkovModels.inputKernel
#print axioms MeynTweedie.MarkovModels.inputKernel_apply
#print axioms MeynTweedie.MarkovModels.contentKernel
#print axioms MeynTweedie.MarkovModels.contentPreInputKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_contentKernel
#print axioms MeynTweedie.MarkovModels.contentRelease_Iic
#print axioms MeynTweedie.MarkovModels.contentKernel_apply'
#print axioms MeynTweedie.MarkovModels.contentKernel_ne_storageKernel
#print axioms MeynTweedie.MarkovModels.contentPreInputKernel_eq_storageKernel
#print axioms MeynTweedie.MarkovModels.renewalKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_renewalKernel
#print axioms MeynTweedie.MarkovModels.renewalKernel_apply_singleton
#print axioms MeynTweedie.MarkovModels.renewalKernel_apply_Ioi
#print axioms MeynTweedie.MarkovModels.le_renewal
#print axioms MeynTweedie.MarkovModels.seqConv
#print axioms MeynTweedie.MarkovModels.seqConv_eq_sum_range
#print axioms MeynTweedie.MarkovModels.seqConv_comm
#print axioms MeynTweedie.MarkovModels.seqConvPow
#print axioms MeynTweedie.MarkovModels.mk_coeff_eq
#print axioms MeynTweedie.MarkovModels.mk_seqConv
#print axioms MeynTweedie.MarkovModels.mk_seqConvPow
#print axioms MeynTweedie.MarkovModels.seqConvPow_succ
#print axioms MeynTweedie.MarkovModels.bind_renewalKernel_singleton
#print axioms MeynTweedie.MarkovModels.renewal_law
#print axioms MeynTweedie.MarkovModels.renewal_law_one
#print axioms MeynTweedie.MarkovModels.fwdStep
#print axioms MeynTweedie.MarkovModels.forwardKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_forwardKernel
#print axioms MeynTweedie.MarkovModels.forwardKernel_of_one_lt
#print axioms MeynTweedie.MarkovModels.forwardKernel_one
#print axioms MeynTweedie.MarkovModels.hazard
#print axioms MeynTweedie.MarkovModels.hazard_le_one
#print axioms MeynTweedie.MarkovModels.backwardKernel
#print axioms MeynTweedie.MarkovModels.backwardKernel_apply
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_backwardKernel
#print axioms MeynTweedie.MarkovModels.backwardKernel_apply_zero
#print axioms MeynTweedie.MarkovModels.backwardKernel_apply_succ
#print axioms MeynTweedie.MarkovModels.fwdTime
#print axioms MeynTweedie.MarkovModels.bwdTime
#print axioms MeynTweedie.MarkovModels.fwdTime_set_nonempty
#print axioms MeynTweedie.MarkovModels.one_le_fwdTime
#print axioms MeynTweedie.MarkovModels.fwdTime_succ_of_one_lt
#print axioms MeynTweedie.MarkovModels.fwdTime_succ_of_eq_one
#print axioms MeynTweedie.MarkovModels.bwdTime_set_empty
#print axioms MeynTweedie.MarkovModels.bwdTime_set_empty_example
#print axioms MeynTweedie.MarkovModels.bwdTime_succ_of_renewal
#print axioms MeynTweedie.MarkovModels.bwdTime_succ_of_not_renewal
#print axioms MeynTweedie.MarkovModels.fwdTimeCts
#print axioms MeynTweedie.MarkovModels.bwdTimeCts
#print axioms MeynTweedie.MarkovModels.fwdSkeleton
#print axioms MeynTweedie.MarkovModels.bwdSkeleton
#print axioms MeynTweedie.MarkovModels.IsGIM1Service
#print axioms MeynTweedie.MarkovModels.IsMG1Arrivals
#print axioms MeynTweedie.MarkovModels.cdf_of_isGIM1Service
#print axioms MeynTweedie.MarkovModels.HasFiniteMeanVariance
#print axioms MeynTweedie.MarkovModels.IsStdGaussianNoise
#print axioms MeynTweedie.MarkovModels.IsNonsingularNoise
#print axioms MeynTweedie.MarkovModels.HasStableEigenvalues
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_lssMatrixKernel_of_stdGaussian
#print axioms MeynTweedie.MarkovModels.IsSemiDynamicalSystem
#print axioms MeynTweedie.MarkovModels.SatisfiesDS2
#print axioms MeynTweedie.MarkovModels.IsSmoothModel
#print axioms MeynTweedie.MarkovModels.HasDensityOnControlSet
#print axioms MeynTweedie.MarkovModels.HasLscDensity
#print axioms MeynTweedie.MarkovModels.isOpen_controlSet
#print axioms MeynTweedie.MarkovModels.hasDensityOnControlSet_of_lsc
#print axioms MeynTweedie.MarkovModels.SatisfiesCM2
#print axioms MeynTweedie.MarkovModels.SatisfiesCM3
#print axioms MeynTweedie.MarkovModels.SatisfiesSAC2
#print axioms MeynTweedie.MarkovModels.SatisfiesSETAR1Noise
#print axioms MeynTweedie.MarkovModels.SatisfiesSETAR2
#print axioms MeynTweedie.MarkovModels.SatisfiesSETAR3
#print axioms MeynTweedie.MarkovModels.SatisfiesSBL2
#print axioms MeynTweedie.MarkovModels.SatisfiesDBL2
#print axioms MeynTweedie.MarkovModels.SatisfiesRCA2
#print axioms MeynTweedie.MarkovModels.SatisfiesRCA3
#print axioms MeynTweedie.MarkovModels.trajKernel
#print axioms MeynTweedie.MarkovModels.isMarkovKernel_trajKernel
#print axioms MeynTweedie.MarkovModels.pathMeasure
#print axioms MeynTweedie.MarkovModels.isProbabilityMeasure_pathMeasure
#print axioms MeynTweedie.MarkovModels.hittingTime
#print axioms MeynTweedie.MarkovModels.hitEvent
#print axioms MeynTweedie.MarkovModels.hittingTime_lt_top_iff
#print axioms MeynTweedie.MarkovModels.measurableSet_hitEvent
#print axioms MeynTweedie.MarkovModels.IsPhiIrreducible
#print axioms MeynTweedie.MarkovModels.IsPhiRecurrent
#print axioms MeynTweedie.MarkovModels.HasFiniteMeanHitting
#print axioms MeynTweedie.MarkovModels.evanescenceEvent
#print axioms MeynTweedie.MarkovModels.IsNonEvanescent
#print axioms MeynTweedie.MarkovModels.IsTightChain
#print axioms MeynTweedie.MarkovModels.invariant_iff_eq_lintegral
#print axioms MeynTweedie.MarkovModels.IsSmallSet
#print axioms MeynTweedie.MarkovModels.BoundedMeanReturn
#print axioms MeynTweedie.MarkovModels.SatisfiesDrift
#print axioms MeynTweedie.MarkovModels.IsLocallyConvergent
#print axioms MeynTweedie.MarkovModels.tvDist
#print axioms MeynTweedie.MarkovModels.ConvergesInTotalVariation
#print axioms MeynTweedie.MarkovModels.IsWeakFeller
#print axioms MeynTweedie.MarkovModels.distStep
#print axioms MeynTweedie.MarkovModels.fixedPoint_distStep_iff
#print axioms MeynTweedie.MarkovModels.IsLagrangeStable
#print axioms MeynTweedie.MarkovModels.IsLyapunovStable
#print axioms MeynTweedie.MarkovModels.IsAsymptoticallyStable
#print axioms MeynTweedie.MarkovModels.IsGloballyAsymptoticallyStable
#print axioms MeynTweedie.MarkovModels.iterate_add_one
#print axioms MeynTweedie.MarkovModels.succ_isLyapunovStable
#print axioms MeynTweedie.MarkovModels.succ_not_isLagrangeStable
#print axioms MeynTweedie.MarkovModels.succ_not_isGloballyAsymptoticallyStable
