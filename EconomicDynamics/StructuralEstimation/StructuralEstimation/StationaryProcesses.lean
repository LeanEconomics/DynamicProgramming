/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.ErgodicTheorem
import Mathlib.Probability.Independence.Basic

/-!
# Stationary processes (Miao §4.2)

Copied from `EconomicDynamics/ErgodicTheory` (module `StationaryProcesses`), namespace renamed.

Miao, §4.2, pp. 120–125. A process is a family `X : ℕ → Ω → E` of random variables on
`(Ω, F, Pr)`; the state space `E` is any measurable space (the book takes `E = ℝ`; only the strong
law needs real values). Its path is `pathOf X ω = (X₀(ω), X₁(ω), …)` and its law on `E^ℕ` is
`pathLaw P X`. The shift is `shift 1`, `θx = (x₁, x₂, …)`, with iterates `shift k`.

* **Definition 4.2.1** (`IsStationary`): the law of `(X_t, …, X_{t+n})` (`window X t n`) does not
  depend on `t`. `isStationary_iff_map_shift`, `isStationary_iff_measurePreserving`: `X` is
  stationary iff the shift preserves its law on path space.
* p. 120: `isStationary_of_iid` (an IID sequence is stationary) and `isStationary_comp_window`
  (`Y_t = g(X_t, …, X_{t+n})` is stationary when `X` is).
* p. 121: `isStationary_of_measurePreserving` (`X_k = g ∘ θᵏ` is stationary for a
  measure-preserving `θ`) and the converse representation `stationary_representation` (on
  `(E^ℕ, B(E^ℕ), P̃r)` the shift is measure preserving and the coordinate process has the law of
  `X`).
* **Definitions 4.2.2–4.2.3** (`IsShiftInvariant`, `IsErgodicProcess`), with the correction
  below: `shiftInvariant_compl_counterexample`, `exists_invariant_ae_eq`,
  `isErgodicProcess_iff_isErgodic`.
* **Theorem 4.2.1** (strong law of large numbers): `theorem_4_2_1` ((4.1), the limit
  `E[X₀ | I]` with `I = invariantField X`), `theorem_4_2_1_ergodic` ((4.2)), and `eq_4_3` (the
  path-space statement (4.3)); `condExp_comp_ae_eq` transports conditional expectations from
  path space.
* **Definition 4.2.4** (`IsMixing`) and **Theorem 4.2.3** (`theorem_4_2_3`): a mixing stationary
  process is ergodic.
* The setting of **Theorem 4.2.4** (`theorem_4_2_4_filtration_mono`: `M_k = θ⁻ᵏM₀` increases);
  the central limit theorem itself is not formalised.

**Corrections.**
1. Definition 4.2.2 calls `A` shift invariant when `θA ⊆ A` (`x ∈ A ⇒ θx ∈ A`). These sets are
   not closed under complements (`shiftInvariant_compl_counterexample`: `A = {0}`), so "the class
   of shift invariant sets" is not a σ-algebra and cannot be the `I` of Theorem 4.2.1, and the
   claim on p. 123 that it equals the σ-algebra of transformation-invariant sets is false. What is
   true: every transformation-invariant set is shift invariant
   (`isShiftInvariant_of_preimage_eq`), and every measurable shift-invariant set differs from a
   transformation-invariant one by a null set (`exists_invariant_ae_eq`). So Definition 4.2.3 is
   equivalent to ergodicity of the shift in the sense of Definition 4.1.4
   (`isErgodicProcess_iff_isErgodic`), and `I` in Theorem 4.2.1 is taken to be the σ-algebra of
   events `{(X₀, X₁, …) ∈ A}` with `θ⁻¹A = A`.
2. Definition 4.2.4 is stated with the difference `Pr(…) − Pr(…) Pr(…) → 0` (its right side
   depends on `n`).
3. Theorem 4.2.4 (Heyde's CLT) is not formalised; it needs a martingale CLT.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-! ### Paths, windows and stationarity -/

/-- The path `(X₀(ω), X₁(ω), …)` of a process. -/
def pathOf (X : ℕ → Ω → E) (ω : Ω) : ℕ → E := fun n => X n ω

/-- The window `(X_t, X_{t+1}, …, X_{t+n})`. -/
def window (X : ℕ → Ω → E) (t n : ℕ) (ω : Ω) : Fin (n + 1) → E := fun i => X (t + i) ω

/-- The first `n + 1` coordinates of a path. -/
def pathWindow (n : ℕ) (x : ℕ → E) : Fin (n + 1) → E := fun i => x i

/-- The law `P̃r = Pr ∘ (X₀, X₁, …)⁻¹` of a process on path space (Miao, p. 121). -/
noncomputable def pathLaw (P : Measure Ω) (X : ℕ → Ω → E) : Measure (ℕ → E) := P.map (pathOf X)

/-- **Definition 4.2.1** (Miao, p. 120). `X` is (strictly) stationary if the distribution of
`(X_t, X_{t+1}, …, X_{t+n})` does not depend on `t`, for every `n`. -/
def IsStationary (P : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ t n : ℕ, P.map (window X t n) = P.map (window X 0 n)

theorem measurable_pathOf {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) :
    Measurable (pathOf X) :=
  measurable_pi_iff.2 hX

theorem measurable_window {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (t n : ℕ) :
    Measurable (window X t n) :=
  measurable_pi_iff.2 fun i => hX (t + i)

theorem measurable_pathWindow (n : ℕ) : Measurable (pathWindow (E := E) n) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `(X_t, …, X_{t+n}) = (first n + 1 coordinates) ∘ θᵗ ∘ (X₀, X₁, …)`. -/
theorem window_eq (X : ℕ → Ω → E) (t n : ℕ) :
    window X t n = pathWindow n ∘ shift t ∘ pathOf X := by
  ext ω i
  rfl

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `(X₀, …, Xₙ) = (first n + 1 coordinates) ∘ (X₀, X₁, …)`. -/
theorem window_zero (X : ℕ → Ω → E) (n : ℕ) : window X 0 n = pathWindow n ∘ pathOf X := by
  ext ω i
  simp [window, pathWindow, pathOf]

/-- The law of the path is a probability measure. -/
theorem isProbabilityMeasure_pathLaw (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} : IsProbabilityMeasure (pathLaw P X) := by
  unfold pathLaw; infer_instance

omit [MeasurableSpace E] in
/-- A box `{x₀ ∈ A₀, …, xₙ ∈ Aₙ}` is the preimage of a rectangle under the first `n + 1`
coordinates. -/
theorem boxSet_eq_preimage (n : ℕ) (A : ℕ → Set E) :
    boxSet n A = pathWindow n ⁻¹' Set.univ.pi (fun i : Fin (n + 1) => A i) := by
  ext x
  simp only [boxSet, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_const, pathWindow]
  constructor
  · intro h i
    exact h i (Nat.lt_succ_iff.1 i.isLt)
  · intro h i hi
    exact h ⟨i, Nat.lt_succ_of_le hi⟩

/-- Two finite measures on path space that agree on all boxes are equal. -/
theorem ext_of_boxSet {μ ν : Measure (ℕ → E)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n (A : ℕ → Set E), (∀ i, MeasurableSet (A i)) → μ (boxSet n A) = ν (boxSet n A)) :
    μ = ν := by
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨n, A, hA, rfl⟩
    exact h n A hA
  · have hu : (Set.univ : Set (ℕ → E)) = boxSet 0 (fun _ => Set.univ) := by
      ext; simp [boxSet]
    rw [hu, h 0 _ fun _ => MeasurableSet.univ]

/-- Stationarity is shift invariance of the law of the path:
`X` is stationary iff `P̃r ∘ (θᵗ)⁻¹ = P̃r` for every `t`. -/
theorem isStationary_iff_map_shift {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) :
    IsStationary P X ↔ ∀ t, (pathLaw P X).map (shift t) = pathLaw P X := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  constructor
  · intro h t
    have : IsProbabilityMeasure ((pathLaw P X).map (shift t)) :=
      inferInstance
    refine ext_of_boxSet fun n A hA => ?_
    have hR : MeasurableSet (Set.univ.pi fun i : Fin (n + 1) => A i) :=
      MeasurableSet.univ_pi fun i => hA i
    have hB := measurableSet_boxSet n hA
    rw [Measure.map_apply (measurable_shift t) hB, pathLaw, Measure.map_apply hΦ hB,
      Measure.map_apply hΦ ((measurable_shift t) hB), boxSet_eq_preimage]
    have h1 := congrArg (fun m : Measure (Fin (n + 1) → E) =>
      m (Set.univ.pi fun i : Fin (n + 1) => A i)) (h t n)
    rw [Measure.map_apply (measurable_window hX t n) hR,
      Measure.map_apply (measurable_window hX 0 n) hR, window_zero] at h1
    exact h1
  · intro h t n
    rw [window_eq, window_zero, ← Measure.map_map (measurable_pathWindow n)
      ((measurable_shift t).comp hΦ), ← Measure.map_map (measurable_shift t) hΦ,
      ← Measure.map_map (measurable_pathWindow n) hΦ]
    change ((pathLaw P X).map (shift t)).map _ = (pathLaw P X).map _
    rw [h t]

/-- `X` is stationary iff the one-step shift `θ` preserves the law `P̃r` of its path. -/
theorem isStationary_iff_measurePreserving {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) :
    IsStationary P X ↔ MeasurePreserving (shift 1) (pathLaw P X) (pathLaw P X) := by
  rw [isStationary_iff_map_shift hX]
  constructor
  · intro h
    exact ⟨measurable_shift 1, h 1⟩
  · intro h t
    have := (h.iterate t).map_eq
    have heq : (shift 1)^[t] = shift (X := E) t := funext (iterate_shift_one t)
    rwa [heq] at this

/-- Miao, p. 121: if `θ` is measure preserving and `g` is measurable, then `X_k = g(θᵏω)` is a
stationary process. -/
theorem isStationary_of_measurePreserving {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Ω} (hθ : MeasurePreserving θ P P) {g : Ω → E} (hg : Measurable g) :
    IsStationary P (fun k ω => g (θ^[k] ω)) := by
  have hX : ∀ k, Measurable fun ω => g (θ^[k] ω) := fun k =>
    hg.comp (hθ.measurable.iterate k)
  rw [isStationary_iff_measurePreserving hX]
  refine ⟨measurable_shift 1, ?_⟩
  have hcomm : shift 1 ∘ pathOf (fun k ω => g (θ^[k] ω)) =
      pathOf (fun k ω => g (θ^[k] ω)) ∘ θ := by
    ext ω i
    simp only [Function.comp_apply, shift_apply, pathOf]
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
  rw [pathLaw, Measure.map_map (measurable_shift 1) (measurable_pathOf hX), hcomm,
    ← Measure.map_map (measurable_pathOf hX) hθ.measurable, hθ.map_eq]

/-- Miao, p. 121 (converse): for a stationary `X`, on the coordinate space
`(E^ℕ, B(E^ℕ), P̃r)` the shift is measure preserving, `X̃_k = f(θᵏx) = x_k` for `f(x) = x₀`, and
`X̃` has the same finite-dimensional distributions as `X`. -/
theorem stationary_representation {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    MeasurePreserving (shift 1) (pathLaw P X) (pathLaw P X) ∧
      (∀ k (x : ℕ → E), (shift 1)^[k] x 0 = x k) ∧
      ∀ n, (pathLaw P X).map (pathWindow n) = P.map (window X 0 n) := by
  refine ⟨(isStationary_iff_measurePreserving hX).1 hst, fun k x => ?_, fun n => ?_⟩
  · rw [iterate_shift_one, shift_apply, add_zero]
  · rw [pathLaw, Measure.map_map (measurable_pathWindow n) (measurable_pathOf hX), window_zero]

/-- Miao, p. 120: if `X` is stationary and `g` is Borel, `Y_t = g(X_t, …, X_{t+n})` is
stationary. (The book says this for an IID `X`; it holds for every stationary `X`.) -/
theorem isStationary_comp_window {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) {F : Type*}
    [MeasurableSpace F] (n : ℕ) {g : (Fin (n + 1) → E) → F} (hg : Measurable g) :
    IsStationary P (fun t ω => g (window X t n ω)) := by
  have hY : ∀ t, Measurable fun ω => g (window X t n ω) := fun t =>
    hg.comp (measurable_window hX t n)
  set G : (ℕ → E) → ℕ → F := fun x t => g (pathWindow n (shift t x)) with hG
  have hGm : Measurable G := measurable_pi_iff.2 fun t =>
    hg.comp ((measurable_pathWindow n).comp (measurable_shift t))
  have hpath : pathOf (fun t ω => g (window X t n ω)) = G ∘ pathOf X := by
    ext ω t
    rfl
  have hcomm : shift 1 ∘ G = G ∘ shift 1 := by
    ext x t
    simp only [Function.comp_apply, shift_apply, hG, shift_shift]
  rw [isStationary_iff_measurePreserving hY]
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  refine ⟨measurable_shift 1, ?_⟩
  rw [pathLaw, hpath, ← Measure.map_map hGm (measurable_pathOf hX),
    Measure.map_map (measurable_shift 1) hGm, hcomm,
    ← Measure.map_map hGm (measurable_shift 1)]
  change ((pathLaw P X).map (shift 1)).map G = (pathLaw P X).map G
  rw [hmp.map_eq]

/-- Miao, p. 120: an IID sequence is stationary. -/
theorem isStationary_of_iid {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X P)
    (hid : ∀ n, P.map (X n) = P.map (X 0)) : IsStationary P X := by
  intro t n
  have hlaw : ∀ s : ℕ, P.map (window X s n) =
      Measure.pi (fun _ : Fin (n + 1) => P.map (X 0)) := by
    intro s
    have hinj : Function.Injective fun i : Fin (n + 1) => s + (i : ℕ) := by
      intro i j hij
      exact Fin.ext (by simpa using hij)
    have h := (iIndepFun_iff_map_fun_eq_pi_map (f := fun i : Fin (n + 1) => X (s + i))
      (fun i => (hX (s + i)).aemeasurable)).1
      (hind.precomp hinj)
    change P.map (fun ω (i : Fin (n + 1)) => X (s + i) ω) = _
    rw [h]
    congr 1
    ext1 i
    exact hid _
  rw [hlaw t, hlaw 0]

/-! ### Definitions 4.2.2–4.2.3 and the correction -/

/-- **Definition 4.2.2** (Miao, p. 122). `A ⊆ E^ℕ` is shift invariant if `θx ∈ A` whenever
`x ∈ A`. -/
def IsShiftInvariant (A : Set (ℕ → E)) : Prop := ∀ x ∈ A, shift 1 x ∈ A

/-- **Definition 4.2.3** (Miao, p. 122). A process is ergodic if every (measurable) shift
invariant set has probability zero or one: `Pr{(X₀, X₁, …) ∈ A} ∈ {0, 1}`. -/
def IsErgodicProcess (P : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ A : Set (ℕ → E), MeasurableSet A → IsShiftInvariant A →
    P (pathOf X ⁻¹' A) = 0 ∨ P (pathOf X ⁻¹' A) = 1

omit [MeasurableSpace E] in
/-- A transformation-invariant set (`θ⁻¹A = A`) is shift invariant in the sense of
Definition 4.2.2. -/
theorem isShiftInvariant_of_preimage_eq {A : Set (ℕ → E)} (h : shift 1 ⁻¹' A = A) :
    IsShiftInvariant A := fun x hx => by
  rw [← h] at hx
  exact hx

/-- **Correction to Definition 4.2.2 / p. 123.** The shift-invariant sets of Definition 4.2.2 are
not closed under complements: `A = {(0, 0, …)}` is shift invariant but its complement is not
(`(1, 0, 0, …) ∈ Aᶜ` while `θ(1, 0, 0, …) ∉ Aᶜ`). So they do not form a σ-algebra. -/
theorem shiftInvariant_compl_counterexample :
    ∃ A : Set (ℕ → ℝ), MeasurableSet A ∧ IsShiftInvariant A ∧ ¬ IsShiftInvariant Aᶜ := by
  refine ⟨{fun _ => 0}, measurableSet_singleton _, fun x hx => ?_, fun h => ?_⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  · set y : ℕ → ℝ := fun n => if n = 0 then 1 else 0 with hy
    have hy1 : y ∈ ({fun _ => 0} : Set (ℕ → ℝ))ᶜ := by
      intro hmem
      have := congrFun (Set.mem_singleton_iff.1 hmem) 0
      simp [hy] at this
    have h2 := h y hy1
    apply h2
    rw [Set.mem_singleton_iff]
    ext n
    simp [hy, shift]

omit [MeasurableSpace E] in
/-- For a shift-invariant `A`, the sets `θ⁻ⁿA` increase. -/
theorem preimage_shift_mono {A : Set (ℕ → E)} (hA : IsShiftInvariant A) (n : ℕ) :
    shift n ⁻¹' A ⊆ shift (n + 1) ⁻¹' A := by
  intro x hx
  have := hA _ hx
  simpa [Set.mem_preimage, shift_shift] using this

/-- **Correction to p. 123.** Every measurable shift-invariant set `A` (Definition 4.2.2) agrees,
up to a null set, with the transformation-invariant set `B = ⋃ₙ θ⁻ⁿA` (`θ⁻¹B = B`), for any
shift-preserving finite measure. -/
theorem exists_invariant_ae_eq {μ : Measure (ℕ → E)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {A : Set (ℕ → E)} (hAm : MeasurableSet A)
    (hA : IsShiftInvariant A) :
    ∃ B : Set (ℕ → E), MeasurableSet B ∧ shift 1 ⁻¹' B = B ∧ B =ᵐ[μ] A ∧ A ⊆ B := by
  refine ⟨⋃ n, shift n ⁻¹' A, MeasurableSet.iUnion fun n => (measurable_shift n) hAm, ?_, ?_,
    fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩⟩
  · rw [Set.preimage_iUnion]
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, shift_shift]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨1 + n, hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := preimage_shift_mono hA n hn
      simpa [Set.mem_preimage, add_comm] using this
  · have hnull : ∀ n, μ (shift n ⁻¹' A \ A) = 0 := by
      intro n
      have hsub : A ⊆ shift n ⁻¹' A := by
        induction n with
        | zero => intro x hx; simpa [Set.mem_preimage, shift_zero] using hx
        | succ n ih => exact ih.trans (preimage_shift_mono hA n)
      have hmp : MeasurePreserving (shift (X := E) n) μ μ := by
        have := hμ.iterate n
        rwa [show (shift 1)^[n] = shift (X := E) n from funext (iterate_shift_one n)] at this
      rw [measure_sdiff hsub hAm.nullMeasurableSet (measure_ne_top μ A),
        hmp.measure_preimage hAm.nullMeasurableSet, tsub_self]
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · rw [Set.iUnion_sdiff]
      exact measure_iUnion_null hnull
    · rw [Set.sdiff_eq_empty.2 (fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩),
        measure_empty]

/-- Definition 4.2.3 agrees with Definition 4.1.4 for the shift on path space: a stationary
process is ergodic iff `(E^ℕ, B(E^ℕ), P̃r, θ)` is an ergodic dynamical system. -/
theorem isErgodicProcess_iff_isErgodic {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    IsErgodicProcess P X ↔ IsErgodic (pathLaw P X) (shift 1) := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  constructor
  · intro h A hA
    have := h A hA.1 (isShiftInvariant_of_preimage_eq hA.2)
    rwa [pathLaw, Measure.map_apply hΦ hA.1]
  · intro h A hAm hA
    obtain ⟨B, hBm, hB, hBA, -⟩ := exists_invariant_ae_eq hmp hAm hA
    have h1 := h B ⟨hBm, hB⟩
    rw [measure_congr hBA, pathLaw, Measure.map_apply hΦ hAm] at h1
    exact h1

/-! ### Theorem 4.2.1 -/

/-- The σ-algebra `I` of Theorem 4.2.1 on `Ω`: the events `{(X₀, X₁, …) ∈ A}` with `A`
transformation invariant for the shift. -/
abbrev invariantField (X : ℕ → Ω → E) : MeasurableSpace Ω :=
  (MeasurableSpace.invariants (shift (X := E) 1)).comap (pathOf X)

/-- Conditional expectations transported from a law: `E[g(Φ) | Φ⁻¹m] = E_{P∘Φ⁻¹}[g | m](Φ)`. -/
theorem condExp_comp_ae_eq {S : Type*} {m : MeasurableSpace S} [mS : MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {Φ : Ω → S} (hΦ : Measurable Φ) (hm : m ≤ mS)
    {g : S → ℝ} (hg : Integrable g (P.map Φ)) :
    P[g ∘ Φ | m.comap Φ] =ᵐ[P] (P.map Φ)[g | m] ∘ Φ := by
  have hle : m.comap Φ ≤ ‹MeasurableSpace Ω› := (MeasurableSpace.comap_mono hm).trans
    hΦ.comap_le
  have hgΦ : Integrable (g ∘ Φ) P := hg.comp_measurable hΦ
  have hc : Integrable ((P.map Φ)[g | m] ∘ Φ) P :=
    integrable_condExp.comp_measurable hΦ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hgΦ (fun s _ _ => hc.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨B, hB, rfl⟩ := hs
    have hBm : MeasurableSet B := hm B hB
    simp only [Function.comp_apply]
    rw [← setIntegral_map hBm (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
      hΦ.aemeasurable, setIntegral_condExp hm hg hB, setIntegral_map hBm hg.1 hΦ.aemeasurable]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable Φ)).aestronglyMeasurable

/-- Miao, (4.3), p. 123: on path space, `(1/N) Σ_{k<N} f(θᵏx) → Ẽ[f | I]` with `f(x) = x₀`,
`P̃r`-a.s. -/
theorem eq_4_3 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hint : Integrable (X 0) P) :
    ∀ᵐ x ∂pathLaw P X, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
      (fun y : ℕ → ℝ => y 0) ((shift 1)^[k] x)) atTop
      (𝓝 ((pathLaw P X)[fun y => y 0 | MeasurableSpace.invariants (shift 1)] x)) := by
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hf : Integrable (fun y : ℕ → ℝ => y 0) (pathLaw P X) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable
      (measurable_pathOf hX).aemeasurable).2 hint
  exact theorem_4_1_1 hmp (measurable_pi_apply 0) hf

/-- **Theorem 4.2.1** (strong law of large numbers, Miao, (4.1), p. 122). For a stationary
real process with `E|X₀| < ∞`, `(1/N) Σ_{k<N} X_k → E[X₀ | I]`, `Pr`-a.s. -/
theorem theorem_4_2_1 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hint : Integrable (X 0) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, X k ω) atTop
      (𝓝 (P[X 0 | invariantField X] ω)) := by
  have hΦ := measurable_pathOf hX
  have hf : Integrable (fun y : ℕ → ℝ => y 0) (P.map (pathOf X)) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable hΦ.aemeasurable).2 hint
  have h1 := ae_of_ae_map hΦ.aemeasurable (eq_4_3 hX hst hint)
  have h2 := condExp_comp_ae_eq hΦ (MeasurableSpace.invariants_le (shift (X := ℝ) 1)) hf
  filter_upwards [h1, h2] with ω hω1 hω2
  have hX0 : (fun y : ℕ → ℝ => y 0) ∘ pathOf X = X 0 := rfl
  rw [invariantField, ← hX0, hω2]
  refine hω1.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one, shift_apply, add_zero]
  rfl

/-- **Theorem 4.2.1** (Miao, (4.2), p. 122): if `X` is also ergodic,
`(1/N) Σ_{k<N} X_k → E X₀`, `Pr`-a.s. -/
theorem theorem_4_2_1_ergodic {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    (hint : Integrable (X 0) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, X k ω) atTop
      (𝓝 (∫ ω, X 0 ω ∂P)) := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hf : Integrable (fun y : ℕ → ℝ => y 0) (pathLaw P X) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable hΦ.aemeasurable).2 hint
  have h := theorem_4_1_1_ergodic hmp ((isErgodicProcess_iff_isErgodic hX hst).1 herg)
    (measurable_pi_apply 0) hf
  have hE : ∫ y, (fun y : ℕ → ℝ => y 0) y ∂pathLaw P X = ∫ ω, X 0 ω ∂P :=
    integral_map hΦ.aemeasurable (measurable_pi_apply 0).aestronglyMeasurable
  rw [hE] at h
  filter_upwards [ae_of_ae_map hΦ.aemeasurable h] with ω hω
  refine hω.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one, shift_apply, add_zero]
  rfl

/-! ### Mixing: Definition 4.2.4 and Theorem 4.2.3 -/

/-- **Definition 4.2.4** (Miao, p. 124). A stationary process is mixing if for all
`A, B ∈ B(E^∞)`, `Pr{(X₁, X₂, …) ∈ A, (Xₙ, Xₙ₊₁, …) ∈ B} − Pr{(X₁, …) ∈ A} Pr{(Xₙ, …) ∈ B} → 0`.
-/
def IsMixing (P : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ A B : Set (ℕ → E), MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℕ => P.real ({ω | shift 1 (pathOf X ω) ∈ A} ∩ {ω | shift n (pathOf X ω) ∈ B})
      - P.real {ω | shift 1 (pathOf X ω) ∈ A} * P.real {ω | shift n (pathOf X ω) ∈ B}) atTop
      (𝓝 0)

/-- **Theorem 4.2.3** (Miao, p. 124). A mixing (stationary) process is ergodic. -/
theorem theorem_4_2_3 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hmix : IsMixing P X) :
    IsErgodicProcess P X := by
  intro A hAm hA
  have hΦ := measurable_pathOf hX
  have hlaw := (isStationary_iff_map_shift hX).1 hst
  -- `Pr{(Xₙ, Xₙ₊₁, …) ∈ A} = Pr{(X₀, X₁, …) ∈ A}` for every `n`
  have hstat : ∀ n, P.real {ω | shift n (pathOf X ω) ∈ A} = P.real (pathOf X ⁻¹' A) := by
    intro n
    have h := congrArg (fun m : Measure (ℕ → E) => m.real A) (hlaw n)
    simp only [pathLaw] at h
    rw [map_measureReal_apply (measurable_shift n) hAm, map_measureReal_apply hΦ
      ((measurable_shift n) hAm), map_measureReal_apply hΦ hAm] at h
    exact h
  -- `(X₁, …) ∈ A` implies `(Xₙ, …) ∈ A` for `n ≥ 1`
  have hsub : ∀ n, 1 ≤ n → {ω | shift 1 (pathOf X ω) ∈ A} ⊆ {ω | shift n (pathOf X ω) ∈ A} := by
    intro n hn ω hω
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => exact hω
    | succ k ih =>
      have := hA _ (ih (by omega))
      simp only [Set.mem_ofPred_eq, shift_shift] at this ⊢
      rwa [add_assoc] at this
  set p := P.real (pathOf X ⁻¹' A) with hp
  have hlim := hmix A A hAm hAm
  have hev : ∀ᶠ n : ℕ in atTop, P.real ({ω | shift 1 (pathOf X ω) ∈ A} ∩
      {ω | shift n (pathOf X ω) ∈ A}) - P.real {ω | shift 1 (pathOf X ω) ∈ A} *
      P.real {ω | shift n (pathOf X ω) ∈ A} = p - p * p := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Set.inter_eq_left.2 (hsub n hn), hstat 1, hstat n]
  have hpp : p - p * p = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono
    fun n h => h.symm)) hlim
  have hp01 : p = 0 ∨ p = 1 := by
    have : p * (1 - p) = 0 := by linarith [hpp]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hm : MeasurableSet (pathOf X ⁻¹' A) := hΦ hAm
  rcases hp01 with h | h
  · left
    rw [hp, measureReal_eq_zero_iff] at h
    exact h
  · right
    rw [hp, measureReal_def, ENNReal.toReal_eq_one_iff] at h
    exact h

/-! ### The setting of Theorem 4.2.4 -/

omit [MeasurableSpace Ω] in
/-- Miao, p. 124 (setting of Theorem 4.2.4): if `M₀ ⊆ θ⁻¹M₀`, the σ-algebras `M_k = θ⁻ᵏM₀`
increase. (The central limit theorem of Theorem 4.2.4 is not formalised.) -/
theorem theorem_4_2_4_filtration_mono (θ : Ω → Ω) (M₀ : MeasurableSpace Ω)
    (h : M₀ ≤ M₀.comap θ) (k : ℕ) : M₀.comap θ^[k] ≤ M₀.comap θ^[k + 1] := by
  rw [Function.iterate_succ', ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono h

end Miao.StructuralEstimation
