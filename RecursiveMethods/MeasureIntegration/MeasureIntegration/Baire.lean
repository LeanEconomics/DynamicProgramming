/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.MeasurableFunctions

/-!
# Baire functions

SLP Exercise 7.13b, p. 182: the Baire functions — the continuous functions, their pointwise
limits, the pointwise limits of those, and so on (`IsBaire`: the smallest class containing the
continuous functions and closed under pointwise limits of sequences) — are exactly the Borel
measurable functions (`ex_7_13b`). Stated on any metric space; the book's case is `ℝˡ`.

* Baire ⇒ Borel: Theorem 7.4.
* Borel ⇒ Baire: the class is closed under continuous combinations `Φ(f, g)`
  (`IsBaire.comp₂`); the sets whose indicators are Baire form a σ-algebra
  (`baireSets`) containing the open sets (an open indicator is the limit of
  `min(1, n·dist(x, Uᶜ))`), so every Borel indicator is Baire; measurable functions with finite
  range are then Baire (`IsBaire.of_finite_range`), and Theorem 7.5 finishes.
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory MeasurableSpace Filter Topology

variable {X : Type*}

/-- The **Baire functions** (SLP Exercise 7.13b): the functions in every class that contains
the continuous functions and is closed under pointwise limits of sequences. -/
def IsBaire [TopologicalSpace X] (f : X → ℝ) : Prop :=
  ∀ 𝒦 : Set (X → ℝ), (∀ g, Continuous g → g ∈ 𝒦) →
    (∀ (u : ℕ → X → ℝ) (g : X → ℝ), (∀ n, u n ∈ 𝒦) →
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) → g ∈ 𝒦) → f ∈ 𝒦

/-- Continuous functions are Baire. -/
theorem IsBaire.continuous [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) : IsBaire f :=
  fun _ hc _ => hc f hf

/-- Pointwise limits of Baire functions are Baire. -/
theorem IsBaire.lim [TopologicalSpace X] {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, IsBaire (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : IsBaire g :=
  fun 𝒦 hc hl => hl f g (fun n => hf n 𝒦 hc hl) hlim

/-- Induction over the Baire functions. -/
theorem IsBaire.induction [TopologicalSpace X] {P : (X → ℝ) → Prop}
    (hc : ∀ f, Continuous f → P f)
    (hl : ∀ (u : ℕ → X → ℝ) (g : X → ℝ), (∀ n, P (u n)) →
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) → P g) {f : X → ℝ} (hf : IsBaire f) :
    P f :=
  hf {f | P f} hc hl

/-- A continuous combination of a Baire function and a continuous function is Baire. -/
theorem IsBaire.comp₂_continuous [TopologicalSpace X] {Φ : ℝ × ℝ → ℝ} (hΦ : Continuous Φ)
    {f g : X → ℝ}
    (hf : IsBaire f) (hg : Continuous g) : IsBaire fun x => Φ (f x, g x) :=
  IsBaire.induction (P := fun f => IsBaire fun x => Φ (f x, g x))
    (fun _ hf => .continuous (hΦ.comp (hf.prodMk hg)))
    (fun _ _ ih hlim => .lim ih fun x =>
      (hΦ.tendsto _).comp ((hlim x).prodMk_nhds tendsto_const_nhds)) hf

/-- **The Baire functions are closed under continuous combinations** `Φ(f, g)`. -/
theorem IsBaire.comp₂ [TopologicalSpace X] {Φ : ℝ × ℝ → ℝ} (hΦ : Continuous Φ) {f g : X → ℝ}
    (hf : IsBaire f)
    (hg : IsBaire g) : IsBaire fun x => Φ (f x, g x) :=
  IsBaire.induction (P := fun g => IsBaire fun x => Φ (f x, g x))
    (fun _ hg => hf.comp₂_continuous hΦ hg)
    (fun _ _ ih hlim => .lim ih fun x =>
      (hΦ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (hlim x))) hg

theorem IsBaire.add [TopologicalSpace X] {f g : X → ℝ} (hf : IsBaire f) (hg : IsBaire g) :
    IsBaire (f + g) :=
  hf.comp₂ (Φ := fun p => p.1 + p.2) (by fun_prop) hg

theorem IsBaire.maxFn [TopologicalSpace X] {f g : X → ℝ} (hf : IsBaire f) (hg : IsBaire g) :
    IsBaire fun x => max (f x) (g x) :=
  hf.comp₂ (Φ := fun p => max p.1 p.2) (by fun_prop) hg

theorem IsBaire.const_mul [TopologicalSpace X] {f : X → ℝ} (hf : IsBaire f) (c : ℝ) :
    IsBaire fun x => c * f x :=
  hf.comp₂ (Φ := fun p => c * p.1) (g := fun _ => (0 : ℝ)) (by fun_prop)
    (.continuous continuous_const)

theorem IsBaire.one_sub [TopologicalSpace X] {f : X → ℝ} (hf : IsBaire f) :
    IsBaire fun x => 1 - f x :=
  hf.comp₂ (Φ := fun p => 1 - p.1) (g := fun _ => (0 : ℝ)) (by fun_prop)
    (.continuous continuous_const)

theorem IsBaire.congr [TopologicalSpace X] {f g : X → ℝ} (hf : IsBaire f) (h : f = g) :
    IsBaire g := h ▸ hf

/-- The sets whose indicator function is Baire form a σ-algebra. -/
abbrev baireSets [TopologicalSpace X] : MeasurableSpace X where
  MeasurableSet' A := IsBaire (A.indicator fun _ => (1 : ℝ))
  measurableSet_empty := by
    rw [indicator_empty]
    exact .continuous continuous_const
  measurableSet_compl A hA := by
    refine hA.one_sub.congr (funext fun x => ?_)
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx]
  measurableSet_iUnion A hA := by
    have hacc : ∀ N, IsBaire ((accumulate A N).indicator fun _ => (1 : ℝ)) := by
      intro N
      induction N with
      | zero =>
        refine (hA 0).congr (funext fun x => ?_)
        simp [accumulate_zero_nat]
      | succ N ih =>
        refine (ih.maxFn (hA (N + 1))).congr (funext fun x => ?_)
        rw [accumulate_succ]
        by_cases h1 : x ∈ accumulate A N <;> by_cases h2 : x ∈ A (N + 1) <;> simp [h1, h2]
    refine .lim hacc fun x => ?_
    by_cases hx : x ∈ ⋃ n, A n
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      rw [indicator_of_mem hx]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with N hN
      rw [indicator_of_mem (mem_accumulate.2 ⟨n, hN, hn⟩)]
    · rw [indicator_of_notMem hx]
      refine tendsto_const_nhds.congr fun N => ?_
      rw [indicator_of_notMem fun h => hx (accumulate_subset_iUnion N h)]


variable [MetricSpace X]

/-- The indicator of an open set is Baire: it is the limit of `min(1, n·dist(x, Uᶜ))`. -/
theorem isBaire_indicator_open {U : Set X} (hU : IsOpen U) :
    IsBaire (U.indicator fun _ => (1 : ℝ)) := by
  by_cases huniv : U = univ
  · subst huniv
    simpa using (IsBaire.continuous (X := X) (continuous_const (y := (1 : ℝ))))
  have hne : (Uᶜ).Nonempty := nonempty_compl.2 huniv
  refine .lim (f := fun n x => min 1 (n * Metric.infDist x Uᶜ))
    (fun n => .continuous (by fun_prop)) fun x => ?_
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx]
    have hpos : 0 < Metric.infDist x Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h hx)
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist x Uᶜ)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [min_eq_left]
    have : (1 : ℝ) / Metric.infDist x Uᶜ ≤ n := hN.le.trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hpos] at this
    linarith
  · rw [indicator_of_notMem hx, Metric.infDist_zero_of_mem (mem_compl hx)]
    simp

variable [MeasurableSpace X] [BorelSpace X]

/-- Every Borel set has a Baire indicator. -/
theorem isBaire_indicator {A : Set X} (hA : MeasurableSet A) :
    IsBaire (A.indicator fun _ => (1 : ℝ)) := by
  have hle : borel X ≤ baireSets := generateFrom_le fun U hU => isBaire_indicator_open hU
  rw [← BorelSpace.measurable_eq (α := X)] at hle
  exact hle A hA

/-- A measurable function with finitely many values is Baire. -/
theorem IsBaire.of_finite_range {g : X → ℝ} (hg : Measurable g) (hfin : (range g).Finite) :
    IsBaire g := by
  classical
  have hsum : ∀ F : Finset ℝ, IsBaire fun x => ∑ v ∈ F, v * (g ⁻¹' {v}).indicator 1 x := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using IsBaire.continuous (X := X) (continuous_const (y := (0 : ℝ)))
    | insert v F hv ih =>
      refine (((isBaire_indicator (hg (measurableSet_singleton v))).const_mul v).add ih).congr ?_
      funext x
      rw [Finset.sum_insert hv]
      rfl
  refine (hsum hfin.toFinset).congr (funext fun x => ?_)
  rw [Finset.sum_eq_single (g x)]
  · simp
  · intro v _ hv
    rw [indicator_of_notMem (show x ∉ g ⁻¹' {v} from fun h => hv (mem_singleton_iff.1 h).symm),
      mul_zero]
  · intro h
    exact absurd (hfin.mem_toFinset.2 (mem_range_self x)) h

/-- **Exercise 7.13b.** The Baire functions are exactly the Borel measurable functions. -/
theorem ex_7_13b {f : X → ℝ} : IsBaire f ↔ Measurable f := by
  constructor
  · exact IsBaire.induction (P := Measurable) (fun _ hf => hf.measurable)
      (fun _ _ ih hlim => theorem_7_4 ih hlim)
  · intro hf
    obtain ⟨φ, hφ, hlim, -, -⟩ := theorem_7_5 hf
    exact .lim (fun n => IsBaire.of_finite_range (hφ n).1 (hφ n).2) hlim

end StokeyLucasPrescott.MeasureIntegration
