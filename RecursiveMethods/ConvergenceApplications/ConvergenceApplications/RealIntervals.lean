/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.MonotoneProcesses

/-!
# Theorem 12.12 on real intervals and on rectangles

Theorem 12.12 (`theorem_12_12`) is stated for order intervals `[a, b]` of `ℝˡ = Fin l → ℝ`. The
models of Chapter 13 live on a real interval `[a, b] ⊆ ℝ` (§§13.3, 13.5) or on a rectangle
`[a, b] ⊆ ℝ × ℝ` (§§13.4, 13.8). This file transports the theorem along an order isomorphism
that is a homeomorphism.

* `transportK`: the kernel `κ′(t) = κ(e⁻¹t) ∘ e⁻¹` on `T` of a kernel `κ` on `S`.
* `theorem_12_12_of_orderIso`: Theorem 12.12 on any `S` order-isomorphic and homeomorphic to an
  order interval of `ℝˡ`, with Assumption 12.1 at the images of the endpoints.
* `theorem_12_12_real` (`S = [a, b] ⊆ ℝ`, through `ℝ¹`) and `theorem_12_12_prod`
  (`S = [a, b] ⊆ ℝ × ℝ` with the coordinatewise order, through `ℝ²`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- The kernel on `T` of a kernel `κ` on `S`, transported along `e : S → T` with inverse `e'`:
`κ′(t) = κ(e′ t)` pushed forward by `e`. -/
noncomputable def transportK (e : S → T) (e' : T → S) (he' : Measurable e') (κ : Kernel S S) :
    Kernel T T :=
  Kernel.map (κ.comap e' he') e

variable {e : S → T} {e' : T → S} (he : Measurable e) (he' : Measurable e')
  (hl : ∀ s, e' (e s) = s) (hr : ∀ t, e (e' t) = t) (κ : Kernel S S)

include he in
theorem transportK_apply (t : T) : transportK e e' he' κ t = (κ (e' t)).map e := by
  rw [transportK, Kernel.map_apply _ he, Kernel.comap_apply]

include he in
theorem isMarkovKernel_transportK [IsMarkovKernel κ] : IsMarkovKernel (transportK e e' he' κ) :=
  Kernel.IsMarkovKernel.map _ he

include he hl in
/-- `T′*(ν ∘ e⁻¹) = (T*ν) ∘ e⁻¹`. -/
theorem adjointOp_transportK_map (ν : Measure S) :
    adjointOp (transportK e e' he' κ) (ν.map e) = (adjointOp κ ν).map e := by
  ext A hA
  rw [adjointOp_apply _ _ hA, Measure.map_apply he hA, adjointOp_apply _ _ (he hA),
    lintegral_map (Kernel.measurable_coe _ hA) he]
  refine lintegral_congr fun s => ?_
  rw [transportK_apply he he' κ, hl, Measure.map_apply he hA]

include he hl in
theorem iterate_transportK_map (ν : Measure S) (n : ℕ) :
    (adjointOp (transportK e e' he' κ))^[n] (ν.map e) = ((adjointOp κ)^[n] ν).map e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      adjointOp_transportK_map he he' hl]

include he hl hr in
theorem kpow_transportK (n : ℕ) (t : T) :
    kpow (transportK e e' he' κ) n t = (kpow κ n (e' t)).map e := by
  rw [← iterate_dirac, ← iterate_dirac,
    show Measure.dirac t = (Measure.dirac (e' t)).map e by rw [Measure.map_dirac' he, hr],
    iterate_transportK_map he he' hl]

include he in
theorem markovOpR_transportK {f : T → ℝ} (hf : Measurable f) (t : T) :
    markovOpR (transportK e e' he' κ) f t = markovOpR κ (f ∘ e) (e' t) := by
  rw [markovOpR, markovOpR, transportK_apply he he' κ,
    integral_map he.aemeasurable hf.aestronglyMeasurable]
  rfl

variable [MetricSpace S] [BorelSpace S] [PartialOrder S] {l : ℕ} {a b : Fin l → ℝ}

/-- **Theorem 12.12**, transported. Let `S` be order-isomorphic and homeomorphic to an order
interval `[a, b]` of `ℝˡ` by `e`. If `P` on `S` is monotone and Feller, and for some `c`, `ε > 0`,
`N ≥ 1`, `Pᴺ(e⁻¹a, [c, ∞)) ≥ ε` and `Pᴺ(e⁻¹b, (−∞, c]) ≥ ε` (Assumption 12.1), then `P` has a
unique invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12_of_orderIso (hab : a ≤ b) (e : S ≃o Icc a b) (he : Continuous e)
    (he' : Continuous e.symm) (κ : Kernel S S) [IsMarkovKernel κ] (hM : IsMonotoneTF κ)
    (hF : IsFeller κ) {c : S} {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hbot : ε ≤ (kpow κ N (e.symm (IccBot hab))).real (Ici c))
    (htop : ε ≤ (kpow κ N (e.symm (IccTop hab))).real (Iic c)) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure S, IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure S, IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  have hem := he.measurable
  have hem' := he'.measurable
  have hl : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  have hr : ∀ t, e (e.symm t) = t := e.apply_symm_apply
  set κ' := transportK e e.symm hem' κ
  have := isMarkovKernel_transportK hem hem' κ
  -- monotone and Feller transfer
  have hM' : IsMonotoneTF κ' := fun f hf hb hm t t' htt' => by
    rw [markovOpR_transportK hem hem' κ hf, markovOpR_transportK hem hem' κ hf]
    obtain ⟨B, hB⟩ := hb
    exact hM (f ∘ e) (hf.comp hem) ⟨B, fun s => hB _⟩ (hm.comp e.monotone) (e.symm.monotone htt')
  have hF' : IsFeller κ' := fun f hf hb => by
    have hfun : markovOpR κ' f = markovOpR κ (f ∘ e) ∘ e.symm :=
      funext fun t => markovOpR_transportK hem hem' κ hf.measurable t
    rw [hfun]
    obtain ⟨B, hB⟩ := hb
    exact (hF (f ∘ e) (hf.comp he) ⟨B, fun s => hB _⟩).comp he'
  -- Assumption 12.1 transfers
  have hpre : ∀ (n : ℕ) (t : Icc a b) {A : Set (Icc a b)}, MeasurableSet A →
      (kpow κ' n t).real A = (kpow κ n (e.symm t)).real (e ⁻¹' A) := fun n t A hA => by
    rw [kpow_transportK hem hem' hl hr κ, measureReal_def, Measure.map_apply hem hA,
      measureReal_def]
  have hA : Assumption12_1 hab κ' (e c) ε N := by
    refine ⟨hε, hN, ?_, ?_⟩
    · rw [hpre N _ measurableSet_Ici]
      convert hbot using 2
      ext s; simp
    · rw [hpre N _ measurableSet_Iic]
      convert htop using 2
      ext s; simp
  obtain ⟨μ', hμ', hfix', huniq', hconv'⟩ := theorem_12_12 hab κ' hM' hF' hA
  have hmap : ∀ ν : Measure S, (ν.map e).map e.symm = ν := fun ν => by
    rw [Measure.map_map hem' hem]
    have : (e.symm ∘ e) = id := funext hl
    rw [this, Measure.map_id]
  set μ := μ'.map e.symm
  have hμe : μ.map e = μ' := by
    rw [Measure.map_map hem hem']
    have : (e ∘ e.symm) = id := funext hr
    rw [this, Measure.map_id]
  have hμ : IsProbabilityMeasure μ := inferInstance
  have hfix : adjointOp κ μ = μ := by
    have h1 := adjointOp_transportK_map hem hem' hl κ μ
    rw [hμe, hfix'] at h1
    rw [← hmap (adjointOp κ μ), ← h1]
  refine ⟨μ, hμ, hfix, fun ν hν hνfix => ?_, fun lam₀ hlam₀ f => ?_⟩
  · have : IsProbabilityMeasure (ν.map e) := inferInstance
    have h1 := adjointOp_transportK_map hem hem' hl κ ν
    rw [hνfix] at h1
    rw [← hmap ν, huniq' _ this h1]
  · have : IsProbabilityMeasure (lam₀.map e) := inferInstance
    set g : Icc a b →ᵇ ℝ := f.compContinuous ⟨e.symm, he'⟩
    have hlim := hconv' _ this g
    have hg : ∀ ν : Measure S, ∫ t, g t ∂(ν.map e) = ∫ s, f s ∂ν := fun ν => by
      rw [integral_map hem.aemeasurable g.continuous.measurable.aestronglyMeasurable]
      simp [g, hl]
    have heq : ∀ n, ∫ t, g t ∂((adjointOp κ')^[n] (lam₀.map e)) =
        ∫ s, f s ∂((adjointOp κ)^[n] lam₀) := fun n => by
      rw [iterate_transportK_map hem hem' hl κ, hg]
    rw [← hμe, hg] at hlim
    exact hlim.congr heq

/-! ### Real intervals -/

/-- `[a, b] ⊆ ℝ` is order-isomorphic to the order interval `[a, b]` of `ℝ¹`. -/
def realToFin1 (a b : ℝ) : Icc a b ≃o Icc (fun _ : Fin 1 => a) (fun _ => b) where
  toFun x := ⟨fun _ => x.1, fun _ => x.2.1, fun _ => x.2.2⟩
  invFun t := ⟨t.1 0, t.2.1 0, t.2.2 0⟩
  left_inv x := rfl
  right_inv t := by ext i; fin_cases i; rfl
  map_rel_iff' {x y} := by
    change ((fun _ : Fin 1 => x.1) ≤ fun _ => y.1) ↔ x ≤ y
    rw [Pi.le_def]
    exact ⟨fun h => h 0, fun h _ => h⟩

theorem continuous_realToFin1 (a b : ℝ) : Continuous (realToFin1 a b) :=
  Continuous.subtype_mk (continuous_pi fun _ => continuous_subtype_val) _

theorem continuous_realToFin1_symm (a b : ℝ) : Continuous (realToFin1 a b).symm :=
  Continuous.subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _

/-- **Theorem 12.12** on a real interval `[a, b]`: a monotone Feller `P` with `Pᴺ(a, [c, b]) ≥ ε`
and `Pᴺ(b, [a, c]) ≥ ε` (`ε > 0`, `N ≥ 1`) has a unique invariant probability measure `λ*`, and
`T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12_real {a b : ℝ} (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b))
    [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hN : 1 ≤ N)
    (hbot : ε ≤ (kpow κ N ⟨a, left_mem_Icc.2 hab⟩).real (Ici c))
    (htop : ε ≤ (kpow κ N ⟨b, right_mem_Icc.2 hab⟩).real (Iic c)) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ :=
  theorem_12_12_of_orderIso (a := fun _ : Fin 1 => a) (b := fun _ => b) (fun _ => hab)
    (realToFin1 a b) (continuous_realToFin1 a b) (continuous_realToFin1_symm a b) κ hM hF hε hN
    hbot htop

/-! ### Rectangles in `ℝ × ℝ` -/

/-- `[a, b] ⊆ ℝ × ℝ` (coordinatewise order) is order-isomorphic to the order interval
`[(a₁, a₂), (b₁, b₂)]` of `ℝ²`. -/
def prodToFin2 (a b : ℝ × ℝ) : Icc a b ≃o Icc ![a.1, a.2] ![b.1, b.2] where
  toFun x := ⟨![x.1.1, x.1.2], fun i => by fin_cases i <;> simp [x.2.1.1, x.2.1.2],
    fun i => by fin_cases i <;> simp [x.2.2.1, x.2.2.2]⟩
  invFun t := ⟨(t.1 0, t.1 1), ⟨by simpa using t.2.1 0, by simpa using t.2.1 1⟩,
    ⟨by simpa using t.2.2 0, by simpa using t.2.2 1⟩⟩
  left_inv x := rfl
  right_inv t := by ext i; fin_cases i <;> rfl
  map_rel_iff' {x y} := by
    change (![x.1.1, x.1.2] ≤ ![y.1.1, y.1.2]) ↔ x ≤ y
    rw [Pi.le_def, Fin.forall_fin_two, Subtype.mk_le_mk, Prod.le_def]
    simp

theorem continuous_prodToFin2 (a b : ℝ × ℝ) : Continuous (prodToFin2 a b) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  fin_cases i
  · exact continuous_fst.comp continuous_subtype_val
  · exact continuous_snd.comp continuous_subtype_val

theorem continuous_prodToFin2_symm (a b : ℝ × ℝ) : Continuous (prodToFin2 a b).symm :=
  Continuous.subtype_mk (((continuous_apply 0).comp continuous_subtype_val).prodMk
    ((continuous_apply 1).comp continuous_subtype_val)) _

/-- **Theorem 12.12** on a rectangle `[a, b] ⊆ ℝ × ℝ` with the coordinatewise order. -/
theorem theorem_12_12_prod {a b : ℝ × ℝ} (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b))
    [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hN : 1 ≤ N)
    (hbot : ε ≤ (kpow κ N ⟨a, left_mem_Icc.2 hab⟩).real (Ici c))
    (htop : ε ≤ (kpow κ N ⟨b, right_mem_Icc.2 hab⟩).real (Iic c)) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  have hab' : ![a.1, a.2] ≤ ![b.1, b.2] := by
    rw [Pi.le_def, Fin.forall_fin_two]; exact ⟨by simpa using hab.1, by simpa using hab.2⟩
  exact theorem_12_12_of_orderIso hab' (prodToFin2 a b) (continuous_prodToFin2 a b)
    (continuous_prodToFin2_symm a b) κ hM hF hε hN hbot htop

end StokeyLucasPrescott.ConvergenceApplications
