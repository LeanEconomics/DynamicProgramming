/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Theorem 14.14: the Riesz representation theorem for signed measures

SLP §14.2, p. 435. The book: `S ⊆ ℝˡ` compact with its Borel sets, `C(S)` the bounded continuous
functions `S → ℝ`; if `T : C(S) → ℝ` is a continuous linear functional, there is a unique signed
measure `ν` with `T f = ∫ f dν` for all `f ∈ C(S)`. The book reuses the letter `T` (elsewhere the
Markov operator) for the functional; here it is `Λ`. The book gives no proof, referring to
Royden (1968, Theorem 8, pp. 310–311).

Here `S` is any compact metric space with its Borel σ-algebra (more general than the book),
`C(S)` is `S →ᵇ ℝ` with the sup norm, and `Λ : StrongDual ℝ (S →ᵇ ℝ)`. Signed measures are
Mathlib's `SignedMeasure S`, and the integral of `f` against `ν` is `sIntegral ν f`
`= ∫ f dν⁺ − ∫ f dν⁻` (Jordan decomposition of `ν`).

* `theorem_14_14_exists`: `Λ f = ∫ f dμ₁ − ∫ f dμ₂` for two finite Borel measures `μ₁, μ₂`.
* `theorem_14_14_unique`: a signed measure is determined by its integrals of `f ∈ C(S)`;
  `theorem_14_14_unique_measures` is the same for the pairs `(μ₁, μ₂)` (unique as `μ₁ − μ₂`).
* `theorem_14_14`: `∃! ν : SignedMeasure S, ∀ f, Λ f = sIntegral ν f`.
* `theorem_14_14_prob`: for nonempty `S`, `Λ f = α₁ ∫ f dλ₁ − α₂ ∫ f dλ₂` with `λ₁, λ₂`
  probability measures and `α₁, α₂ ≥ 0` (the form the book uses).

Proof route (Royden's).
1. *Jordan decomposition of the functional* (`functional_jordanDecomposition`). For `f ≥ 0` put
   `Λ⁺ f = sup {Λ g : 0 ≤ g ≤ f}` (`rieszPosSup`; bounded by `‖Λ‖ ‖f‖`). It is additive
   (`rieszPosSup_add`, splitting `0 ≤ g ≤ a + b` as `g ⊓ a + (g − g ⊓ a)`) and positively
   homogeneous (`rieszPosSup_smul`). Extend by `Λ⁺ f = Λ⁺ (f ⊔ 0) − Λ⁺ ((−f) ⊔ 0)`
   (`rieszPosPart`); independence of the decomposition (`rieszPosPart_sub`) makes it linear
   (`rieszPosPartLM`). Then `Λ⁺ ≥ 0` and `Λ⁻ := Λ⁺ − Λ ≥ 0`.
2. *Positive functionals are measures* (`exists_measure_of_positive`): Mathlib's
   Riesz–Markov–Kakutani theorem `RealRMK.integral_rieszMeasure` on `C_c(S, ℝ)`, which on a
   compact space is all of `C(S)`; the measure is finite.
3. *Uniqueness*: finite Borel measures on a metric space are determined by integrals of bounded
   continuous functions (`ext_of_forall_integral_eq_of_IsFiniteMeasure`). If `ν, ν'` integrate
   every `f` equally, then `ν⁺ + ν'⁻ = ν'⁺ + ν⁻`, hence `ν = ν'`.

Only the representation half is used later in the book (for Lemma 14.9); the isometry between
`C(S)*` and the signed measures with the total-variation norm is not formalised.
-/

open MeasureTheory BoundedContinuousFunction Set
open scoped BoundedContinuousFunction CompactlySupported

namespace StokeyLucasPrescott.LawsOfLargeNumbers

/-- The positive part of `Λ` evaluated at `f ≥ 0`:
`Λ⁺ f = sup {Λ g : g ∈ C(S), 0 ≤ g ≤ f}` (Royden's construction). For `f` not nonnegative the
set is empty and the value is junk; only `f ≥ 0` is used. -/
noncomputable def rieszPosSup {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f : S →ᵇ ℝ) : ℝ :=
  sSup (Λ '' {g | 0 ≤ g ∧ g ≤ f})

/-- The set `{Λ g : 0 ≤ g ≤ f}` is bounded above by `‖Λ‖ ‖f‖`; this is where continuity of `Λ` is
used. -/
theorem rieszPosSup_bddAbove {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f : S →ᵇ ℝ) : BddAbove (Λ '' {g | 0 ≤ g ∧ g ≤ f}) := by
  refine ⟨‖Λ‖ * ‖f‖, ?_⟩
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  have hg : ‖g‖ ≤ ‖f‖ := by
    refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x => ?_
    have h0 : 0 ≤ g x := hg0 x
    have h1 : g x ≤ f x := hgf x
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.trans ((le_abs_self (f x)).trans
      (by simpa [Real.norm_eq_abs] using norm_coe_le_norm f x))
  calc Λ g ≤ ‖Λ g‖ := Real.le_norm_self _
    _ ≤ ‖Λ‖ * ‖g‖ := Λ.le_opNorm g
    _ ≤ ‖Λ‖ * ‖f‖ := mul_le_mul_of_nonneg_left hg (norm_nonneg Λ)

/-- Every `Λ g` with `0 ≤ g ≤ f` is at most `Λ⁺ f`. -/
theorem le_rieszPosSup {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f g : S →ᵇ ℝ} (hg0 : 0 ≤ g) (hgf : g ≤ f) : Λ g ≤ rieszPosSup Λ f :=
  le_csSup (rieszPosSup_bddAbove Λ f) ⟨g, ⟨hg0, hgf⟩, rfl⟩

/-- `Λ⁺ f ≤ c` as soon as `Λ g ≤ c` for every `0 ≤ g ≤ f` (for `f ≥ 0`, so that `g = 0` is a
witness of non-emptiness). -/
theorem rieszPosSup_le {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) {c : ℝ} (h : ∀ g : S →ᵇ ℝ, 0 ≤ g → g ≤ f → Λ g ≤ c) :
    rieszPosSup Λ f ≤ c := by
  refine csSup_le ⟨Λ 0, 0, ⟨le_rfl, hf⟩, rfl⟩ ?_
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  exact h g hg0 hgf

/-- `Λ⁺ 0 = 0`. -/
theorem rieszPosSup_zero {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    rieszPosSup Λ 0 = 0 := by
  refine le_antisymm (rieszPosSup_le Λ le_rfl fun g hg0 hg => ?_) ?_
  · rw [le_antisymm hg hg0, map_zero]
  · simpa using le_rieszPosSup Λ (le_refl (0 : S →ᵇ ℝ)) le_rfl

/-- `Λ⁺` is additive on nonnegative functions. For `≤`, a function `0 ≤ g ≤ a + b` splits as
`g = g ⊓ a + (g − g ⊓ a)` with `0 ≤ g ⊓ a ≤ a` and `0 ≤ g − g ⊓ a ≤ b`. -/
theorem rieszPosSup_add {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {a b : S →ᵇ ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rieszPosSup Λ (a + b) = rieszPosSup Λ a + rieszPosSup Λ b := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  refine le_antisymm (rieszPosSup_le Λ hab fun g hg0 hg => ?_) ?_
  · have h1 : 0 ≤ g ⊓ a := le_inf hg0 ha
    have h2 : g ⊓ a ≤ a := inf_le_right
    have h3 : 0 ≤ g - g ⊓ a := sub_nonneg.2 inf_le_left
    have h4 : g - g ⊓ a ≤ b := by
      intro x
      have hx : g x ≤ a x + b x := hg x
      change (g - g ⊓ a) x ≤ b x
      simp only [coe_sub, coe_inf, Pi.sub_apply, Pi.inf_apply]
      rcases le_total (g x) (a x) with h | h
      · have hbx : 0 ≤ b x := hb x
        rw [inf_eq_left.2 h]; linarith
      · rw [inf_eq_right.2 h]; linarith
    have e : g = g ⊓ a + (g - g ⊓ a) := by abel
    rw [e, map_add]
    exact add_le_add (le_rieszPosSup Λ h1 h2) (le_rieszPosSup Λ h3 h4)
  · rw [← le_sub_iff_add_le]
    refine rieszPosSup_le Λ ha fun g hg0 hga => ?_
    rw [le_sub_comm]
    refine rieszPosSup_le Λ hb fun h hh0 hhb => ?_
    rw [le_sub_iff_add_le, ← map_add]
    exact le_rieszPosSup Λ (add_nonneg hh0 hg0) (by rw [add_comm a b]; exact add_le_add hhb hga)

/-- A nonnegative multiple of a nonnegative bounded continuous function is nonnegative. -/
theorem bcf_smul_nonneg {S : Type*} [TopologicalSpace S] {c : ℝ} (hc : 0 ≤ c)
    {a : S →ᵇ ℝ} (ha : 0 ≤ a) : 0 ≤ c • a := fun x => by
  have hax : 0 ≤ a x := ha x
  change 0 ≤ (c • a) x
  simp only [coe_smul, smul_eq_mul]
  exact mul_nonneg hc hax

/-- Multiplication by a nonnegative scalar is monotone on bounded continuous functions. -/
theorem bcf_smul_le {S : Type*} [TopologicalSpace S] {c : ℝ} (hc : 0 ≤ c)
    {a b : S →ᵇ ℝ} (hab : a ≤ b) : c • a ≤ c • b := fun x => by
  have hx : a x ≤ b x := hab x
  change (c • a) x ≤ (c • b) x
  simp only [coe_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hx hc

/-- `Λ⁺` is positively homogeneous on nonnegative functions: `Λ⁺ (c f) = c Λ⁺ f` for `c ≥ 0`. -/
theorem rieszPosSup_smul {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {c : ℝ} (hc : 0 ≤ c) {a : S →ᵇ ℝ} (ha : 0 ≤ a) :
    rieszPosSup Λ (c • a) = c * rieszPosSup Λ a := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, rieszPosSup_zero, zero_mul]
  have hca : 0 ≤ c • a := bcf_smul_nonneg hc.le ha
  refine le_antisymm (rieszPosSup_le Λ hca fun g hg0 hg => ?_) ?_
  · have h1 : 0 ≤ c⁻¹ • g := bcf_smul_nonneg (inv_nonneg.2 hc.le) hg0
    have h2 : c⁻¹ • g ≤ a := by
      intro x
      have hx : g x ≤ c * a x := hg x
      change (c⁻¹ • g) x ≤ a x
      simp only [coe_smul, smul_eq_mul]
      rw [inv_mul_le_iff₀ hc]
      exact hx
    have e : g = c • (c⁻¹ • g) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [e, map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (le_rieszPosSup Λ h1 h2) hc.le
  · rw [← le_div_iff₀' hc]
    refine rieszPosSup_le Λ ha fun g hg0 hga => ?_
    rw [le_div_iff₀' hc, ← smul_eq_mul, ← map_smul]
    exact le_rieszPosSup Λ (bcf_smul_nonneg hc.le hg0) (bcf_smul_le hc.le hga)

/-- Every bounded continuous function is the difference of its positive and negative parts:
`f = f ⊔ 0 − (−f) ⊔ 0`. -/
theorem bcf_eq_posPart_sub_negPart {S : Type*} [TopologicalSpace S] (f : S →ᵇ ℝ) :
    f = f ⊔ 0 - (-f) ⊔ 0 := by
  ext x
  simp only [coe_sub, coe_sup, coe_neg, coe_zero, Pi.sub_apply, Pi.sup_apply, Pi.neg_apply,
    Pi.zero_apply]
  rw [max_def, max_def]
  split_ifs <;> linarith

/-- The extension of `Λ⁺` to all of `C(S)`: `Λ⁺ f = Λ⁺ (f ⊔ 0) − Λ⁺ ((−f) ⊔ 0)`. -/
noncomputable def rieszPosPart {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f : S →ᵇ ℝ) : ℝ :=
  rieszPosSup Λ (f ⊔ 0) - rieszPosSup Λ ((-f) ⊔ 0)

/-- Independence of the decomposition: if `a, b ≥ 0` then `Λ⁺ (a − b) = Λ⁺ a − Λ⁺ b`. -/
theorem rieszPosPart_sub {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {a b : S →ᵇ ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rieszPosPart Λ (a - b) = rieszPosSup Λ a - rieszPosSup Λ b := by
  have hp : (0 : S →ᵇ ℝ) ≤ (a - b) ⊔ 0 := le_sup_right
  have hn : (0 : S →ᵇ ℝ) ≤ (-(a - b)) ⊔ 0 := le_sup_right
  have e : (a - b) ⊔ 0 + b = a + (-(a - b)) ⊔ 0 := by
    ext x
    simp only [coe_add, coe_sub, coe_sup, coe_neg, coe_zero, Pi.add_apply, Pi.sub_apply,
      Pi.sup_apply, Pi.neg_apply, Pi.zero_apply]
    rw [max_def, max_def]
    split_ifs <;> linarith
  have h := congrArg (rieszPosSup Λ) e
  rw [rieszPosSup_add Λ hp hb, rieszPosSup_add Λ ha hn] at h
  unfold rieszPosPart
  linarith

/-- The extended `Λ⁺` is additive. -/
theorem rieszPosPart_add {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f g : S →ᵇ ℝ) : rieszPosPart Λ (f + g) = rieszPosPart Λ f + rieszPosPart Λ g := by
  have hf1 : (0 : S →ᵇ ℝ) ≤ f ⊔ 0 := le_sup_right
  have hf2 : (0 : S →ᵇ ℝ) ≤ (-f) ⊔ 0 := le_sup_right
  have hg1 : (0 : S →ᵇ ℝ) ≤ g ⊔ 0 := le_sup_right
  have hg2 : (0 : S →ᵇ ℝ) ≤ (-g) ⊔ 0 := le_sup_right
  have e : f + g = (f ⊔ 0 + g ⊔ 0) - ((-f) ⊔ 0 + (-g) ⊔ 0) := by
    nth_rewrite 1 [bcf_eq_posPart_sub_negPart f]
    nth_rewrite 1 [bcf_eq_posPart_sub_negPart g]
    abel
  rw [e, rieszPosPart_sub Λ (add_nonneg hf1 hg1) (add_nonneg hf2 hg2), rieszPosSup_add Λ hf1 hg1,
    rieszPosSup_add Λ hf2 hg2]
  unfold rieszPosPart
  ring

/-- The extended `Λ⁺` is homogeneous: `Λ⁺ (c f) = c Λ⁺ f` for every real `c`. -/
theorem rieszPosPart_smul {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (c : ℝ) (f : S →ᵇ ℝ) : rieszPosPart Λ (c • f) = c * rieszPosPart Λ f := by
  have hf1 : (0 : S →ᵇ ℝ) ≤ f ⊔ 0 := le_sup_right
  have hf2 : (0 : S →ᵇ ℝ) ≤ (-f) ⊔ 0 := le_sup_right
  have hx : ∀ x, f x = (f ⊔ 0) x - ((-f) ⊔ 0) x := fun x =>
    congrArg (fun g : S →ᵇ ℝ => g x) (bcf_eq_posPart_sub_negPart f)
  rcases le_or_gt 0 c with hc | hc
  · have e : c • f = c • (f ⊔ 0) - c • ((-f) ⊔ 0) := by
      ext x
      change c * f x = c * (f ⊔ 0) x - c * ((-f) ⊔ 0) x
      rw [hx x]
      ring
    rw [e, rieszPosPart_sub Λ (bcf_smul_nonneg hc hf1) (bcf_smul_nonneg hc hf2),
      rieszPosSup_smul Λ hc hf1, rieszPosSup_smul Λ hc hf2]
    unfold rieszPosPart
    ring
  · have hc' : 0 ≤ -c := by linarith
    have e : c • f = (-c) • ((-f) ⊔ 0) - (-c) • (f ⊔ 0) := by
      ext x
      change c * f x = (-c) * ((-f) ⊔ 0) x - (-c) * (f ⊔ 0) x
      rw [hx x]
      ring
    rw [e, rieszPosPart_sub Λ (bcf_smul_nonneg hc' hf2) (bcf_smul_nonneg hc' hf1),
      rieszPosSup_smul Λ hc' hf1, rieszPosSup_smul Λ hc' hf2]
    unfold rieszPosPart
    ring

/-- On nonnegative functions the extension agrees with the supremum. -/
theorem rieszPosPart_of_nonneg {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) : rieszPosPart Λ f = rieszPosSup Λ f := by
  unfold rieszPosPart
  rw [sup_eq_left.2 hf, sup_eq_right.2 (neg_nonpos.2 hf), rieszPosSup_zero, sub_zero]

/-- The positive part `Λ⁺` of `Λ`, as a linear functional on `C(S)`. -/
noncomputable def rieszPosPartLM {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    (S →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun := rieszPosPart Λ
  map_add' := rieszPosPart_add Λ
  map_smul' c f := by rw [rieszPosPart_smul, RingHom.id_apply, smul_eq_mul]

/-- `Λ⁺` is a positive functional. -/
theorem rieszPosPartLM_nonneg {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) : 0 ≤ rieszPosPartLM Λ f := by
  change 0 ≤ rieszPosPart Λ f
  rw [rieszPosPart_of_nonneg Λ hf]
  simpa using le_rieszPosSup Λ (le_refl (0 : S →ᵇ ℝ)) hf

/-- `Λ ≤ Λ⁺` on nonnegative functions, so that `Λ⁻ = Λ⁺ − Λ` is positive. -/
theorem le_rieszPosPartLM {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) : Λ f ≤ rieszPosPartLM Λ f := by
  change Λ f ≤ rieszPosPart Λ f
  rw [rieszPosPart_of_nonneg Λ hf]
  exact le_rieszPosSup Λ hf le_rfl

/-- **Jordan decomposition of a continuous linear functional on `C(S)`**: `Λ = Λ⁺ − Λ⁻` with
`Λ⁺` and `Λ⁻` positive linear functionals. -/
theorem functional_jordanDecomposition {S : Type*} [TopologicalSpace S]
    (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃ P₁ P₂ : (S →ᵇ ℝ) →ₗ[ℝ] ℝ, (∀ f, 0 ≤ f → 0 ≤ P₁ f) ∧ (∀ f, 0 ≤ f → 0 ≤ P₂ f) ∧
      ∀ f, Λ f = P₁ f - P₂ f := by
  refine ⟨rieszPosPartLM Λ, rieszPosPartLM Λ - (Λ : (S →ᵇ ℝ) →ₗ[ℝ] ℝ),
    fun f hf => rieszPosPartLM_nonneg Λ hf, fun f hf => ?_, fun f => ?_⟩
  · rw [LinearMap.sub_apply, ContinuousLinearMap.coe_coe, sub_nonneg]
    exact le_rieszPosPartLM Λ hf
  · rw [LinearMap.sub_apply, ContinuousLinearMap.coe_coe]
    ring

/-- A positive linear functional on `C(S)`, `S` a compact metric space, is integration against a
finite Borel measure. This transfers Mathlib's Riesz–Markov–Kakutani theorem
(`RealRMK.integral_rieszMeasure`, stated on `C_c(S, ℝ)`) to bounded continuous functions; the
measure is finite because `S` is compact. -/
theorem exists_measure_of_positive {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (P : (S →ᵇ ℝ) →ₗ[ℝ] ℝ) (hP : ∀ f, 0 ≤ f → 0 ≤ P f) :
    ∃ μ : Measure S, IsFiniteMeasure μ ∧ ∀ f : S →ᵇ ℝ, P f = ∫ s, f s ∂μ := by
  let L : C_c(S, ℝ) →ₗ[ℝ] (S →ᵇ ℝ) :=
    { toFun := fun f => mkOfCompact (f : C(S, ℝ))
      map_add' := fun f g => by ext x; rfl
      map_smul' := fun c f => by ext x; rfl }
  let Q : C_c(S, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (P.comp L) fun f hf => hP _ fun s => hf s
  refine ⟨RealRMK.rieszMeasure Q, inferInstance, fun f => ?_⟩
  let f' : C_c(S, ℝ) := ⟨f.toContinuousMap, HasCompactSupport.of_compactSpace _⟩
  have h1 := RealRMK.integral_rieszMeasure Q f'
  have h2 : Q f' = P f := by
    change P (L f') = P f
    congr 1
  rw [← h2, ← h1]
  rfl

/-- The integral of `f` against a signed measure `ν`: `∫ f dν⁺ − ∫ f dν⁻`, where `ν = ν⁺ − ν⁻`
is the Jordan decomposition of `ν`. -/
noncomputable def sIntegral {S : Type*} [MeasurableSpace S] (ν : SignedMeasure S)
    (f : S → ℝ) : ℝ :=
  ∫ s, f s ∂ν.toJordanDecomposition.posPart - ∫ s, f s ∂ν.toJordanDecomposition.negPart

/-- If two differences of finite measures integrate every bounded continuous function equally,
`∫ f dμ₁ − ∫ f dμ₂ = ∫ f dμ₃ − ∫ f dμ₄`, then `μ₁ + μ₄ = μ₃ + μ₂`: finite Borel measures on a
metric space are determined by the integrals of bounded continuous functions. -/
theorem add_eq_add_of_integral_sub_eq {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] {μ₁ μ₂ μ₃ μ₄ : Measure S} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h : ∀ f : S →ᵇ ℝ, ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ = ∫ s, f s ∂μ₃ - ∫ s, f s ∂μ₄) :
    μ₁ + μ₄ = μ₃ + μ₂ := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_add_measure (f.integrable μ₁) (f.integrable μ₄),
    integral_add_measure (f.integrable μ₃) (f.integrable μ₂)]
  linarith [h f]

/-- If `μ₁ − μ₂ = μ₃ − μ₄` as signed measures, then `∫ f dμ₁ − ∫ f dμ₂ = ∫ f dμ₃ − ∫ f dμ₄` for
every bounded continuous `f`. -/
theorem integral_sub_eq_of_toSignedMeasure_eq {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] {μ₁ μ₂ μ₃ μ₄ : Measure S} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h : μ₁.toSignedMeasure - μ₂.toSignedMeasure = μ₃.toSignedMeasure - μ₄.toSignedMeasure)
    (f : S →ᵇ ℝ) : ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ = ∫ s, f s ∂μ₃ - ∫ s, f s ∂μ₄ := by
  have h' : μ₁ + μ₄ = μ₃ + μ₂ := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add, ← sub_eq_sub_iff_add_eq_add]
    exact h
  have h2 := congrArg (fun μ : Measure S => ∫ s, f s ∂μ) h'
  rw [integral_add_measure (f.integrable μ₁) (f.integrable μ₄),
    integral_add_measure (f.integrable μ₃) (f.integrable μ₂)] at h2
  linarith

/-- The integral against the signed measure `μ₁ − μ₂` is `∫ f dμ₁ − ∫ f dμ₂`, whatever the
Jordan decomposition of `μ₁ − μ₂` is. -/
theorem sIntegral_toSignedMeasure_sub {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (f : S →ᵇ ℝ) :
    sIntegral (μ₁.toSignedMeasure - μ₂.toSignedMeasure) f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ :=
  integral_sub_eq_of_toSignedMeasure_eq
    (SignedMeasure.toSignedMeasure_toJordanDecomposition _) f

/-- **Theorem 14.14, existence** (p. 435): every continuous linear functional `Λ` on `C(S)` is
`Λ f = ∫ f dμ₁ − ∫ f dμ₂` for two finite Borel measures `μ₁, μ₂`. -/
theorem theorem_14_14_exists {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃ μ₁ μ₂ : Measure S, IsFiniteMeasure μ₁ ∧ IsFiniteMeasure μ₂ ∧
      ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hΛ⟩ := functional_jordanDecomposition Λ
  obtain ⟨μ₁, hμ₁, h₁⟩ := exists_measure_of_positive P₁ hP₁
  obtain ⟨μ₂, hμ₂, h₂⟩ := exists_measure_of_positive P₂ hP₂
  exact ⟨μ₁, μ₂, hμ₁, hμ₂, fun f => by rw [hΛ f, h₁ f, h₂ f]⟩

/-- **Theorem 14.14, uniqueness** (p. 435): a signed measure is determined by its integrals of
bounded continuous functions. (Compactness is not needed here.) -/
theorem theorem_14_14_unique {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ν ν' : SignedMeasure S} (h : ∀ f : S →ᵇ ℝ, sIntegral ν f = sIntegral ν' f) : ν = ν' := by
  have hm := add_eq_add_of_integral_sub_eq h
  calc ν = ν.toJordanDecomposition.toSignedMeasure :=
        (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm
    _ = ν'.toJordanDecomposition.toSignedMeasure := by
        unfold JordanDecomposition.toSignedMeasure
        rw [sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add,
          ← Measure.toSignedMeasure_add]
        exact Measure.toSignedMeasure_congr hm
    _ = ν' := SignedMeasure.toSignedMeasure_toJordanDecomposition ν'

/-- **Theorem 14.14, uniqueness for the pair of measures**: two representations
`Λ f = ∫ f dμ₁ − ∫ f dμ₂ = ∫ f dμ₃ − ∫ f dμ₄` give the same signed measure `μ₁ − μ₂ = μ₃ − μ₄`. -/
theorem theorem_14_14_unique_measures {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) {μ₁ μ₂ μ₃ μ₄ : Measure S} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h₁₂ : ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂)
    (h₃₄ : ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₃ - ∫ s, f s ∂μ₄) :
    μ₁.toSignedMeasure - μ₂.toSignedMeasure = μ₃.toSignedMeasure - μ₄.toSignedMeasure := by
  have hm := add_eq_add_of_integral_sub_eq fun f => (h₁₂ f).symm.trans (h₃₄ f)
  rw [sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
  exact Measure.toSignedMeasure_congr hm

/-- **Theorem 14.14** (Riesz representation theorem, p. 435): for every continuous linear
functional `Λ` on `C(S)`, `S` a compact metric space, there is a unique signed measure `ν` with
`Λ f = ∫ f dν` for all `f ∈ C(S)`. -/
theorem theorem_14_14 {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃! ν : SignedMeasure S, ∀ f : S →ᵇ ℝ, Λ f = sIntegral ν f := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hΛ⟩ := theorem_14_14_exists Λ
  refine ⟨μ₁.toSignedMeasure - μ₂.toSignedMeasure,
    fun f => by rw [sIntegral_toSignedMeasure_sub, hΛ f], fun ν hν => ?_⟩
  refine theorem_14_14_unique fun f => ?_
  rw [← hν f, sIntegral_toSignedMeasure_sub, hΛ f]

/-- A finite measure on a nonempty space is `α` times a probability measure, `α ≥ 0`. -/
theorem exists_smul_probabilityMeasure {S : Type*} [MeasurableSpace S] [Nonempty S]
    (μ : Measure S) [IsFiniteMeasure μ] :
    ∃ α : ℝ, ∃ p : Measure S, 0 ≤ α ∧ IsProbabilityMeasure p ∧
      ∀ f : S → ℝ, ∫ s, f s ∂μ = α * ∫ s, f s ∂p := by
  by_cases hμ : μ = 0
  · exact ⟨0, Measure.dirac (Classical.arbitrary S), le_rfl, inferInstance,
      fun f => by simp [hμ]⟩
  · have : NeZero μ := ⟨hμ⟩
    refine ⟨μ.real univ, (μ univ)⁻¹ • μ, measureReal_nonneg, inferInstance, fun f => ?_⟩
    rw [integral_smul_measure, smul_eq_mul, ← mul_assoc, measureReal_def,
      ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel (NeZero.ne _) (measure_ne_top _ _),
      ENNReal.toReal_one, one_mul]

/-- **Theorem 14.14, the form used in the book** (for Lemma 14.9): every continuous linear
functional on `C(S)` is `Λ f = α₁ ∫ f dλ₁ − α₂ ∫ f dλ₂` with `λ₁, λ₂` probability measures and
`α₁, α₂ ≥ 0`. (`S` must be nonempty for probability measures to exist.) -/
theorem theorem_14_14_prob {S : Type*} [MetricSpace S] [CompactSpace S] [Nonempty S]
    [MeasurableSpace S] [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃ α₁ α₂ : ℝ, ∃ p₁ p₂ : Measure S, 0 ≤ α₁ ∧ 0 ≤ α₂ ∧ IsProbabilityMeasure p₁ ∧
      IsProbabilityMeasure p₂ ∧
      ∀ f : S →ᵇ ℝ, Λ f = α₁ * ∫ s, f s ∂p₁ - α₂ * ∫ s, f s ∂p₂ := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hΛ⟩ := theorem_14_14_exists Λ
  obtain ⟨α₁, p₁, hα₁, hp₁, h₁⟩ := exists_smul_probabilityMeasure μ₁
  obtain ⟨α₂, p₂, hα₂, hp₂, h₂⟩ := exists_smul_probabilityMeasure μ₂
  exact ⟨α₁, α₂, p₁, p₂, hα₁, hα₂, hp₁, hp₂, fun f => by rw [hΛ f, h₁, h₂]⟩

end StokeyLucasPrescott.LawsOfLargeNumbers
