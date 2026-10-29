/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.StateDependentDrift

/-!
# Random walk on the orthant `ℝ²₊` (MT §19.1.2)

Meyn and Tweedie, §19.1.2, pp. 487–489. The chain (19.20) is
`Φₙ = ([Φₙ₋₁(1) + Zₙ(1)]⁺, [Φₙ₋₁(2) + Zₙ(2)]⁺)` with i.i.d. increments `Zₙ ∼ Γ` on `ℝ²`
(`orthantKernel Γ`, a random recursion on `ℝ × ℝ`; from any state it moves into `ℝ²₊`).

**Results.**
* `orthant_pow_zero_ge`: if `Γ{Z(1) < −h, Z(2) < −h} = q > 0`, then
  `P^{k+1}((x, y), {(0, 0)}) ≥ q^{k+1}` whenever `x⁺, y⁺ ≤ (k + 1)h` (the book's
  `Pᵐ((x, y), (0, 0)) > h^{2m}` on squares); hence `orthant_isPhiIrreducible` (the chain is
  `δ_{(0,0)}`-irreducible) and `orthant_isSmall` (squares are small).
* `orthant_drift_real` (Kingman's quadratic test function, the alternative noted in the
  Commentary, p. 508): `V(x, y) = 1 + (x⁺)² + (y⁺)²` satisfies (V2) off a square.
* **Theorem 19.1.4** (`theorem_19_1_4`, p. 488), corrected: with negative mean increments, finite
  second moments and `Γ{Z(1) < −h, Z(2) < −h} > 0`, the walk is positive Harris recurrent, and
  `E_{(x,y)}[τ_C] ≤ 1 + (x⁺)² + (y⁺)² + b` for a square `C`.
* `exists_joint_neg_of_prod`: for independent coordinates (`Γ = Γ₁ ⊗ Γ₂`) with negative means,
  `Γ{Z(1) < −h, Z(2) < −h} > 0` for some `h > 0`, as the book assumes.

**Corrections.**
* (19.25) as stated, `E_{(x,y)}[τ_{A(m)}] ≤ c(x + y)`, fails at the origin for every set and every
  `c`, since `τ ≥ 1` (`theorem_19_1_4_counterexample`). The proof concerns the hitting time of a
  square `{x ≤ m, y ≤ m}` (the complement of the drift regions `A(M) ∪ A₁ ∪ A₂`), not of
  `A(m) = {x ≥ m, y ≥ m}`, and the bound has to be of the form `c(1 + x + y)`.
* The `δ_{(0,0)}`-irreducibility on p. 487 (and the invariance of `π₁ × π₂` on p. 488) use
  independence of the two coordinates of `Zₖ`, which the book does not assume. With
  `Z = (−1 + ξ, −1 − ξ)`, `ξ = ±3`, both means are `−1`, the second moments are finite, and the
  origin is never reached from the origin (`orthant_not_irreducible_counterexample`). Theorem 19.1.4
  is proved here under the joint condition `Γ{Z(1) < −h, Z(2) < −h} > 0`, which holds for
  independent coordinates.

* `theorem_19_1_4_linear` ((19.25), corrected): `E_{(x,y)}[τ_C] ≤ c(1 + x⁺ + y⁺)` for a square
  `C`, with negative means and finite second moments only. The test function
  `V = √(1 + (x⁺)² + (y⁺)²)` has linear growth, and Jensen's inequality
  (`sq_integral_le_integral_sq`) with the quadratic drift gives `PV ≤ V − ε/2` off `C`. This
  replaces the book's state-dependent construction through (19.22)–(19.24), which needs the
  `f`-norm ergodic theorem for the marginal walks.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

/-- One step of the walk on the orthant (19.20): `(x, y), z ↦ ([x + z₁]⁺, [y + z₂]⁺)`. -/
def orthantStep (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (max (p.1.1 + p.2.1) 0, max (p.1.2 + p.2.2) 0)

/-- The step is measurable. -/
theorem measurable_orthantStep : Measurable orthantStep :=
  ((measurable_fst.fst.add measurable_snd.fst).max measurable_const).prodMk
    ((measurable_fst.snd.add measurable_snd.snd).max measurable_const)

/-- **The random walk on `ℝ²₊`** (19.20), MT p. 487, with increment law `Γ`. -/
noncomputable def orthantKernel (Γ : Measure (ℝ × ℝ)) : Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  recursionKernel Γ orthantStep

/-- The walk is a Markov kernel. -/
theorem isMarkovKernel_orthantKernel (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (orthantKernel Γ) :=
  isMarkovKernel_recursionKernel Γ measurable_orthantStep

/-- `P(s, A) = Γ{z : step(s, z) ∈ A}`. -/
theorem orthantKernel_apply' (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] (s : ℝ × ℝ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    orthantKernel Γ s A = Γ {z | orthantStep (s, z) ∈ A} :=
  recursionKernel_apply' Γ measurable_orthantStep s hA

/-! ### Reaching the origin -/

/-- **Reaching the origin from squares**: if `Γ{Z(1) < −h, Z(2) < −h} ≥ q`, then
`P^{k+1}((x, y), {(0, 0)}) ≥ q^{k+1}` whenever `x⁺, y⁺ ≤ (k + 1)h`. -/
theorem orthant_pow_zero_ge (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {h : ℝ} (hh : 0 < h)
    {q : ℝ≥0∞} (hq : q ≤ Γ {z | z.1 < -h ∧ z.2 < -h}) (k : ℕ) (s : ℝ × ℝ)
    (h1 : max s.1 0 ≤ (k + 1) * h) (h2 : max s.2 0 ≤ (k + 1) * h) :
    q ^ (k + 1) ≤ (orthantKernel Γ ^ (k + 1)) s {((0 : ℝ), (0 : ℝ))} := by
  have := isMarkovKernel_orthantKernel Γ
  have hm0 : MeasurableSet ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := measurableSet_singleton _
  -- from a square of side `(k + 1)h`, one step reaches the square of side `kh` with prob. `≥ q`
  have hone : ∀ (k : ℕ) (s : ℝ × ℝ), max s.1 0 ≤ (k + 1) * h → max s.2 0 ≤ (k + 1) * h →
      q ≤ orthantKernel Γ s {t | max t.1 0 ≤ k * h ∧ max t.2 0 ≤ k * h} := by
    intro k s h1 h2
    have hm : MeasurableSet {t : ℝ × ℝ | max t.1 0 ≤ k * h ∧ max t.2 0 ≤ k * h} :=
      (measurableSet_le (measurable_fst.max measurable_const) measurable_const).inter
        (measurableSet_le (measurable_snd.max measurable_const) measurable_const)
    rw [orthantKernel_apply' Γ s hm]
    refine hq.trans (measure_mono fun z hz => ?_)
    obtain ⟨hz1, hz2⟩ := hz
    have hk : (0 : ℝ) ≤ k * h := by positivity
    simp only [mem_ofPred_eq, orthantStep]
    refine ⟨?_, ?_⟩
    · rw [max_eq_left (le_max_right _ _)]
      exact max_le (by linarith [le_max_left s.1 0]) hk
    · rw [max_eq_left (le_max_right _ _)]
      exact max_le (by linarith [le_max_left s.2 0]) hk
  induction k generalizing s with
  | zero =>
    rw [zero_add, pow_one, pow_one, orthantKernel_apply' Γ s hm0]
    refine hq.trans (measure_mono fun z hz => ?_)
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Nat.cast_zero, zero_add, one_mul] at h1 h2
    simp only [mem_ofPred_eq, orthantStep, mem_singleton_iff, Prod.mk.injEq]
    exact ⟨max_eq_right (by linarith [le_max_left s.1 0]),
      max_eq_right (by linarith [le_max_left s.2 0])⟩
  | succ k ih =>
    have hG : MeasurableSet {t : ℝ × ℝ | max t.1 0 ≤ (k + 1 : ℕ) * h ∧
        max t.2 0 ≤ (k + 1 : ℕ) * h} :=
      (measurableSet_le (measurable_fst.max measurable_const) measurable_const).inter
        (measurableSet_le (measurable_snd.max measurable_const) measurable_const)
    have hstep := hone (k + 1) s (by push_cast at h1 ⊢; linarith) (by push_cast at h2 ⊢; linarith)
    rw [pow_succ_apply _ (k + 1) s hm0]
    calc q ^ (k + 1 + 1) = q ^ (k + 1) * q := pow_succ _ _
      _ ≤ q ^ (k + 1) * orthantKernel Γ s {t | max t.1 0 ≤ (k + 1 : ℕ) * h ∧
            max t.2 0 ≤ (k + 1 : ℕ) * h} := mul_le_mul' le_rfl hstep
      _ = ∫⁻ _ in {t : ℝ × ℝ | max t.1 0 ≤ (k + 1 : ℕ) * h ∧ max t.2 0 ≤ (k + 1 : ℕ) * h},
            q ^ (k + 1) ∂orthantKernel Γ s := by rw [setLIntegral_const]
      _ ≤ ∫⁻ t in {t : ℝ × ℝ | max t.1 0 ≤ (k + 1 : ℕ) * h ∧ max t.2 0 ≤ (k + 1 : ℕ) * h},
            (orthantKernel Γ ^ (k + 1)) t {((0 : ℝ), (0 : ℝ))} ∂orthantKernel Γ s :=
          setLIntegral_mono' hG fun t ht => ih t (by exact_mod_cast ht.1) (by exact_mod_cast ht.2)
      _ ≤ _ := setLIntegral_le_lintegral _ _

/-- Every point lies in some square of side `(k + 1)h`. -/
theorem orthant_exists_side {h : ℝ} (hh : 0 < h) (s : ℝ × ℝ) :
    ∃ k : ℕ, max s.1 0 ≤ (k + 1) * h ∧ max s.2 0 ≤ (k + 1) * h := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max (max s.1 0) (max s.2 0) / h)
  have hk' : max (max s.1 0) (max s.2 0) ≤ k * h := (div_le_iff₀ hh).1 hk
  exact ⟨k, by nlinarith [le_max_left (max s.1 0) (max s.2 0)],
    by nlinarith [le_max_right (max s.1 0) (max s.2 0)]⟩

/-- **`δ_{(0,0)}`-irreducibility** (MT p. 487): if `Γ{Z(1) < −h, Z(2) < −h} > 0`, the origin is
reached from every point. -/
theorem orthant_isPhiIrreducible (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {h : ℝ}
    (hh : 0 < h) (hq : 0 < Γ {z | z.1 < -h ∧ z.2 < -h}) :
    haveI := isMarkovKernel_orthantKernel Γ
    IsPhiIrreducible (orthantKernel Γ) (Measure.dirac ((0 : ℝ), (0 : ℝ))) := by
  have := isMarkovKernel_orthantKernel Γ
  intro A hA hpos x
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ A := by
    by_contra h0
    rw [Measure.dirac_apply' _ hA, indicator_of_notMem h0] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨k, hk1, hk2⟩ := orthant_exists_side hh x
  refine (hitProb_pos_iff _ hA x).2 ⟨k, lt_of_lt_of_le (ENNReal.pow_pos hq (k + 1)) ?_⟩
  exact (orthant_pow_zero_ge Γ hh le_rfl k x hk1 hk2).trans
    (measure_mono (singleton_subset_iff.2 h0))

/-- **Squares are small** (MT p. 487): `{x⁺ ≤ R, y⁺ ≤ R}` is `ν_{k+1}`-small with
`ν = q^{k+1} δ_{(0,0)}`. -/
theorem orthant_isSmall (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {h : ℝ}
    (hh : 0 < h) (hq : 0 < Γ {z | z.1 < -h ∧ z.2 < -h}) (R : ℝ) :
    IsSmall (orthantKernel Γ) {s : ℝ × ℝ | max s.1 0 ≤ R ∧ max s.2 0 ≤ R} := by
  have := isMarkovKernel_orthantKernel Γ
  obtain ⟨k, hk⟩ := exists_nat_ge (max R 0 / h)
  have hk' : max R 0 ≤ k * h := (div_le_iff₀ hh).1 hk
  set q := Γ {z | z.1 < -h ∧ z.2 < -h}
  refine ⟨k + 1, q ^ (k + 1) • Measure.dirac ((0 : ℝ), (0 : ℝ)), ?_, Nat.succ_pos k, ?_, ?_⟩
  · exact (measurableSet_le (measurable_fst.max measurable_const) measurable_const).inter
      (measurableSet_le (measurable_snd.max measurable_const) measurable_const)
  · intro h0
    have := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ) h0
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.coe_zero,
      Pi.zero_apply] at this
    exact (ENNReal.pow_pos hq _).ne' this
  · intro s hs
    refine Measure.le_intro fun A hA _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    by_cases h0 : ((0 : ℝ), (0 : ℝ)) ∈ A
    · rw [indicator_of_mem h0, Pi.one_apply, mul_one]
      refine (orthant_pow_zero_ge Γ hh le_rfl k s ?_ ?_).trans
        (measure_mono (singleton_subset_iff.2 h0))
      · nlinarith [hs.1, le_max_left R 0]
      · nlinarith [hs.2, le_max_left R 0]
    · rw [indicator_of_notMem h0, mul_zero]; exact zero_le

/-! ### The quadratic test function -/

/-- Kingman's test function `V(x, y) = 1 + (x⁺)² + (y⁺)²`. -/
noncomputable def orthantV (s : ℝ × ℝ) : ℝ := 1 + max s.1 0 ^ 2 + max s.2 0 ^ 2

/-- `V` is measurable. -/
theorem measurable_orthantV : Measurable orthantV :=
  (measurable_const.add ((measurable_fst.max measurable_const).pow_const 2)).add
    ((measurable_snd.max measurable_const).pow_const 2)

/-- `V ≥ 1`. -/
theorem one_le_orthantV (s : ℝ × ℝ) : 1 ≤ orthantV s := by
  unfold orthantV; nlinarith [sq_nonneg (max s.1 0), sq_nonneg (max s.2 0)]

/-- `[x + z]⁺² ≤ (x⁺ + z)²`. -/
theorem max_add_sq_le (x z : ℝ) : max (x + z) 0 ^ 2 ≤ (max x 0 + z) ^ 2 := by
  have h1 : 0 ≤ max (x + z) 0 := le_max_right _ _
  have h2 : max (x + z) 0 ≤ max (max x 0 + z) 0 :=
    max_le_max (by linarith [le_max_left x 0]) le_rfl
  have h3 : max (max x 0 + z) 0 ^ 2 ≤ (max x 0 + z) ^ 2 := by
    rcases le_total 0 (max x 0 + z) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, zero_pow two_ne_zero]; exact sq_nonneg _
  nlinarith

/-- **The one-step drift of `V`**: with means `m₁, m₂` and second moments `σ₁, σ₂` of the
increments, `PV(x, y) ≤ V(x, y) + 2m₁x⁺ + 2m₂y⁺ + σ₁ + σ₂`. -/
theorem orthant_drift_real (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    (hW1 : Integrable (fun z : ℝ × ℝ => z.1) Γ) (hW2 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hS1 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) Γ) (hS2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ)
    (s : ℝ × ℝ) :
    Integrable orthantV (orthantKernel Γ s) ∧
      ∫ t, orthantV t ∂orthantKernel Γ s ≤ orthantV s + 2 * (∫ z, z.1 ∂Γ) * max s.1 0 +
        2 * (∫ z, z.2 ∂Γ) * max s.2 0 + ∫ z, z.1 ^ 2 ∂Γ + ∫ z, z.2 ^ 2 ∂Γ := by
  have hm : Measurable fun z : ℝ × ℝ => orthantStep (s, z) :=
    measurable_orthantStep.comp measurable_prodMk_left
  set g : ℝ × ℝ → ℝ := fun z => orthantV s + 2 * max s.1 0 * z.1 + 2 * max s.2 0 * z.2 +
    z.1 ^ 2 + z.2 ^ 2 with hg
  have hgi : Integrable g Γ :=
    ((((integrable_const _).add (hW1.const_mul _)).add (hW2.const_mul _)).add hS1).add hS2
  have hpt : ∀ z, orthantV (orthantStep (s, z)) ≤ g z := fun z => by
    simp only [orthantV, orthantStep, hg]
    rw [max_eq_left (le_max_right _ _), max_eq_left (le_max_right _ _)]
    nlinarith [max_add_sq_le s.1 z.1, max_add_sq_le s.2 z.2]
  have hfi : Integrable (fun z => orthantV (orthantStep (s, z))) Γ :=
    Integrable.mono' hgi (measurable_orthantV.comp hm).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [one_le_orthantV (orthantStep (s, z))])]
        exact hpt z)
  have hk : orthantKernel Γ s = Γ.map fun z => orthantStep (s, z) :=
    recursionKernel_apply Γ measurable_orthantStep s
  rw [hk]
  refine ⟨(integrable_map_measure measurable_orthantV.aestronglyMeasurable hm.aemeasurable).2 hfi,
    ?_⟩
  rw [integral_map hm.aemeasurable measurable_orthantV.aestronglyMeasurable]
  refine (integral_mono hfi hgi hpt).trans (le_of_eq ?_)
  have hA0 : Integrable (fun z : ℝ × ℝ => orthantV s + 2 * max s.1 0 * z.1) Γ :=
    (integrable_const _).add (hW1.const_mul _)
  have hA1 : Integrable (fun z : ℝ × ℝ => orthantV s + 2 * max s.1 0 * z.1 +
      2 * max s.2 0 * z.2) Γ := hA0.add (hW2.const_mul _)
  have hA2 : Integrable (fun z : ℝ × ℝ => orthantV s + 2 * max s.1 0 * z.1 +
      2 * max s.2 0 * z.2 + z.1 ^ 2) Γ := hA1.add hS1
  have e4 := integral_add hA2 hS2
  have e3 := integral_add hA1 hS1
  have e2 := integral_add hA0 (hW2.const_mul (2 * max s.2 0))
  have e1 := integral_add (integrable_const (orthantV s)) (hW1.const_mul (2 * max s.1 0))
  simp only [hg]
  rw [e4, e3, e2, e1, integral_const, integral_const_mul, integral_const_mul, probReal_univ,
    one_smul]
  ring

/-- **Theorem 19.1.4** (MT p. 488), corrected: if the increments have negative means and finite
second moments, and `Γ{Z(1) < −h, Z(2) < −h} > 0` for some `h > 0` (true for independent
coordinates, `exists_joint_neg_of_prod`), then the random walk on `ℝ²₊` is positive Harris
recurrent (with the maximal irreducibility measure generated by `δ_{(0,0)}`), and for some
square `C = {x⁺ ≤ R, y⁺ ≤ R}` and `b < ∞`, `E_{(x,y)}[τ_C] ≤ 1 + (x⁺)² + (y⁺)² + b`. The proof
uses (V2) with Kingman's quadratic `V` (Commentary, p. 508) instead of the book's
state-dependent drift. -/
theorem theorem_19_1_4 (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    (hW1 : Integrable (fun z : ℝ × ℝ => z.1) Γ) (hW2 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hS1 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) Γ) (hS2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ)
    (hm1 : ∫ z, z.1 ∂Γ < 0) (hm2 : ∫ z, z.2 ∂Γ < 0) {h : ℝ} (hh : 0 < h)
    (hq : 0 < Γ {z | z.1 < -h ∧ z.2 < -h}) :
    haveI := isMarkovKernel_orthantKernel Γ
    IsPositiveHarris (orthantKernel Γ)
        (maxIrrMeasure (orthantKernel Γ) (Measure.dirac ((0 : ℝ), (0 : ℝ)))) ∧
      ∃ R b : ℝ, ∀ s, meanReturnTime (orthantKernel Γ)
        {s : ℝ × ℝ | max s.1 0 ≤ R ∧ max s.2 0 ≤ R} s ≤ ENNReal.ofReal (orthantV s + b) := by
  have := isMarkovKernel_orthantKernel Γ
  set P := orthantKernel Γ
  have hψ := isMaximalIrreducibility_maxIrrMeasure P (orthant_isPhiIrreducible Γ hh hq)
    Measure.dirac_ne_zero
  set m1 := ∫ z, z.1 ∂Γ
  set m2 := ∫ z, z.2 ∂Γ
  set σ := ∫ z, z.1 ^ 2 ∂Γ + ∫ z, z.2 ^ 2 ∂Γ with hσ
  have hσ0 : 0 ≤ σ := add_nonneg (integral_nonneg fun z => sq_nonneg _)
    (integral_nonneg fun z => sq_nonneg _)
  set ε := min (-m1) (-m2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  set R := (σ + 1) / (2 * ε) with hR
  have hR0 : 0 ≤ R := by rw [hR]; exact div_nonneg (by linarith) (by linarith)
  set C := {s : ℝ × ℝ | max s.1 0 ≤ R ∧ max s.2 0 ≤ R} with hCdef
  have hCm : MeasurableSet C :=
    (measurableSet_le (measurable_fst.max measurable_const) measurable_const).inter
      (measurableSet_le (measurable_snd.max measurable_const) measurable_const)
  set W : ℝ × ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (orthantV s) with hWdef
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp measurable_orthantV
  set b := ENNReal.ofReal (σ + 1) with hb
  have hdrift : DriftV2 P W b C := by
    intro s
    obtain ⟨hint, hle⟩ := orthant_drift_real Γ hW1 hW2 hS1 hS2 s
    rw [hWdef, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => by
      change (0 : ℝ) ≤ orthantV t; linarith [one_le_orthantV t])]
    have hx1 := le_max_right s.1 0
    have hx2 := le_max_right s.2 0
    have hneg : 2 * m1 * max s.1 0 + 2 * m2 * max s.2 0 ≤ -(2 * ε) * (max s.1 0 + max s.2 0) := by
      have e1 : ε ≤ -m1 := min_le_left _ _
      have e2 : ε ≤ -m2 := min_le_right _ _
      nlinarith
    by_cases hs : s ∈ C
    · rw [indicator_of_mem hs, hb]
      have : ∫ t, orthantV t ∂P s ≤ orthantV s + (σ + 1) - 1 := by
        have : 0 ≤ ε * (max s.1 0 + max s.2 0) := by positivity
        linarith
      calc ENNReal.ofReal (∫ t, orthantV t ∂P s) + 1
          ≤ ENNReal.ofReal (orthantV s + (σ + 1) - 1) + ENNReal.ofReal 1 := by
            rw [ENNReal.ofReal_one]; exact add_le_add (ENNReal.ofReal_le_ofReal this) le_rfl
        _ = ENNReal.ofReal (orthantV s + (σ + 1)) := by
            rw [← ENNReal.ofReal_add (by linarith [one_le_orthantV s]) zero_le_one, sub_add_cancel]
        _ = ENNReal.ofReal (orthantV s) + ENNReal.ofReal (σ + 1) :=
            ENNReal.ofReal_add (by linarith [one_le_orthantV s]) (by linarith)
    · rw [indicator_of_notMem hs, add_zero]
      have hbig : R < max s.1 0 + max s.2 0 := by
        simp only [hCdef, mem_ofPred_eq, not_and_or, not_le] at hs
        rcases hs with h | h <;> linarith
      have hRε : 2 * ε * R = σ + 1 := by rw [hR]; field_simp
      have : ∫ t, orthantV t ∂P s ≤ orthantV s - 1 := by nlinarith
      calc ENNReal.ofReal (∫ t, orthantV t ∂P s) + 1
          ≤ ENNReal.ofReal (orthantV s - 1) + ENNReal.ofReal 1 := by
            rw [ENNReal.ofReal_one]; exact add_le_add (ENNReal.ofReal_le_ofReal this) le_rfl
        _ = ENNReal.ofReal (orthantV s) := by
            rw [← ENNReal.ofReal_add (by linarith [one_le_orthantV s]) zero_le_one, sub_add_cancel]
  have hCpet : IsPetite P C := by
    obtain ⟨k, ν, hsm⟩ := orthant_isSmall Γ hh hq R
    exact ⟨_, _, proposition_5_5_3 hsm⟩
  have hbt : b ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨theorem_11_3_4_positiveHarris hψ hWm hbt hCpet hdrift (fun _ => ENNReal.ofReal_ne_top)
    (M := ENNReal.ofReal (1 + R ^ 2 + R ^ 2)) ENNReal.ofReal_ne_top fun s hs => ?_,
    R, σ + 1, fun s => ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    simp only [orthantV]
    have h1 := hs.1
    have h2 := hs.2
    have := le_max_right s.1 0
    have := le_max_right s.2 0
    nlinarith
  · refine (theorem_11_3_4 hWm hCm hdrift s).trans ?_
    rw [ENNReal.ofReal_add (by linarith [one_le_orthantV s]) (by linarith)]
    exact add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) s)

/-! ### The linear bound (19.25) -/

/-- `(E X)² ≤ E[X²]` for a probability measure. -/
theorem sq_integral_le_integral_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {X : α → ℝ} (hX : Integrable X μ)
    (hX2 : Integrable (fun a => X a ^ 2) μ) : (∫ a, X a ∂μ) ^ 2 ≤ ∫ a, X a ^ 2 ∂μ := by
  set c := ∫ a, X a ∂μ
  have h0 : 0 ≤ ∫ a, (X a - c) ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have e : ∀ a, (X a - c) ^ 2 = X a ^ 2 - 2 * c * X a + c ^ 2 := fun a => by ring
  simp_rw [e] at h0
  rw [integral_add (f := fun a => X a ^ 2 - 2 * c * X a) (g := fun _ => c ^ 2)
    (hX2.sub (hX.const_mul _)) (integrable_const _),
    integral_sub (f := fun a => X a ^ 2) (g := fun a => 2 * c * X a) hX2 (hX.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at h0
  nlinarith

/-- **The linear bound (19.25)**, corrected (MT p. 488): with negative mean increments and finite
second moments (no independence of the coordinates is needed), for a square
`C = {x⁺ ≤ R, y⁺ ≤ R}` and some `c`, `E_{(x,y)}[τ_C] ≤ c(1 + x⁺ + y⁺)`. The test function is
`V = √(1 + (x⁺)² + (y⁺)²)`, of linear growth: by Jensen's inequality and the quadratic drift,
`PV ≤ √(PW) ≤ V − ε/2` off `C`, where `−ε` bounds the mean increments; this replaces the book's
state-dependent construction (19.22)–(19.24). -/
theorem theorem_19_1_4_linear (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    (hW1 : Integrable (fun z : ℝ × ℝ => z.1) Γ) (hW2 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hS1 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) Γ) (hS2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ)
    (hm1 : ∫ z, z.1 ∂Γ < 0) (hm2 : ∫ z, z.2 ∂Γ < 0) :
    haveI := isMarkovKernel_orthantKernel Γ
    ∃ R c : ℝ, 0 ≤ c ∧ ∀ s, meanReturnTime (orthantKernel Γ)
      {s : ℝ × ℝ | max s.1 0 ≤ R ∧ max s.2 0 ≤ R} s ≤
        ENNReal.ofReal (c * (1 + max s.1 0 + max s.2 0)) := by
  have := isMarkovKernel_orthantKernel Γ
  set P := orthantKernel Γ
  set m1 := ∫ z, z.1 ∂Γ
  set m2 := ∫ z, z.2 ∂Γ
  set σ := ∫ z, z.1 ^ 2 ∂Γ + ∫ z, z.2 ^ 2 ∂Γ with hσ
  have hσ0 : 0 ≤ σ := add_nonneg (integral_nonneg fun z => sq_nonneg _)
    (integral_nonneg fun z => sq_nonneg _)
  set ε := min (-m1) (-m2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have e1 : ε ≤ -m1 := min_le_left _ _
  have e2 : ε ≤ -m2 := min_le_right _ _
  set K := max (2 + σ / ε) ε with hK
  set C := {s : ℝ × ℝ | max s.1 0 ≤ K ∧ max s.2 0 ≤ K} with hCdef
  have hCm : MeasurableSet C :=
    (measurableSet_le (measurable_fst.max measurable_const) measurable_const).inter
      (measurableSet_le (measurable_snd.max measurable_const) measurable_const)
  set V : ℝ × ℝ → ℝ := fun s => Real.sqrt (orthantV s) with hVdef
  have hVm : Measurable V := Real.continuous_sqrt.measurable.comp measurable_orthantV
  have hW1' : ∀ s, 1 ≤ orthantV s := one_le_orthantV
  have hV1 : ∀ s, 1 ≤ V s := fun s => by
    rw [hVdef, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt (hW1' s)
  have hVsq : ∀ s, V s ^ 2 = orthantV s := fun s => Real.sq_sqrt (by linarith [hW1' s])
  have hVW : ∀ s, V s ≤ orthantV s := fun s => by
    have h := hVsq s
    nlinarith [hV1 s]
  have hVlin : ∀ s, V s ≤ 1 + max s.1 0 + max s.2 0 := fun s => by
    rw [hVdef, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    simp only [orthantV]
    nlinarith [le_max_right s.1 0, le_max_right s.2 0]
  have hVcoord : ∀ s, max s.1 0 ≤ V s ∧ max s.2 0 ≤ V s := fun s => by
    refine ⟨Real.le_sqrt_of_sq_le ?_, Real.le_sqrt_of_sq_le ?_⟩ <;>
      simp only [orthantV] <;> nlinarith [sq_nonneg (max s.1 0), sq_nonneg (max s.2 0)]
  -- Jensen: `PV ≤ √(PW)`
  have hPV : ∀ s, Integrable V (P s) ∧ ∫ t, V t ∂P s ≤ Real.sqrt (∫ t, orthantV t ∂P s) := by
    intro s
    obtain ⟨hint, -⟩ := orthant_drift_real Γ hW1 hW2 hS1 hS2 s
    have hVi : Integrable V (P s) := Integrable.mono' hint hVm.aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hV1 t])]; exact hVW t)
    refine ⟨hVi, Real.le_sqrt_of_sq_le ?_⟩
    have h := sq_integral_le_integral_sq (P s) hVi (by simp_rw [hVsq]; exact hint)
    simp_rw [hVsq] at h
    exact h
  -- the drift of `V`
  have hoff : ∀ s ∉ C, ∫ t, V t ∂P s ≤ V s - ε / 2 := by
    intro s hs
    obtain ⟨-, hle⟩ := orthant_drift_real Γ hW1 hW2 hS1 hS2 s
    obtain ⟨-, hJ⟩ := hPV s
    have hx1 := le_max_right s.1 0
    have hx2 := le_max_right s.2 0
    have hneg : 2 * m1 * max s.1 0 + 2 * m2 * max s.2 0 ≤
        -(2 * ε) * (max s.1 0 + max s.2 0) := by nlinarith
    have hvK : K < V s := by
      simp only [hCdef, mem_ofPred_eq, not_and_or, not_le] at hs
      rcases hs with h | h
      · exact h.trans_le (hVcoord s).1
      · exact h.trans_le (hVcoord s).2
    have hvK1 : 2 + σ / ε ≤ V s := (le_max_left _ _).trans hvK.le
    have hvK2 : ε ≤ V s := (le_max_right _ _).trans hvK.le
    have hεv : 2 * ε + σ ≤ ε * V s := by
      have h1 := mul_le_mul_of_nonneg_left hvK1 hε0.le
      have h3 : ε * (2 + σ / ε) = 2 * ε + σ := by field_simp
      linarith
    refine hJ.trans ((Real.sqrt_le_iff).2 ⟨by linarith, ?_⟩)
    have hsq := hVsq s
    have hl := hVlin s
    nlinarith
  have hon : ∀ s, ∫ t, V t ∂P s ≤ V s + Real.sqrt σ := by
    intro s
    obtain ⟨-, hle⟩ := orthant_drift_real Γ hW1 hW2 hS1 hS2 s
    obtain ⟨-, hJ⟩ := hPV s
    have hx1 := le_max_right s.1 0
    have hx2 := le_max_right s.2 0
    have hneg : 2 * m1 * max s.1 0 + 2 * m2 * max s.2 0 ≤ 0 := by nlinarith
    refine hJ.trans ((Real.sqrt_le_iff).2 ⟨by linarith [hV1 s, Real.sqrt_nonneg σ], ?_⟩)
    have hsq := hVsq s
    have hs2 := Real.sq_sqrt hσ0
    nlinarith [hV1 s, Real.sqrt_nonneg σ]
  -- (V2) for `W' = (2/ε) V`
  set W' : ℝ × ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (2 / ε * V s) with hW'def
  have hW'm : Measurable W' := ENNReal.measurable_ofReal.comp (measurable_const.mul hVm)
  set b := ENNReal.ofReal (2 / ε * Real.sqrt σ + 1) with hb
  have hc2 : 0 < 2 / ε := by positivity
  have hdrift : DriftV2 P W' b C := by
    intro s
    obtain ⟨hVi, -⟩ := hPV s
    rw [hW'def, ← ofReal_integral_eq_lintegral_ofReal (hVi.const_mul _)
      (Eventually.of_forall fun t => by
        change (0 : ℝ) ≤ 2 / ε * V t; exact mul_nonneg hc2.le (by linarith [hV1 t])),
      integral_const_mul]
    by_cases hs : s ∈ C
    · rw [indicator_of_mem hs, hb, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (mul_nonneg hc2.le (integral_nonneg fun t => (by
          linarith [hV1 t] : (0 : ℝ) ≤ V t))) zero_le_one,
        ← ENNReal.ofReal_add (mul_nonneg hc2.le (by linarith [hV1 s])) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left (hon s) hc2.le
      nlinarith
    · rw [indicator_of_notMem hs, add_zero, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (mul_nonneg hc2.le (integral_nonneg fun t => (by
          linarith [hV1 t] : (0 : ℝ) ≤ V t))) zero_le_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left (hoff s hs) hc2.le
      have e : 2 / ε * (ε / 2) = 1 := by field_simp
      nlinarith
  set c := 2 / ε + (2 / ε * Real.sqrt σ + 1) with hc
  refine ⟨K, c, by positivity, fun s => ?_⟩
  refine (theorem_11_3_4 hW'm hCm hdrift s).trans ?_
  have hu : 1 ≤ 1 + max s.1 0 + max s.2 0 := by
    linarith [le_max_right s.1 0, le_max_right s.2 0]
  calc W' s + C.indicator (fun _ => b) s ≤ W' s + b :=
        add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) s)
    _ = ENNReal.ofReal (2 / ε * V s + (2 / ε * Real.sqrt σ + 1)) :=
        (ENNReal.ofReal_add (mul_nonneg hc2.le (by linarith [hV1 s])) (by positivity)).symm
    _ ≤ ENNReal.ofReal (c * (1 + max s.1 0 + max s.2 0)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := mul_le_mul_of_nonneg_left (hVlin s) hc2.le
        have h2 : (2 / ε * Real.sqrt σ + 1) ≤ (2 / ε * Real.sqrt σ + 1) *
            (1 + max s.1 0 + max s.2 0) := le_mul_of_one_le_right (by positivity) hu
        rw [hc]
        nlinarith

/-! ### Corrections -/

/-- **(19.25) fails as stated** (correction): for every increment law, every set `A` and every
`c`, `E_{(0,0)}[τ_A] ≥ 1 > c(0 + 0)`; the bound must be of the form `c(1 + x + y)`. -/
theorem theorem_19_1_4_counterexample (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    (A : Set (ℝ × ℝ)) (c : ℝ) :
    haveI := isMarkovKernel_orthantKernel Γ
    ¬ meanReturnTime (orthantKernel Γ) A ((0 : ℝ), (0 : ℝ)) ≤ ENNReal.ofReal (c * (0 + 0)) := by
  have := isMarkovKernel_orthantKernel Γ
  have := isMarkovKernel_pathKernel (orthantKernel Γ)
  intro h
  rw [add_zero, mul_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h
  have h1 : (1 : ℝ≥0∞) ≤ meanReturnTime (orthantKernel Γ) A ((0 : ℝ), (0 : ℝ)) := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂pathKernel (orthantKernel Γ) ((0 : ℝ), (0 : ℝ)) := by simp
      _ ≤ _ := lintegral_mono fun ω => by
          calc (1 : ℝ≥0∞) = ENat.toENNReal ((1 : ℕ) : ℕ∞) := by simp
            _ ≤ _ := ENat.toENNReal_le.2 (one_le_firstReturn A ω)
  rw [h] at h1
  exact absurd h1 (by simp)

/-- The increment law of the counterexample: `Z = (−1 + ξ, −1 − ξ)`, `ξ = ±3` with probability
`½` each. -/
noncomputable def orthantCounterLaw : Measure (ℝ × ℝ) :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac ((2 : ℝ), (-4 : ℝ)) + Measure.dirac ((-4 : ℝ), (2 : ℝ)))

/-- The law is a probability. -/
theorem isProbabilityMeasure_orthantCounterLaw : IsProbabilityMeasure orthantCounterLaw :=
  ⟨by
    rw [orthantCounterLaw, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ,
      smul_eq_mul, one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- **The irreducibility claim needs independent coordinates** (correction, MT p. 487): for
`Z = (−1 + ξ, −1 − ξ)` with `ξ = ±3`, both coordinates have mean `−1` and finite variance, but
from the origin the walk never returns to the origin (one coordinate is always `≥ 2`), so the
walk is not `δ_{(0,0)}`-irreducible. -/
theorem orthant_not_irreducible_counterexample :
    haveI := isProbabilityMeasure_orthantCounterLaw
    haveI := isMarkovKernel_orthantKernel orthantCounterLaw
    (∫ z, z.1 ∂orthantCounterLaw = -1 ∧ ∫ z, z.2 ∂orthantCounterLaw = -1) ∧
      hitProb (orthantKernel orthantCounterLaw) {((0 : ℝ), (0 : ℝ))} ((0 : ℝ), (0 : ℝ)) = 0 ∧
      ¬ IsPhiIrreducible (orthantKernel orthantCounterLaw) (Measure.dirac ((0 : ℝ), (0 : ℝ))) := by
  have := isProbabilityMeasure_orthantCounterLaw
  have := isMarkovKernel_orthantKernel orthantCounterLaw
  set P := orthantKernel orthantCounterLaw
  set Q := {s : ℝ × ℝ | 0 ≤ s.1 ∧ 0 ≤ s.2} with hQ
  set S := {s : ℝ × ℝ | 0 ≤ s.1 ∧ 0 ≤ s.2 ∧ (2 ≤ s.1 ∨ 2 ≤ s.2)} with hS
  have hQm : MeasurableSet Q :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_le measurable_const measurable_fst).union
          (measurableSet_le measurable_const measurable_snd)))
  have hlaw : ∀ {B : Set (ℝ × ℝ)}, MeasurableSet B → ((2 : ℝ), (-4 : ℝ)) ∉ B →
      ((-4 : ℝ), (2 : ℝ)) ∉ B → orthantCounterLaw B = 0 := fun {B} hB h1 h2 => by
    simp [orthantCounterLaw, Measure.dirac_apply' _ hB, h1, h2]
  have hstepm : ∀ s, Measurable fun z : ℝ × ℝ => orthantStep (s, z) := fun s =>
    measurable_orthantStep.comp measurable_prodMk_left
  have hPQ : ∀ s, P s Qᶜ = 0 := fun s => by
    rw [orthantKernel_apply' _ s hQm.compl]
    refine hlaw (hstepm s hQm.compl) ?_ ?_ <;>
      simp [hQ, orthantStep]
  have hPS : ∀ s ∈ Q, P s Sᶜ = 0 := fun s hs => by
    rw [orthantKernel_apply' _ s hSm.compl]
    obtain ⟨hs1, hs2⟩ := hs
    refine hlaw (hstepm s hSm.compl) ?_ ?_
    · simp only [mem_compl_iff, mem_ofPred_eq, hS, orthantStep, not_not]
      exact ⟨le_max_right _ _, le_max_right _ _, Or.inl (le_max_of_le_left (by linarith))⟩
    · simp only [mem_compl_iff, mem_ofPred_eq, hS, orthantStep, not_not]
      exact ⟨le_max_right _ _, le_max_right _ _, Or.inr (le_max_of_le_left (by linarith))⟩
  have hpowQ : ∀ n, (P ^ n) ((0 : ℝ), (0 : ℝ)) Qᶜ = 0 := fun n => by
    cases n with
    | zero =>
      rw [pow_zero_apply, Measure.dirac_apply' _ hQm.compl, indicator_of_notMem (by simp [hQ])]
    | succ n =>
      rw [pow_succ_apply' _ n _ hQm.compl]
      simp [hPQ]
  have hpowS : ∀ n, (P ^ (n + 1)) ((0 : ℝ), (0 : ℝ)) Sᶜ = 0 := fun n => by
    have := isMarkovKernel_pow P n
    rw [pow_succ_apply' _ n _ hSm.compl]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe P hSm.compl)).2 ?_
    have hae : ∀ᵐ t ∂(P ^ n) ((0 : ℝ), (0 : ℝ)), t ∈ Q := by
      rw [ae_iff]
      have : {a : ℝ × ℝ | ¬ a ∈ Q} = Qᶜ := rfl
      rw [this]; exact hpowQ n
    filter_upwards [hae] with t ht
    exact hPS t ht
  have hhit : hitProb P {((0 : ℝ), (0 : ℝ))} ((0 : ℝ), (0 : ℝ)) = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P (measurableSet_singleton _) _).1 (pos_iff_ne_zero.2 hne)
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ Sᶜ := by simp [hS]
    have := (measure_mono (singleton_subset_iff.2 h0) :
      (P ^ (n + 1)) ((0 : ℝ), (0 : ℝ)) {((0 : ℝ), (0 : ℝ))} ≤ _)
    rw [hpowS n] at this
    exact hn.ne' (nonpos_iff_eq_zero.1 this)
  refine ⟨⟨?_, ?_⟩, hhit, fun hirr => ?_⟩
  · rw [orthantCounterLaw, integral_smul_measure, integral_add_measure
      (integrable_dirac' measurable_fst.stronglyMeasurable enorm_lt_top)
      (integrable_dirac' measurable_fst.stronglyMeasurable enorm_lt_top),
      integral_dirac' _ _ measurable_fst.stronglyMeasurable,
      integral_dirac' _ _ measurable_fst.stronglyMeasurable]
    norm_num
  · rw [orthantCounterLaw, integral_smul_measure, integral_add_measure
      (integrable_dirac' measurable_snd.stronglyMeasurable enorm_lt_top)
      (integrable_dirac' measurable_snd.stronglyMeasurable enorm_lt_top),
      integral_dirac' _ _ measurable_snd.stronglyMeasurable,
      integral_dirac' _ _ measurable_snd.stronglyMeasurable]
    norm_num
  · have := hirr {((0 : ℝ), (0 : ℝ))} (measurableSet_singleton _) (by simp) ((0 : ℝ), (0 : ℝ))
    rw [hhit] at this
    exact lt_irrefl _ this

/-- **Independent coordinates** (MT p. 487): if `Γ = Γ₁ ⊗ Γ₂` and both coordinates have negative
mean, then `Γ{Z(1) < −h, Z(2) < −h} > 0` for some `h > 0`. -/
theorem exists_joint_neg_of_prod (Γ₁ Γ₂ : Measure ℝ) [IsProbabilityMeasure Γ₁]
    [IsProbabilityMeasure Γ₂] (h1 : ∫ w, w ∂Γ₁ < 0) (h2 : ∫ w, w ∂Γ₂ < 0) :
    ∃ h : ℝ, 0 < h ∧ 0 < (Γ₁.prod Γ₂) {z | z.1 < -h ∧ z.2 < -h} := by
  have key : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∫ w, w ∂μ < 0 →
      ∃ h : ℝ, 0 < h ∧ 0 < μ (Iio (-h)) := by
    intro μ _ hμ
    by_contra hc
    push Not at hc
    have hU : Iio (0 : ℝ) = ⋃ n : ℕ, Iio (-(1 / ((n : ℝ) + 1))) := by
      ext w
      simp only [mem_Iio, mem_iUnion]
      constructor
      · intro hw
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hw)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have h0 : μ (Iio 0) = 0 := by
      rw [hU]
      exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc _ (by positivity))
    have hnn : 0 ≤ᵐ[μ] fun w => w := by
      rw [Filter.EventuallyLE, ae_iff]
      have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Iio 0 := by ext w; simp
      rw [this]; exact h0
    exact absurd (integral_nonneg_of_ae hnn) (not_le.2 hμ)
  obtain ⟨a, ha, hμa⟩ := key Γ₁ h1
  obtain ⟨b, hb, hμb⟩ := key Γ₂ h2
  refine ⟨min a b, lt_min ha hb, ?_⟩
  have hsub : Iio (-a) ×ˢ Iio (-b) ⊆ {z : ℝ × ℝ | z.1 < -min a b ∧ z.2 < -min a b} := by
    rintro z ⟨hz1, hz2⟩
    simp only [mem_Iio] at hz1 hz2
    exact ⟨by linarith [min_le_left a b], by linarith [min_le_right a b]⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos hμa.ne' hμb.ne'

end MeynTweedie.GeneralizedDrift
