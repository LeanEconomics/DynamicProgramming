/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.MaximalIrreducibility

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

namespace MeynTweedie.Epilogue

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

end MeynTweedie.Epilogue
