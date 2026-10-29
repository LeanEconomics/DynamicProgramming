/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.RegularityConverse
import Epilogue.Dichotomy
import Epilogue.UniformTransience

/-!
# Two hitting-time inequalities from §11.1 (MT pp. 258–259)

Copied for Chapter 13 from the Chapter 11 project
(`DriftRegularity/AtomHittingBounds.lean`), with the namespace changed to
`MeynTweedie.Epilogue` and the imports to this project's modules.

Meyn and Tweedie, §11.1, pp. 258–259: the two inequalities used, without proof, in the proofs
of Proposition 11.1.1 and Theorem 11.1.2.

* `toENNReal_firstReturn_le_shift`: pathwise `τ_B ≤ t + τ_B ∘ θᵗ`.
* `meanReturnTime_le_add_of_forall_le`: if `E_y[τ_B] ≤ M` for `y ∈ A`, then
  `E_x[τ_B] ≤ E_x[τ_A] + M` (strong Markov property at `τ_A`, `lintegral_shiftAt_firstReturn`).
* **(11.11)** (`eq_11_11`, p. 259): for an atom `α`, `E_x[τ_B] ≤ E_x[τ_α] + E_α[τ_B]`.
* `add_toENNReal_firstReturn_shift_le`: pathwise, on `{Φₙ ∉ A, τ_A ≥ n}`,
  `n + τ_A ∘ θⁿ ≤ τ_A`.
* `tabooProb_mul_le_meanReturnTime`: for `y ∉ A`, `E_x[τ_A] ≥ _APⁿ(x, y) [E_y[τ_A] + n]`
  (Markov property at time `n`).
* **The inequality in the proof of Proposition 11.1.1** (`proposition_11_1_1_ineq`, p. 258):
  `E_x[τ_x] ≥ ₓPⁿ(x, y) [E_y[τ_x] + n]` for `y ≠ x`.

**Corrections.** The book writes the inequality of Proposition 11.1.1 "for any fixed states
`x, y`"; it fails for `y = x` (`proposition_11_1_1_ineq_counterexample`: on a one-point space
`E_x[τ_x] = 1 < 2 = ₓP¹(x, x) [E_x[τ_x] + 1]`). The proof only uses `y ≠ x`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

omit [MeasurableSpace X] in
/-- Pathwise, `τ_B ≤ t + τ_B ∘ θᵗ`: after time `t` the chain still has to reach `B`. -/
theorem toENNReal_firstReturn_le_shift (B : Set X) (ω : ℕ → X) (t : ℕ) :
    ENat.toENNReal (firstReturn B ω) ≤ t + ENat.toENNReal (firstReturn B (shift t ω)) := by
  cases h : firstReturn B (shift t ω) with
  | top =>
    rw [show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top, add_top]
    exact le_top
  | coe s =>
    have hs1 : 1 ≤ s := by
      have := one_le_firstReturn B (shift t ω)
      rw [h] at this
      exact WithTop.coe_le_coe.1 this
    have hmem : ω (t + s) ∈ B := (mem_of_firstReturn_eq h : shift t ω s ∈ B)
    have hle := firstReturn_le_of_mem (A := B) (j := t + s) (by omega) hmem
    calc ENat.toENNReal (firstReturn B ω) ≤ ENat.toENNReal (WithTop.some (t + s)) :=
          ENat.toENNReal_mono hle
      _ = t + ENat.toENNReal (WithTop.some s) := by
          rw [toENNReal_some, toENNReal_some]; push_cast; rfl

/-- **The hitting-time bound behind (11.11)**: if `E_y[τ_B] ≤ M` for every `y ∈ A`, then
`E_x[τ_B] ≤ E_x[τ_A] + M` for every `x` (strong Markov property at `τ_A`). -/
theorem meanReturnTime_le_add_of_forall_le [IsMarkovKernel P] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {M : ℝ≥0∞}
    (hM : ∀ y ∈ A, meanReturnTime P B y ≤ M) (x : X) :
    meanReturnTime P B x ≤ meanReturnTime P A x + M := by
  have := isMarkovKernel_pathKernel P
  have hT := measurableSet_firstReturn_ne_top hA
  have hH := measurable_toENNReal_firstReturn hB
  have hpt : ∀ ω, ENat.toENNReal (firstReturn B ω) ≤ ENat.toENNReal (firstReturn A ω) +
      {ω | firstReturn A ω ≠ ⊤}.indicator
        (fun ω => ENat.toENNReal (firstReturn B (shiftAt (firstReturn A) ω))) ω := fun ω => by
    cases h : firstReturn A ω with
    | top =>
      rw [show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top, top_add]
      exact le_top
    | coe t =>
      rw [indicator_of_mem (by simp [h] : ω ∈ {ω | firstReturn A ω ≠ ⊤}), shiftAt_of_eq h,
        toENNReal_some]
      exact toENNReal_firstReturn_le_shift B ω t
  calc meanReturnTime P B x = ∫⁻ ω, ENat.toENNReal (firstReturn B ω) ∂pathKernel P x := rfl
    _ ≤ ∫⁻ ω, (ENat.toENNReal (firstReturn A ω) + {ω | firstReturn A ω ≠ ⊤}.indicator
          (fun ω => ENat.toENNReal (firstReturn B (shiftAt (firstReturn A) ω))) ω)
          ∂pathKernel P x := lintegral_mono hpt
    _ = meanReturnTime P A x + ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
          ENat.toENNReal (firstReturn B (shiftAt (firstReturn A) ω)) ∂pathKernel P x := by
        rw [lintegral_add_left (measurable_toENNReal_firstReturn hA), lintegral_indicator hT]
        rfl
    _ = meanReturnTime P A x + ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
          meanReturnTime P B (stoppedState (firstReturn A) ω) ∂pathKernel P x := by
        rw [lintegral_shiftAt_firstReturn P x hA hH]
        rfl
    _ ≤ meanReturnTime P A x + ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, M ∂pathKernel P x := by
        refine add_le_add le_rfl (setLIntegral_mono measurable_const fun ω hω => hM _ ?_)
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
        rw [stoppedState_of_eq ht.symm]
        exact mem_of_firstReturn_eq ht.symm
    _ ≤ meanReturnTime P A x + M := by
        rw [setLIntegral_const]
        exact add_le_add le_rfl (mul_le_of_le_one_right' prob_le_one)

/-- **(11.11)** (MT p. 259, proof of Theorem 11.1.2): for an atom `α`, any `a ∈ α` and any `x`,
`E_x[τ_B] ≤ E_x[τ_α] + E_α[τ_B]`, where `E_α[τ_B] = E_a[τ_B]` does not depend on `a ∈ α`. -/
theorem eq_11_11 [IsMarkovKernel P] {α B : Set X} (hα : IsAtom P α) (hB : MeasurableSet B)
    {a : X} (ha : a ∈ α) (x : X) :
    meanReturnTime P B x ≤ meanReturnTime P α x + meanReturnTime P B a :=
  meanReturnTime_le_add_of_forall_le hα.1 hB
    (fun _ hy => (hα.meanReturnTime_eq hB hy ha).le) x

omit [MeasurableSpace X] in
/-- Pathwise, on `{Φₙ ∉ A, τ_A ≥ n}`, `τ_A ≥ n + τ_A ∘ θⁿ`. -/
theorem add_toENNReal_firstReturn_shift_le {A : Set X} {ω : ℕ → X} {n : ℕ} (hn : ω n ∉ A)
    (hle : WithTop.some n ≤ firstReturn A ω) :
    n + ENat.toENNReal (firstReturn A (shift n ω)) ≤ ENat.toENNReal (firstReturn A ω) := by
  cases h : firstReturn A ω with
  | top =>
    rw [show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top]
    exact le_top
  | coe t =>
    rw [h] at hle
    have htn : n ≤ t := WithTop.coe_le_coe.1 hle
    have hne : t ≠ n := fun he => hn (he ▸ mem_of_firstReturn_eq h)
    obtain ⟨s, rfl⟩ : ∃ s, t = n + s := ⟨t - n, by omega⟩
    have hmem : shift n ω s ∈ A := (mem_of_firstReturn_eq h : ω (n + s) ∈ A)
    have hs := firstReturn_le_of_mem (A := A) (ω := shift n ω) (j := s) (by omega) hmem
    calc (n : ℝ≥0∞) + ENat.toENNReal (firstReturn A (shift n ω))
        ≤ n + ENat.toENNReal (WithTop.some s) := add_le_add le_rfl (ENat.toENNReal_mono hs)
      _ = ENat.toENNReal (WithTop.some (n + s)) := by
          rw [toENNReal_some, toENNReal_some]; push_cast; rfl

variable [MeasurableSingletonClass X] in
/-- **The inequality in the proof of Proposition 11.1.1** (MT p. 258), for a general set `A`:
if `y ∉ A`, then `E_x[τ_A] ≥ _AP^n(x, y) [E_y[τ_A] + n]` for every `n` and `x`. -/
theorem tabooProb_mul_le_meanReturnTime [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {y : X} (hy : y ∉ A) (n : ℕ) (x : X) :
    tabooProb P A n x {y} * (meanReturnTime P A y + n) ≤ meanReturnTime P A x := by
  have := isMarkovKernel_pathKernel P
  set G := {ω : ℕ → X | ω n ∈ ({y} : Set X)} ∩ {ω | WithTop.some n ≤ firstReturn A ω}
    with hGdef
  have hGn : MeasurableSet[natFilt n] G :=
    (measurableSet_coord_natFilt le_rfl (measurableSet_singleton y)).inter
      (measurableSet_natFilt_le_firstReturn hA n)
  have hG : MeasurableSet G := (natFilt (X := X)).le n _ hGn
  have hH := measurable_toENNReal_firstReturn (X := X) hA
  have hmk := markov_lintegral P (Measure.dirac x) hGn hH
  rw [pathMeasure_dirac] at hmk
  calc tabooProb P A n x {y} * (meanReturnTime P A y + n)
      = ∫⁻ _ in G, (n + meanReturnTime P A y) ∂pathKernel P x := by
        rw [setLIntegral_const, add_comm, mul_comm]; rfl
    _ = ∫⁻ ω in G, (n + ENat.toENNReal (firstReturn A (shift n ω))) ∂pathKernel P x := by
        rw [lintegral_add_left measurable_const, lintegral_add_left measurable_const, hmk]
        congr 1
        refine setLIntegral_congr_fun hG fun ω hω => ?_
        have : ω n = y := hω.1
        rw [this]
        rfl
    _ ≤ ∫⁻ ω in G, ENat.toENNReal (firstReturn A ω) ∂pathKernel P x :=
        setLIntegral_mono hH fun ω hω => add_toENNReal_firstReturn_shift_le
          (by have : ω n = y := hω.1; rw [this]; exact hy) hω.2
    _ ≤ meanReturnTime P A x := setLIntegral_le_lintegral _ _

/-- **The inequality in the proof of Proposition 11.1.1** (MT p. 258), as printed: for states
`y ≠ x`, `E_x[τ_x] ≥ ₓPⁿ(x, y) [E_y[τ_x] + n]`. -/
theorem proposition_11_1_1_ineq [MeasurableSingletonClass X] [IsMarkovKernel P] {x y : X}
    (hxy : y ≠ x) (n : ℕ) :
    tabooProb P {x} n x {y} * (meanReturnTime P {x} y + n) ≤ meanReturnTime P {x} x :=
  tabooProb_mul_le_meanReturnTime (measurableSet_singleton x) (by simpa using hxy) n x

/-- **The inequality of Proposition 11.1.1 fails for `y = x`.** For the chain on a single point,
`E_x[τ_x] = 1` while `ₓP¹(x, x) [E_x[τ_x] + 1] = 2`; the book applies it only with `y ≠ x`. -/
theorem proposition_11_1_1_ineq_counterexample :
    ¬ ∀ n : ℕ, tabooProb (Kernel.id : Kernel Unit Unit) {()} n () {()} *
      (meanReturnTime Kernel.id {()} () + n) ≤ meanReturnTime Kernel.id {()} () := by
  intro h
  have h1 := h 1
  have hfr : ∀ ω : ℕ → Unit, firstReturn {()} ω = WithTop.some 1 := fun ω =>
    (firstReturn_eq_iff _ ω 0).2 ⟨one_le_firstReturn _ ω, mem_singleton _⟩
  have := isMarkovKernel_pathKernel (Kernel.id : Kernel Unit Unit)
  have hm : meanReturnTime (Kernel.id : Kernel Unit Unit) {()} () = 1 := by
    simp only [meanReturnTime, hfr, toENNReal_some]
    simp
  rw [hm, tabooProb_one _ _ _ (measurableSet_singleton _), Kernel.id_apply,
    Measure.dirac_apply_of_mem (mem_singleton _)] at h1
  norm_num at h1

end MeynTweedie.Epilogue
