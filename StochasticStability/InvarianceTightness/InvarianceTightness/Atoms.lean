/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.Accessibility

/-!
# Atoms (MT Chapter 5 introduction and §5.1)

Meyn and Tweedie, pp. 96–98.

* `IsAtom P α` (p. 96): `α` is measurable and `P(x, ·)` is the same measure `ν` for every
  `x ∈ α`; `isAtom_singleton`: a single point is an atom.
* `IsAccessibleAtom P ψ α` (p. 96): an atom with `ψ(α) > 0` for a maximal irreducibility
  measure `ψ`; `IsMaximalIrreducibility.pos_iff_hitProb_pos`: for maximal `ψ`, `ψ(α) > 0` iff
  `L(x, α) > 0` for every `x`, so accessibility does not depend on the choice of `ψ`.
* `exists_pow_comp_pos`: from any nonzero initial law, a `φ`-irreducible chain reaches a set of
  positive `φ`-measure with positive probability: `ρPᵐ⁺¹(B) > 0` for some `m`.
* `hitProb_pos_of_exists_pow`: if every state reaches `α` (time `0` allowed), then
  `L(x, α) > 0` for every `x`.
* `pow_succ_ge_of_atom`: the bound `Pⁿ⁺¹(x, A) ≥ Pⁿ(x, α) ν(A)` of the proof of Proposition 5.1.1.
* **Proposition 5.1.1** (`proposition_5_1_1`, p. 97): if `Σₙ Pⁿ(x, α) > 0` for every `x`, then the
  chain is `ν`-irreducible with `ν = P(α, ·)`, `L(x, α) > 0` for every `x`, and `α` is an
  accessible atom for every maximal irreducibility measure.
* `hitProb_atom_eq`: `L(·, A)` is constant on an atom; **Proposition 5.1.2**
  (`proposition_5_1_2`, p. 98): if `L(x, A) > 0` for some `x ∈ α`, then `α ⇝ A`.

**Corrections.** None. In Proposition 5.1.1 the sum may include `n = 0`: the conclusion
`L(x, α) > 0` holds also for `x ∈ α`.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- An *atom* (MT p. 96): a measurable set `α` such that `P(x, ·) = ν` for every `x ∈ α`, for
one measure `ν`. -/
def IsAtom (P : Kernel X X) (α : Set X) : Prop :=
  MeasurableSet α ∧ ∃ ν : Measure X, ∀ x ∈ α, P x = ν

/-- A single point is an atom (MT p. 96), when points are measurable. -/
theorem isAtom_singleton [MeasurableSingletonClass X] (P : Kernel X X) (x : X) :
    IsAtom P {x} :=
  ⟨measurableSet_singleton x, P x, fun y hy => by rw [mem_singleton_iff.1 hy]⟩

/-- An *accessible atom* (MT p. 96): an atom `α` with `ψ(α) > 0`, where `ψ` is a maximal
irreducibility measure. -/
def IsAccessibleAtom (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (α : Set X) : Prop :=
  IsAtom P α ∧ IsMaximalIrreducibility P ψ ∧ 0 < ψ α

/-- For a maximal irreducibility measure `ψ`, `ψ(A) > 0` iff `L(x, A) > 0` for every `x`. -/
theorem IsMaximalIrreducibility.pos_iff_hitProb_pos {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) :
    0 < ψ A ↔ ∀ x, 0 < hitProb P A x := by
  refine ⟨fun h => hψ.2.1 A hA h, fun h => ?_⟩
  rw [pos_iff_ne_zero]
  intro h0
  have := hψ.hitSet_null hA h0
  have hu : {y | 0 < hitProb P A y} = univ := eq_univ_of_forall h
  rw [hu, Measure.measure_univ_eq_zero] at this
  exact hψ.1 this

/-- The bound in the proof of Proposition 5.1.1 (MT p. 97): if `P(y, ·) = ν` on `α`, then
`Pⁿ⁺¹(x, A) ≥ ∫_α Pⁿ(x, dy) P(y, A) = Pⁿ(x, α) ν(A)`. -/
theorem pow_succ_ge_of_atom (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) {ν : Measure X}
    (hν : ∀ y ∈ α, P y = ν) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (P ^ n) x α * ν A ≤ (P ^ (n + 1)) x A := by
  rw [pow_succ_apply' P n x hA]
  calc (P ^ n) x α * ν A = ∫⁻ y in α, P y A ∂(P ^ n) x := by
        rw [setLIntegral_congr_fun hα (fun y hy => by rw [hν y hy]), setLIntegral_const,
          mul_comm]
    _ ≤ ∫⁻ y, P y A ∂(P ^ n) x := setLIntegral_le_lintegral _ _

/-- If the chain is `φ`-irreducible, then from any nonzero initial law `ρ` it reaches a set of
positive `φ`-measure: `ρPᵐ⁺¹(B) > 0` for some `m`. -/
theorem exists_pow_comp_pos {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {ρ : Measure X} (hρ : ρ ≠ 0) {B : Set X} (hB : MeasurableSet B)
    (hpos : 0 < φ B) :
    ∃ m, 0 < ((P ^ (m + 1) : Kernel X X) ∘ₘ ρ) B := by
  by_contra hc
  push Not at hc
  have hz : ∀ m, ∀ᵐ y ∂ρ, (P ^ (m + 1)) y B = 0 := fun m => by
    have := nonpos_iff_eq_zero.1 (hc m)
    rw [measure_kernel_apply ρ _ hB, lintegral_eq_zero_iff (Kernel.measurable_coe _ hB)] at this
    exact this
  rw [← ae_all_iff] at hz
  have : ∀ᵐ y ∂ρ, False := hz.mono fun y hy => by
    obtain ⟨m, hm⟩ := (hitProb_pos_iff P hB y).1 (hφ B hB hpos y)
    exact (hm.ne' (hy m)).elim
  exact hρ (ae_eq_bot.1 (by simpa using this))

/-- If every state reaches `α` (with `n = 0` allowed), then every state enters `α` at some time
`n ≥ 1`: `L(x, α) > 0` for every `x`. -/
theorem hitProb_pos_of_exists_pow (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (h : ∀ x, ∃ n, 0 < (P ^ n) x α) (x : X) : 0 < hitProb P α x := by
  refine hitProb_pos_of_compl P hα (fun y hy => ?_) x
  obtain ⟨n, hn⟩ := h y
  rcases n with _ | n
  · rw [pow_zero_apply, Measure.dirac_apply' _ hα, indicator_of_notMem hy] at hn
    exact absurd hn (lt_irrefl _)
  · exact (hitProb_pos_iff P hα y).2 ⟨n, hn⟩

/-- **Proposition 5.1.1** (MT p. 97). Let `α` be an atom, `P(x, ·) = ν` for `x ∈ α`, and suppose
`Σₙ Pⁿ(x, α) > 0` for every `x`. Then the chain is `ν`-irreducible, `L(x, α) > 0` for every `x`,
and `α` is an accessible atom: `ψ(α) > 0` for every maximal irreducibility measure `ψ`. -/
theorem proposition_5_1_1 (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : MeasurableSet α)
    {ν : Measure X} (hν : ∀ y ∈ α, P y = ν) (h : ∀ x, ∃ n, 0 < (P ^ n) x α) :
    IsPhiIrreducible P ν ∧ (∀ x, 0 < hitProb P α x) ∧
      ∀ ψ : Measure X, IsMaximalIrreducibility P ψ → IsAccessibleAtom P ψ α := by
  have hL := hitProb_pos_of_exists_pow P hα h
  refine ⟨fun A hA hpos x => ?_, hL, fun ψ hψ =>
    ⟨⟨hα, ν, hν⟩, hψ, (hψ.pos_iff_hitProb_pos hα).2 hL⟩⟩
  obtain ⟨n, hn⟩ := h x
  exact (ENNReal.mul_pos hn.ne' hpos.ne').trans_le
    ((pow_succ_ge_of_atom P hα hν n x hA).trans (pow_le_hitProb P hA n x))

/-- `L(·, A)` is constant on an atom: by the first-step equation,
`L(y, A) = ν(A) + ∫_{Aᶜ} ν(dz) L(z, A)` for every `y ∈ α`. -/
theorem hitProb_atom_eq (P : Kernel X X) [IsMarkovKernel P] {α : Set X} {ν : Measure X}
    (hν : ∀ y ∈ α, P y = ν) {A : Set X} (hA : MeasurableSet A) {x y : X} (hx : x ∈ α)
    (hy : y ∈ α) : hitProb P A y = hitProb P A x := by
  rw [hitProb_first_step P hA x, hitProb_first_step P hA y, hν x hx, hν y hy]

/-- **Proposition 5.1.2** (MT p. 98). If `α` is an atom and `L(x, A) > 0` for some `x ∈ α`, then
`α ⇝ A`: `L(y, A) = L(x, A)` for every `y ∈ α`. -/
theorem proposition_5_1_2 (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {A : Set X} (hA : MeasurableSet A) {x : X} (hx : x ∈ α) (hpos : 0 < hitProb P A x) :
    UnifAccessible P α A := by
  obtain ⟨-, ν, hν⟩ := hα
  exact ⟨hitProb P A x, hpos, fun y hy => (hitProb_atom_eq P hν hA hx hy).ge⟩

end MeynTweedie.InvarianceTightness
