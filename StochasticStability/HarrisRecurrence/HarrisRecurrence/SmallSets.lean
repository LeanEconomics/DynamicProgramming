/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.SplitMarginal

/-!
# Small sets (MT §5.2)

Meyn and Tweedie, §5.2, pp. 102–106: the definition and the elementary results. The existence
of small sets (Theorems 5.2.1–5.2.3, Proposition 5.2.4 (ii)) is in `SmallSetExistence`.

* `IsSmallSet P m ν C` (5.14), p. 102: `C` is `νₘ`-small, `m ≥ 1`, `ν ≠ 0` and `Pᵐ(x, ·) ≥ ν` for
  every `x ∈ C`; `IsSmall P C`: `C` is small for some `m` and `ν`.
* `IsSmallSet.mono`, `IsSmallSet.smul`, `IsSmallSet.le_apply`: elementary properties;
  `IsSmallSet.measure_univ_le`: `ν(X) ≤ 1` when `C` is non-empty.
* `isSmallSet_of_atom` (p. 102): an atom with `P(x, ·) = ν` is `ν`-small with `m = 1`.
* `pow_add_ge_of_le`: the Chapman–Kolmogorov bound `Pᵐ⁺ⁿ(x, B) ≥ Pᵐ(x, C) ν(B)` when
  `Pⁿ(y, ·) ≥ ν` on `C`; `comp_le_comp`: `μ ≤ μ'` implies `μK ≤ μ'K`.
* **Proposition 5.2.4 (i)** (`proposition_5_2_4_i`, p. 105): if `C` is `νₙ`-small and
  `Pᵐ(x, C) ≥ δ > 0` on `D`, then `D` is `δνₙ`-small with index `m + n`.
* **Proposition 5.2.4 (iii)** (`proposition_5_2_4_iii`, p. 106): for a `φ`-irreducible chain
  and a small `C` with `φ(C) > 0`, `C` is `ν_M`-small for some `M` with `ν_M(C) > 0`, namely
  `ν_M = νPᵐ⁺¹`.
* `IsSmallSet.minorization`: a `ν`-small set with `ν(C) > 0` gives the minorization condition
  (5.2) for `Pᵐ`, with the book's normalisation `ν(Cᶜ) = 0`.

**Corrections.** None.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- `C` is a **`νₘ`-small set** (5.14), MT p. 102: `C` is measurable, `m ≥ 1`, `ν` is a nonzero
measure and `Pᵐ(x, B) ≥ ν(B)` for every `x ∈ C` and every measurable `B`. -/
def IsSmallSet (P : Kernel X X) (m : ℕ) (ν : Measure X) (C : Set X) : Prop :=
  MeasurableSet C ∧ 0 < m ∧ ν ≠ 0 ∧ ∀ x ∈ C, ν ≤ (P ^ m) x

/-- `C` is a **small set** (MT p. 102): it is `νₘ`-small for some `m ≥ 1` and nonzero `ν`. -/
def IsSmall (P : Kernel X X) (C : Set X) : Prop := ∃ m ν, IsSmallSet P m ν C

/-- The bound `Pᵐ(x, B) ≥ ν(B)` of a small set. -/
theorem IsSmallSet.le_apply {P : Kernel X X} {m : ℕ} {ν : Measure X} {C : Set X}
    (h : IsSmallSet P m ν C) {x : X} (hx : x ∈ C) (B : Set X) : ν B ≤ (P ^ m) x B :=
  h.2.2.2 x hx B

/-- A measurable subset of a small set is small. -/
theorem IsSmallSet.mono {P : Kernel X X} {m : ℕ} {ν : Measure X} {C D : Set X}
    (h : IsSmallSet P m ν C) (hD : MeasurableSet D) (hDC : D ⊆ C) : IsSmallSet P m ν D :=
  ⟨hD, h.2.1, h.2.2.1, fun x hx => h.2.2.2 x (hDC hx)⟩

/-- A nonzero multiple of a nonzero measure is nonzero. -/
theorem smul_measure_ne_zero {ν : Measure X} (hν : ν ≠ 0) {c : ℝ≥0∞} (hc : c ≠ 0) :
    c • ν ≠ 0 := fun h => by
  have h1 := congrArg (fun μ : Measure X => μ univ) h
  simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
    Measure.measure_univ_eq_zero] at h1
  exact h1.elim hc hν

/-- A nonzero multiple `cν` with `c ≤ 1` of a minorizing measure is minorizing. -/
theorem IsSmallSet.smul {P : Kernel X X} {m : ℕ} {ν : Measure X} {C : Set X}
    (h : IsSmallSet P m ν C) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc1 : c ≤ 1) : IsSmallSet P m (c • ν) C :=
  ⟨h.1, h.2.1, smul_measure_ne_zero h.2.2.1 hc0, fun x hx => by
    refine Measure.le_intro fun B _ _ => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact (mul_le_of_le_one_left' hc1).trans (h.le_apply hx B)⟩

/-- The minorizing measure of a non-empty small set has mass at most one. -/
theorem IsSmallSet.measure_univ_le {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} {ν : Measure X}
    {C : Set X} (h : IsSmallSet P m ν C) (hne : C.Nonempty) : ν univ ≤ 1 := by
  obtain ⟨x, hx⟩ := hne
  have := isMarkovKernel_pow P m
  exact (h.le_apply hx univ).trans prob_le_one

/-- An atom is small (MT p. 102): if `P(x, ·) = ν` on `α`, with `ν ≠ 0`, then `α` is `ν`-small
with `m = 1`. -/
theorem isSmallSet_of_atom (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) {ν : Measure X}
    (hν : ∀ x ∈ α, P x = ν) (h0 : ν ≠ 0) : IsSmallSet P 1 ν α :=
  ⟨hα, one_pos, h0, fun x hx => by rw [pow_one, hν x hx]⟩

/-- **Chapman–Kolmogorov through `C`**: if `Pⁿ(y, ·) ≥ ν` for every `y ∈ C`, then
`Pᵐ⁺ⁿ(x, B) ≥ ∫_C Pᵐ(x, dy) Pⁿ(y, B) ≥ Pᵐ(x, C) ν(B)` (5.26). -/
theorem pow_add_ge_of_le (P : Kernel X X) {m n : ℕ} {C : Set X}
    {ν : Measure X} (hν : ∀ y ∈ C, ν ≤ (P ^ n) y) (x : X) {B : Set X} (hB : MeasurableSet B) :
    (P ^ m) x C * ν B ≤ (P ^ (m + n)) x B := by
  rw [Kernel.pow_add_apply_eq_lintegral P m n x hB]
  calc (P ^ m) x C * ν B = ∫⁻ _ in C, ν B ∂(P ^ m) x := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in C, (P ^ n) y B ∂(P ^ m) x := setLIntegral_mono (Kernel.measurable_coe _ hB)
        fun y hy => hν y hy B
    _ ≤ ∫⁻ y, (P ^ n) y B ∂(P ^ m) x := setLIntegral_le_lintegral _ _

/-- The bound `Pᵐ⁺ⁿ(x, ·) ≥ Pᵐ(x, C) ν` as an inequality of measures. -/
theorem smul_le_pow_add_of_le (P : Kernel X X) {m n : ℕ} {C : Set X}
    {ν : Measure X} (hν : ∀ y ∈ C, ν ≤ (P ^ n) y) (x : X) :
    (P ^ m) x C • ν ≤ (P ^ (m + n)) x :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact pow_add_ge_of_le P hν x hB

/-- Composition with a kernel is monotone in the measure: `μ ≤ μ'` implies `μK ≤ μ'K`. -/
theorem comp_le_comp {Y : Type*} [MeasurableSpace Y] (K : Kernel X Y) {μ μ' : Measure X}
    (h : μ ≤ μ') : K ∘ₘ μ ≤ K ∘ₘ μ' :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.bind_apply hB K.aemeasurable, Measure.bind_apply hB K.aemeasurable]
    exact lintegral_mono' h le_rfl

/-- **Proposition 5.2.4 (i)** (MT p. 105). If `C` is `νₙ`-small and `Pᵐ(x, C) ≥ δ > 0` for every
`x ∈ D`, then `D` is `δνₙ`-small with index `m + n`. -/
theorem proposition_5_2_4_i (P : Kernel X X) {n m : ℕ} {ν : Measure X} {C D : Set X}
    (hC : IsSmallSet P n ν C) (hD : MeasurableSet D) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (h : ∀ x ∈ D, δ ≤ (P ^ m) x C) : IsSmallSet P (m + n) (δ • ν) D :=
  ⟨hD, Nat.add_pos_right m hC.2.1, smul_measure_ne_zero hC.2.2.1 hδ.ne', fun x hx =>
    Measure.le_intro fun B hB _ => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact (mul_le_mul_left (h x hx) _).trans (pow_add_ge_of_le P hC.2.2.2 x hB)⟩

/-- **Proposition 5.2.4 (iii)** (MT p. 106). For a `φ`-irreducible chain and a `νₙ`-small set `C`
with `φ(C) > 0`, there are `m` and `ν_M = νPᵐ⁺¹` such that `C` is `ν_M`-small with index
`M = n + m + 1` and `ν_M(C) > 0`. -/
theorem proposition_5_2_4_iii (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {n : ℕ} {ν : Measure X} {C : Set X} (hC : IsSmallSet P n ν C)
    (hCφ : 0 < φ C) :
    ∃ m, IsSmallSet P (n + (m + 1)) ((P ^ (m + 1) : Kernel X X) ∘ₘ ν) C ∧
      0 < ((P ^ (m + 1) : Kernel X X) ∘ₘ ν) C := by
  obtain ⟨m, hm⟩ := exists_pow_comp_pos hφ hC.2.2.1 hC.1 hCφ
  refine ⟨m, ⟨hC.1, by omega, fun h0 => by rw [h0] at hm; exact lt_irrefl _ hm, fun x hx => ?_⟩,
    hm⟩
  rw [show n + (m + 1) = (m + 1) + n by omega, Kernel.pow_add P (m + 1) n, Kernel.comp_apply]
  exact comp_le_comp _ (hC.2.2.2 x hx)

/-- A `ν`-small set `C` with `ν(C) > 0` gives the minorization condition (5.2) for `Pᵐ` on `C`,
with `ν(Cᶜ) = 0`. -/
noncomputable def IsSmallSet.minorization {P : Kernel X X} [IsMarkovKernel P] {m : ℕ}
    {ν : Measure X} {C : Set X} (h : IsSmallSet P m ν C) (hpos : 0 < ν C) : Minorization (P ^ m) :=
  Minorization.ofLe h.1 h.2.2.2 hpos (ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono (subset_univ C)).trans (h.measure_univ_le (nonempty_of_measure_ne_zero
      hpos.ne'))))

/-- The minorization of a small set lives on that set. -/
theorem IsSmallSet.minorization_C {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} {ν : Measure X}
    {C : Set X} (h : IsSmallSet P m ν C) (hpos : 0 < ν C) : (h.minorization hpos).C = C := rfl

/-- The minorization of a small set satisfies the book's normalisation `ν(Cᶜ) = 0`. -/
theorem IsSmallSet.minorization_isConcentrated {P : Kernel X X} [IsMarkovKernel P] {m : ℕ}
    {ν : Measure X} {C : Set X} (h : IsSmallSet P m ν C) (hpos : 0 < ν C) :
    (h.minorization hpos).IsConcentrated :=
  Minorization.ofLe_isConcentrated _ _ _ _

end MeynTweedie.HarrisRecurrence
