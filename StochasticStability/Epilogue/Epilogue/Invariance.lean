/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.HarrisDefinitions

/-!
# Stationarity and invariance (MT Chapter 10 introduction and §10.1)

Meyn and Tweedie, pp. 229–234. A measure `μ` and a kernel `P` give the measure
`μP = P ∘ₘ μ`, `μP(A) = ∫ μ(dx) P(x, A)`.

**Definitions** (pp. 229–232).
* `IsInvariant P μ` (10.1): `μP = μ`; `IsSubinvariant P μ` (10.5): `μP ≤ μ`, both as equations of
  measures, with no σ-finiteness; `IsInvariantMeasure`, `IsSubinvariantMeasure`: the book's
  notions, which add `SigmaFinite μ`.
* `IsPositive P ψ` (p. 230): `ψ` is a maximal irreducibility measure and there is an invariant
  probability measure; `IsNull P ψ`: `ψ`-irreducible with no invariant probability measure;
  `IsPositiveHarris P ψ` (p. 231): Harris and positive.

**Basic properties.**
* `isInvariant_iff`, `isSubinvariant_iff`: the set-wise forms of (10.1) and (10.5).
* `IsInvariant.pow` (the iteration on p. 231): `μPⁿ = μ`; `IsSubinvariant.pow`: `μPⁿ ≤ μ`.
* `sampledKernel_comp_apply`: `μK_a(A) = Σₙ a(n) μPⁿ(A)`; (10.6) `IsSubinvariant.sampledKernel`:
  `μK_a ≤ μ` for every `a` with `Σ a ≤ 1`; `IsInvariant.sampledKernel`: `μK_a = μ` for a sampling
  distribution `a`; `IsInvariant.resolvent`, `IsSubinvariant.resolvent`.
* Stationarity (p. 231): `IsInvariant.map_coord`, under `P_π` every `Φₙ` has law `π`;
  `IsInvariant.map_shift`, the shifted chain `θⁿΦ` has law `P_π`, so the chain started at `π` is
  a stationary process; `isInvariant_iff_map_shift`: conversely, stationarity of `Φ` under `P_π`
  forces invariance of `π`.
* `lintegral_potKernel_of_isInvariant`: `∫ μ(dx) U(x, A) = Σ_{n ≥ 1} μ(A)`.

**Results.**
* **Proposition 10.1.1** (`proposition_10_1_1`, p. 231): a positive chain is recurrent.
* **Proposition 10.1.2** (p. 233), for a `ψ`-irreducible chain and a measure `μ` with `μP ≤ μ`
  and `μ(A) < ∞` for one `A ∈ B⁺(X)`: (i) `proposition_10_1_2_i`, `μ` is σ-finite; (ii)
  `proposition_10_1_2_ii`, `ψ ≪ μ` if `μ ≠ 0`; (iii) `proposition_10_1_2_iii`, `μ(C) < ∞` for every
  petite `C`; (iv) `proposition_10_1_2_iv`, a finite subinvariant measure is invariant (for any
  chain).
* **Proposition 10.1.3** (`proposition_10_1_3`, p. 233): a transient chain has a σ-finite
  subinvariant measure which is not invariant, namely `U(x, ·)`; `potKernel_comp_add` is the
  identity (10.9), `U(x, ·)P + P(x, ·) = U(x, ·)`.

**Correction.** Proposition 10.1.2 (ii) needs `μ ≠ 0`: the zero measure satisfies all the
hypotheses (`μ(A) = 0 < ∞`), and `ψ ≪ 0` fails since `ψ ≠ 0`
(`proposition_10_1_2_ii_counterexample`).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Definitions -/

/-- The invariance equation (10.1), MT p. 229: `μP = μ`, i.e. `μ(A) = ∫ μ(dx) P(x, A)`. -/
def IsInvariant (P : Kernel X X) (μ : Measure X) : Prop := P ∘ₘ μ = μ

/-- The subinvariance inequality (10.5), MT p. 232: `μP ≤ μ`. -/
def IsSubinvariant (P : Kernel X X) (μ : Measure X) : Prop := P ∘ₘ μ ≤ μ

/-- An *invariant measure* (MT p. 229): a σ-finite measure with `μP = μ`. -/
def IsInvariantMeasure (P : Kernel X X) (μ : Measure X) : Prop :=
  SigmaFinite μ ∧ IsInvariant P μ

/-- A *subinvariant measure* (MT p. 232): a σ-finite measure with `μP ≤ μ`. -/
def IsSubinvariantMeasure (P : Kernel X X) (μ : Measure X) : Prop :=
  SigmaFinite μ ∧ IsSubinvariant P μ

/-- A *positive chain* (MT p. 230): `ψ`-irreducible, with an invariant probability measure. -/
def IsPositive (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsMaximalIrreducibility P ψ ∧ ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π

/-- A *null chain* (MT p. 230): `ψ`-irreducible, with no invariant probability measure. -/
def IsNull (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsMaximalIrreducibility P ψ ∧ ¬ ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π

/-- A *positive Harris chain* (MT p. 231): Harris recurrent and positive. -/
def IsPositiveHarris (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsHarris P ψ ∧ IsPositive P ψ

/-- A `ψ`-irreducible chain is either positive or null. -/
theorem isPositive_or_isNull {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) : IsPositive P ψ ∨ IsNull P ψ := by
  by_cases h : ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π
  · exact Or.inl ⟨hψ, h⟩
  · exact Or.inr ⟨hψ, h⟩

/-- A chain is not both positive and null. -/
theorem IsPositive.not_isNull {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (h : IsPositive P ψ) : ¬ IsNull P ψ := fun h' => h'.2 h.2

/-! ### Set-wise forms -/

/-- (10.1) set-wise: `μ` is invariant iff `∫ μ(dx) P(x, A) = μ(A)` for measurable `A`. -/
theorem isInvariant_iff (P : Kernel X X) (μ : Measure X) :
    IsInvariant P μ ↔ ∀ A, MeasurableSet A → ∫⁻ x, P x A ∂μ = μ A := by
  constructor
  · intro h A hA
    rw [← measure_kernel_apply μ P hA, h]
  · intro h
    ext A hA
    rw [measure_kernel_apply μ P hA, h A hA]

/-- (10.5) set-wise: `μ` is subinvariant iff `∫ μ(dx) P(x, A) ≤ μ(A)` for measurable `A`. -/
theorem isSubinvariant_iff (P : Kernel X X) (μ : Measure X) :
    IsSubinvariant P μ ↔ ∀ A, MeasurableSet A → ∫⁻ x, P x A ∂μ ≤ μ A := by
  constructor
  · intro h A hA
    rw [← measure_kernel_apply μ P hA]
    exact h A
  · intro h
    exact Measure.le_intro fun A hA _ => by rw [measure_kernel_apply μ P hA]; exact h A hA

/-- An invariant measure is subinvariant. -/
theorem IsInvariant.isSubinvariant {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ) :
    IsSubinvariant P μ := h.le

/-- An invariant measure in the book's sense is a subinvariant measure. -/
theorem IsInvariantMeasure.isSubinvariantMeasure {P : Kernel X X} {μ : Measure X}
    (h : IsInvariantMeasure P μ) : IsSubinvariantMeasure P μ := ⟨h.1, h.2.isSubinvariant⟩

/-- Invariance is preserved by positive scalar multiples. -/
theorem IsInvariant.smul {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ) (c : ℝ≥0∞) :
    IsInvariant P (c • μ) := by
  unfold IsInvariant at *
  rw [Measure.comp_smul, h]

/-- Subinvariance is preserved by scalar multiples. -/
theorem IsSubinvariant.smul {P : Kernel X X} {μ : Measure X} (h : IsSubinvariant P μ)
    (c : ℝ≥0∞) : IsSubinvariant P (c • μ) := by
  unfold IsSubinvariant at *
  rw [Measure.comp_smul]
  exact Measure.le_intro fun A _ _ => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (h A) c

/-- Invariance is preserved by sums. -/
theorem IsInvariant.add {P : Kernel X X} {μ ν : Measure X} (hμ : IsInvariant P μ)
    (hν : IsInvariant P ν) : IsInvariant P (μ + ν) := by
  unfold IsInvariant at *
  rw [Measure.comp_add, hμ, hν]

/-! ### Iterates and sampled kernels -/

/-- The iteration on MT p. 231: an invariant `μ` satisfies `μPⁿ = μ`. -/
theorem IsInvariant.pow {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ) (n : ℕ) :
    IsInvariant (P ^ n) μ := by
  unfold IsInvariant at *
  induction n with
  | zero => rw [pow_zero]; exact Measure.id_comp
  | succ n ih =>
    rw [pow_add_eq P n 1, pow_one, ← Measure.comp_assoc, ih, h]

/-- MT p. 232: a subinvariant `μ` satisfies `μPⁿ ≤ μ`. -/
theorem IsSubinvariant.pow {P : Kernel X X} {μ : Measure X} (h : IsSubinvariant P μ) (n : ℕ) :
    IsSubinvariant (P ^ n) μ := by
  unfold IsSubinvariant at *
  induction n with
  | zero => rw [pow_zero]; exact Measure.id_comp.le
  | succ n ih =>
    rw [pow_add_eq P n 1, pow_one, ← Measure.comp_assoc]
    exact (comp_le_comp P ih).trans h

/-- `μK_a(A) = Σₙ a(n) μPⁿ(A)`. -/
theorem sampledKernel_comp_apply (P : Kernel X X) (a : ℕ → ℝ≥0∞) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : (sampledKernel P a ∘ₘ μ) A = ∑' n, a n * ((P ^ n) ∘ₘ μ) A := by
  rw [measure_kernel_apply μ _ hA]
  simp_rw [sampledKernel_apply P a _ hA]
  rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA), measure_kernel_apply μ _ hA]

/-- (10.6), MT p. 232: a subinvariant `μ` satisfies `μK_a ≤ μ` whenever `Σ a ≤ 1`. -/
theorem IsSubinvariant.sampledKernel {P : Kernel X X} {μ : Measure X} (h : IsSubinvariant P μ)
    {a : ℕ → ℝ≥0∞} (ha : ∑' n, a n ≤ 1) : IsSubinvariant (sampledKernel P a) μ :=
  Measure.le_intro fun A hA _ => by
    rw [sampledKernel_comp_apply P a μ hA]
    calc ∑' n, a n * ((P ^ n) ∘ₘ μ) A ≤ ∑' n, a n * μ A :=
          ENNReal.tsum_le_tsum fun n => mul_le_mul_right ((h.pow n) A) _
      _ = (∑' n, a n) * μ A := ENNReal.tsum_mul_right
      _ ≤ 1 * μ A := mul_le_mul_left ha _
      _ = μ A := one_mul _

/-- MT p. 242 (via (10.4)): an invariant `μ` is invariant for every `K_a` with `Σ a = 1`. -/
theorem IsInvariant.sampledKernel {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ)
    {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) : IsInvariant (sampledKernel P a) μ := by
  ext A hA
  rw [sampledKernel_comp_apply P a μ hA]
  simp_rw [show ∀ n, ((P ^ n : Kernel X X) ∘ₘ μ) A = μ A from fun n => by rw [(h.pow n)]]
  rw [ENNReal.tsum_mul_right, ha, one_mul]

/-- An invariant `μ` is invariant for the resolvent `K_{a_ε}`, `ε < 1`. -/
theorem IsInvariant.resolvent {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ)
    {ε : ℝ≥0∞} (hε : ε < 1) : IsInvariant (resolvent P ε) μ :=
  h.sampledKernel (tsum_geometric_weights hε)

/-- A subinvariant `μ` is subinvariant for the resolvent `K_{a_ε}`, `ε < 1`. -/
theorem IsSubinvariant.resolvent {P : Kernel X X} {μ : Measure X} (h : IsSubinvariant P μ)
    {ε : ℝ≥0∞} (hε : ε < 1) : IsSubinvariant (resolvent P ε) μ :=
  h.sampledKernel (tsum_geometric_weights hε).le

/-! ### Stationarity -/

/-- MT p. 231: under `P_π`, with `π` an invariant probability, every `Φₙ` has law `π`. -/
theorem IsInvariant.map_coord {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (h : IsInvariant P π) (n : ℕ) :
    (pathMeasure P π).map (fun ω => ω n) = π :=
  (pathMeasure_map_coord P π n).trans (h.pow n)

/-- **Stationarity** (MT p. 231): started at an invariant probability `π`, the shifted chain
`θⁿΦ` has the same law `P_π` as `Φ`; all finite-dimensional distributions are invariant under
translation in time. -/
theorem IsInvariant.map_shift {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (h : IsInvariant P π) (n : ℕ) :
    (pathMeasure P π).map (shift n) = pathMeasure P π := by
  have hm := markov_measure P π (n := n) (G := univ) MeasurableSet.univ
  rw [Measure.restrict_univ] at hm
  rw [hm, h.map_coord n, pathMeasure_eq_comp]

/-- MT p. 231: the chain started at a probability `π` is stationary iff `π` is invariant. -/
theorem isInvariant_iff_map_shift {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] :
    IsInvariant P π ↔ ∀ n, (pathMeasure P π).map (shift n) = pathMeasure P π := by
  refine ⟨fun h n => h.map_shift n, fun h => ?_⟩
  have h1 := congrArg (fun m : Measure (ℕ → X) => m.map (fun ω => ω 0)) (h 1)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_shift 1)] at h1
  have h2 : (fun ω : ℕ → X => ω 0) ∘ shift 1 = fun ω => ω 1 := by
    ext ω; simp [shift]
  rw [h2, pathMeasure_map_coord, pathMeasure_map_coord, pow_one, pow_zero] at h1
  unfold IsInvariant
  rw [h1]
  exact Measure.id_comp

/-! ### Proposition 10.1.1 -/

/-- `∫ μ(dx) U(x, A) = Σ_{n ≥ 1} μPⁿ(A)`. -/
theorem lintegral_potKernel (P : Kernel X X) (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ x, potKernel P x A ∂μ = ∑' n, ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) A := by
  simp_rw [potKernel_apply P _ hA]
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ hA).aemeasurable]
  exact tsum_congr fun n => (measure_kernel_apply μ _ hA).symm

/-- For an invariant `μ`, `∫ μ(dx) U(x, A) = Σ_{n ≥ 1} μ(A)`, which is `∞` unless `μ(A) = 0`. -/
theorem lintegral_potKernel_of_isInvariant {P : Kernel X X} {μ : Measure X}
    (h : IsInvariant P μ) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ x, potKernel P x A ∂μ = ∑' _ : ℕ, μ A := by
  rw [lintegral_potKernel P μ hA]
  exact tsum_congr fun n => by rw [h.pow (n + 1)]

/-- An invariant probability measure charges no uniformly transient set (proof of
Proposition 10.1.1). -/
theorem IsInvariant.measure_eq_zero_of_uniformlyTransient {P : Kernel X X} [IsMarkovKernel P]
    {π : Measure X} [IsProbabilityMeasure π] (h : IsInvariant P π) {A : Set X}
    (hA : IsUniformlyTransient P A) : π A = 0 := by
  obtain ⟨hAm, M, hM, hle⟩ := hA
  by_contra h0
  have htop := lintegral_potKernel_of_isInvariant h hAm
  rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at htop
  have : ∫⁻ x, potKernel P x A ∂π ≤ ∫⁻ _, 1 + M ∂π :=
    lintegral_mono fun x => proposition_8_3_1_i P hAm hle x
  rw [htop, lintegral_const, measure_univ, mul_one] at this
  exact (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hM⟩) (top_le_iff.1 this)

/-- **Proposition 10.1.1** (MT p. 231): a positive chain is recurrent. -/
theorem proposition_10_1_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (h : IsPositive P ψ) : IsRecurrentChain P ψ := by
  obtain ⟨hψ, π, hπ, hinv⟩ := h
  rcases theorem_8_3_4 P hψ with hrec | htr
  · exact hrec
  · exfalso
    obtain ⟨B, hB, hcov⟩ := htr.2
    have h0 : π univ = 0 := by
      refine le_antisymm ?_ (zero_le)
      calc π univ ≤ π (⋃ n, B n) := measure_mono hcov
        _ ≤ ∑' n, π (B n) := measure_iUnion_le _
        _ = 0 := by simp [hinv.measure_eq_zero_of_uniformlyTransient (hB _)]
    simp at h0

/-- A positive Harris chain is positive. -/
theorem IsPositiveHarris.isPositive {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (h : IsPositiveHarris P ψ) : IsPositive P ψ := h.2

/-! ### Proposition 10.1.2 -/

/-- The sets `A*(j) = {y : K_{a_{1/2}}(y, A) > (j + 1)⁻¹}` of the proof of Proposition 10.1.2. -/
noncomputable def resolventLevel (P : Kernel X X) (A : Set X) (j : ℕ) : Set X :=
  {y | ((j : ℝ≥0∞) + 1)⁻¹ < resolventHalf P y A}

/-- `A*(j)` is measurable. -/
theorem measurableSet_resolventLevel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (j : ℕ) : MeasurableSet (resolventLevel P A j) :=
  measurableSet_lt measurable_const (Kernel.measurable_coe _ hA)

/-- For a `ψ`-irreducible chain and `ψ(A) > 0`, the sets `A*(j)` cover `X`. -/
theorem iUnion_resolventLevel {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {A : Set X} (hA : MeasurableSet A) (hψA : 0 < ψ A) :
    ⋃ j, resolventLevel P A j = univ := by
  refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
  have hpos := ((proposition_4_2_1 P ψ).2.2.1 hψ) A hA hψA y
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
  refine ⟨j, ?_⟩
  change ((j : ℝ≥0∞) + 1)⁻¹ < _
  exact lt_of_le_of_lt (ENNReal.inv_le_inv.2 le_self_add) hj

/-- For a subinvariant `μ`, `μ(A*(j)) ≤ (j + 1) μ(A)`. -/
theorem measure_resolventLevel_le {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    (h : IsSubinvariant P μ) {A : Set X} (hA : MeasurableSet A) (j : ℕ) :
    μ (resolventLevel P A j) ≤ ((j : ℝ≥0∞) + 1) * μ A := by
  have hK := (h.resolvent (ε := 2⁻¹) (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)) A
  rw [measure_kernel_apply μ _ hA] at hK
  have hS := measurableSet_resolventLevel P hA j
  have h1 : ((j : ℝ≥0∞) + 1)⁻¹ * μ (resolventLevel P A j) ≤ μ A :=
    calc ((j : ℝ≥0∞) + 1)⁻¹ * μ (resolventLevel P A j)
        = ∫⁻ _ in resolventLevel P A j, ((j : ℝ≥0∞) + 1)⁻¹ ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in resolventLevel P A j, resolventHalf P y A ∂μ :=
          setLIntegral_mono (Kernel.measurable_coe _ hA) fun y hy => le_of_lt hy
      _ ≤ ∫⁻ y, resolventHalf P y A ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ μ A := hK
  calc μ (resolventLevel P A j)
      = ((j : ℝ≥0∞) + 1) * (((j : ℝ≥0∞) + 1)⁻¹ * μ (resolventLevel P A j)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    _ ≤ ((j : ℝ≥0∞) + 1) * μ A := mul_le_mul_right h1 _

/-- **Proposition 10.1.2 (i)** (MT p. 233): for a `ψ`-irreducible chain, a measure `μ` with
`μP ≤ μ` and `μ(A) < ∞` for some `A ∈ B⁺(X)` is σ-finite. -/
theorem proposition_10_1_2_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {μ : Measure X} (h : IsSubinvariant P μ) {A : Set X}
    (hA : MeasurableSet A) (hψA : 0 < ψ A) (hμA : μ A ≠ ∞) : SigmaFinite μ :=
  ⟨⟨{ set := resolventLevel P A
      set_mem := fun _ => trivial
      finite := fun j => lt_of_le_of_lt (measure_resolventLevel_le h hA j)
        (ENNReal.mul_lt_top (by simp) hμA.lt_top)
      spanning := iUnion_resolventLevel hψ hA hψA }⟩⟩

/-- Proposition 10.1.2 (i) in the book's language: such a `μ` is a subinvariant measure. -/
theorem proposition_10_1_2_i' {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {μ : Measure X} (h : IsSubinvariant P μ) {A : Set X}
    (hA : MeasurableSet A) (hψA : 0 < ψ A) (hμA : μ A ≠ ∞) : IsSubinvariantMeasure P μ :=
  ⟨proposition_10_1_2_i hψ h hA hψA hμA, h⟩

/-- For a `ψ`-irreducible chain, a nonzero subinvariant `μ` charges every set of `B⁺(X)`. -/
theorem IsSubinvariant.pos_of_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {μ : Measure X} (h : IsSubinvariant P μ) (hμ : μ ≠ 0)
    {B : Set X} (hB : MeasurableSet B) (hψB : 0 < ψ B) : 0 < μ B := by
  have hK := (h.resolvent (ε := 2⁻¹) (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)) B
  rw [measure_kernel_apply μ _ hB] at hK
  exact lt_of_lt_of_le (lintegral_pos_of_pos hμ (Kernel.measurable_coe _ hB)
    (((proposition_4_2_1 P ψ).2.2.1 hψ) B hB hψB)) hK

/-- **Proposition 10.1.2 (ii)** (MT p. 233): for a `ψ`-irreducible chain, a nonzero measure with
`μP ≤ μ` dominates `ψ`: `ψ ≪ μ`. -/
theorem proposition_10_1_2_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {μ : Measure X} (h : IsSubinvariant P μ) (hμ : μ ≠ 0) :
    ψ ≪ μ := by
  refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
  by_contra hne
  exact (h.pos_of_pos hψ hμ hB (pos_iff_ne_zero.2 hne)).ne' h0

/-- The correction to Proposition 10.1.2 (ii): without `μ ≠ 0` it fails, for the zero measure
and any chain with a nonzero irreducibility measure. -/
theorem proposition_10_1_2_ii_counterexample {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ0 : ψ ≠ 0) : IsSubinvariant P 0 ∧ ¬ ψ ≪ (0 : Measure X) := by
  refine ⟨by simp [IsSubinvariant], fun hac => hψ0 ?_⟩
  rw [← Measure.measure_univ_eq_zero]
  exact hac (by simp)

/-- **Proposition 10.1.2 (iii)** (MT p. 233): for a `ψ`-irreducible chain and `μ` with `μP ≤ μ`
and `μ(A) < ∞` for some `A ∈ B⁺(X)`, every petite set has finite `μ`-measure. -/
theorem proposition_10_1_2_iii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {μ : Measure X} (h : IsSubinvariant P μ) {A : Set X}
    (hA : MeasurableSet A) (hψA : 0 < ψ A) (hμA : μ A ≠ ∞) {C : Set X} (hC : IsPetite P C) :
    μ C < ∞ := by
  obtain ⟨a, ν, -, ha, hν, hle⟩ := hC
  have hνu : 0 < ν (⋃ j, resolventLevel P A j) := by
    rw [iUnion_resolventLevel hψ hA hψA]
    exact pos_iff_ne_zero.2 (fun h0 => hν (Measure.measure_univ_eq_zero.1 h0))
  obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion hνu
  have hS := measurableSet_resolventLevel P hA j
  have h1 : μ C * ν (resolventLevel P A j) ≤ μ (resolventLevel P A j) := by
    have := (smul_le_comp_of_le_on (sampledKernel P a) μ hle) (resolventLevel P A j)
    rw [Measure.smul_apply, smul_eq_mul] at this
    exact this.trans ((h.sampledKernel ha.le) _)
  have h2 : μ (resolventLevel P A j) < ∞ :=
    lt_of_le_of_lt (measure_resolventLevel_le h hA j) (ENNReal.mul_lt_top (by simp) hμA.lt_top)
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.top_mul hj.ne'] at h1
  exact h2.ne (top_le_iff.1 h1)

/-- `(μP)(X) = μ(X)` for a transition probability kernel. -/
theorem comp_apply_univ (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    (P ∘ₘ μ) univ = μ univ := by
  rw [measure_kernel_apply μ P MeasurableSet.univ]
  simp

/-- **Proposition 10.1.2 (iv)** (MT p. 233): a finite measure with `μP ≤ μ` is invariant. No
irreducibility is needed. -/
theorem proposition_10_1_2_iv {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    (h : IsSubinvariant P μ) (hfin : μ univ ≠ ∞) : IsInvariant P μ := by
  refine le_antisymm h (Measure.le_intro fun A hA _ => ?_)
  have hu := comp_apply_univ P μ
  have hfin' : (P ∘ₘ μ) univ ≠ ∞ := by rw [hu]; exact hfin
  have h1 := measure_compl hA (measure_ne_top_of_subset (subset_univ A) hfin)
  have h2 := measure_compl (μ := P ∘ₘ μ) hA (measure_ne_top_of_subset (subset_univ A) hfin')
  have h3 : (P ∘ₘ μ) Aᶜ ≤ μ Aᶜ := h Aᶜ
  rw [h1, h2, hu] at h3
  exact (ENNReal.sub_le_sub_iff_left (measure_mono (subset_univ A)) hfin).1 h3

/-- A finite subinvariant measure is an invariant measure in the book's sense. -/
theorem IsSubinvariant.isInvariantMeasure_of_finite {P : Kernel X X} [IsMarkovKernel P]
    {μ : Measure X} (h : IsSubinvariant P μ) (hfin : μ univ ≠ ∞) : IsInvariantMeasure P μ := by
  have : IsFiniteMeasure μ := ⟨hfin.lt_top⟩
  exact ⟨inferInstance, proposition_10_1_2_iv h hfin⟩

/-! ### Proposition 10.1.3 -/

/-- (10.9), MT p. 234: `U(x, ·)P + P(x, ·) = U(x, ·)`. -/
theorem potKernel_comp_add (P : Kernel X X) (x : X) :
    P ∘ₘ potKernel P x + P x = potKernel P x := by
  ext A hA
  rw [Measure.add_apply, measure_kernel_apply _ P hA, potKernel_apply P x hA,
    tsum_eq_zero_add' ENNReal.summable, zero_add, pow_one, add_comm]
  congr 1
  rw [potKernel, Kernel.sum_apply, lintegral_sum_measure]
  exact tsum_congr fun n => (pow_succ_apply' P (n + 1) x hA).symm

/-- `U(x, ·)` is subinvariant (MT p. 234). -/
theorem isSubinvariant_potKernel (P : Kernel X X) (x : X) :
    IsSubinvariant P (potKernel P x) := by
  unfold IsSubinvariant
  conv_rhs => rw [← potKernel_comp_add P x]
  exact Measure.le_add_right le_rfl

/-- **Proposition 10.1.3** (MT p. 233): a transient chain has a strictly subinvariant measure:
`U(x, ·)` is σ-finite, subinvariant and not invariant. -/
theorem proposition_10_1_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (h : IsTransientChain P ψ) (x : X) :
    IsSubinvariantMeasure P (potKernel P x) ∧ ¬ IsInvariant P (potKernel P x) := by
  obtain ⟨B, hB, hcov⟩ := h.2
  have hfin : ∀ n, potKernel P x (B n) < ∞ := fun n => by
    obtain ⟨hm, M, hM, hle⟩ := hB n
    exact lt_of_le_of_lt (proposition_8_3_1_i P hm hle x)
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hM.lt_top⟩)
  have hspan : ⋃ n, B n = univ := eq_univ_of_univ_subset hcov
  refine ⟨⟨⟨⟨{ set := B, set_mem := fun _ => trivial, finite := hfin, spanning := hspan }⟩⟩,
    isSubinvariant_potKernel P x⟩, fun hinv => ?_⟩
  have hpos : 0 < P x (⋃ n, B n) := by rw [hspan]; simp
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hpos
  have hadd := congrArg (fun m : Measure X => m (B n)) (potKernel_comp_add P x)
  simp only [Measure.add_apply] at hadd
  unfold IsInvariant at hinv
  rw [hinv] at hadd
  have : P x (B n) = 0 := by
    have h' : potKernel P x (B n) + P x (B n) = potKernel P x (B n) + 0 := by
      rw [add_zero]; exact hadd
    exact (ENNReal.add_right_inj (hfin n).ne).1 h'
  exact hn.ne' this

end MeynTweedie.Epilogue
