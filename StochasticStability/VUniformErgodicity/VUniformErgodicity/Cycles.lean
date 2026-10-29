/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.SmallSetExistence
import VUniformErgodicity.Period

/-!
# Cycles for a general state space chain (MT §5.4.3)

Meyn and Tweedie, §5.4.3, pp. 112–115. `ψ` is a maximal irreducibility measure.

* `IsCycle P ψ d D` (Theorem 5.4.4, p. 113): a `d`-cycle, disjoint measurable sets `D i`,
  `i ∈ ZMod d`, with `P(x, D_{i+1}) = 1` on `D_i` and `ψ`-null complement of `⋃ D_i`;
  `IsCycle.pow_apply`: `Pⁿ(x, D_{i+n}) = 1` on `D_i`.
* `smallTimes P C ν = E_C` (5.40), p. 112: the times `n ≥ 1` at which `C` is small with a
  multiple of `ν` as minorizing measure; `smallTimes_isAddClosed` (p. 113) and
  `mem_smallTimes_of_isSmallSet`.
* `IsSmallSet.isPhiIrreducible`: the minorizing measure of a small set in `B⁺(X)` is an
  irreducibility measure (used on p. 114, and Proposition 5.5.4 (ii) for small sets).
* `cycleSet P C d i = D*_i` (p. 113), `iUnion_cycleSet`, and the key estimate
  `measure_cycleSet_inter`: `ψ(D*_i ∩ D*_k) = 0` for `i ≠ k`.
* **Theorem 5.4.4** (`theorem_5_4_4`, p. 113): if `C ∈ B⁺(X)` is `ν_M`-small with `ν(C) > 0` and
  `d = g.c.d. E_C`, there is a `d`-cycle, and every `d'`-cycle has `d' ∣ d`;
  `theorem_5_4_4_unique`: the cycle is unique up to `ψ`-null sets and a relabelling
  `i ↦ k + i`, and every cycle class of a `d'`-cycle contains a cycle class of the `d`-cycle
  up to a `ψ`-null set.
* `exists_isSmallSet_mul_gcd` (p. 113, from Lemma D.7.4): `C` is `δₙν`-small at every large
  multiple of `d`; `exists_class_subset_ae` (p. 114): a small set lies, up to a null set, in one
  class of any cycle.
* `IsPeriod P ψ d` (p. 114): `d` is the largest `d` for which a `d`-cycle exists; `isPeriod_gcd`,
  `IsPeriod.eq_gcd`: the period is `g.c.d. E_C` for every such `C`; `exists_isPeriod`: on a
  countably generated space every `ψ`-irreducible chain has a period; `IsAperiodic`,
  `IsStronglyAperiodic`.
* `smallTimes_smul`: `E_C` does not change when `ν` is scaled; `isPhiIrreducible_of_pow_skeleton`:
  irreducibility of a skeleton passes to the chain;
  `exists_forall_mem_smallTimes_of_aperiodic`: for an aperiodic chain `E_C` contains every
  large time.
* **Proposition 5.4.5** (p. 114): (i) `proposition_5_4_5_i`, a strongly aperiodic chain
  satisfies the minorization condition (5.2); (ii) `proposition_5_4_5_ii`, the resolvent is
  strongly aperiodic; (iii) `proposition_5_4_5_iii`, for an aperiodic chain every skeleton is
  `ψ`-irreducible and aperiodic and some skeleton is strongly aperiodic.
* **Proposition 5.4.6** (`proposition_5_4_6`, p. 115): each cycle class is absorbing and
  `ψ`-irreducible for `Pᵈ`; the aperiodicity of `Pᵈ` on each class is
  `proposition_5_4_6_aperiodic` in `CycleAperiodic`.

**Corrections and hypotheses.** Theorem 5.4.4 as stated takes any `ν_M`-small `C ∈ B⁺(X)`; the
proof needs `ν_M(C) > 0` (assumed "without loss of generality" on p. 112, via Proposition 5.2.4
(iii)), and it is a hypothesis here. In the uniqueness statement the book's "`Dᵢ = D'ᵢ` a.e. after
reordering" is the shift `i ↦ k + i`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Cycles -/

variable (P : Kernel X X) (ψ : Measure X) (d : ℕ) in
/-- A **`d`-cycle** (MT Theorem 5.4.4, p. 113): disjoint measurable sets `D i`, `i ∈ ZMod d`,
with `P(x, D_{i+1}) = 1` for `x ∈ D_i`, whose union has `ψ`-null complement. -/
structure IsCycle (D : ZMod d → Set X) : Prop where
  /-- Each class is measurable. -/
  measurableSet : ∀ i, MeasurableSet (D i)
  /-- The classes are disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j)
  /-- The chain moves from `D i` to `D (i + 1)`. -/
  step : ∀ i, ∀ x ∈ D i, P x (D (i + 1)) = 1
  /-- `N = (⋃ D_i)ᶜ` is `ψ`-null. -/
  null_compl : ψ (⋃ i, D i)ᶜ = 0

/-- On a cycle, `Pⁿ(x, D_{i+n}) = 1` for `x ∈ D_i`. -/
theorem IsCycle.pow_apply {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    {D : ZMod d → Set X} (h : IsCycle P ψ d D) (n : ℕ) {i : ZMod d} {x : X} (hx : x ∈ D i) :
    (P ^ n) x (D (i + n)) = 1 :=
  pow_apply_eq_one_of_step P h.measurableSet h.step n i x hx

/-- On a cycle, `Pⁿ(x, D_j) = 0` for `x ∈ D_i` and `j ≠ i + n`. -/
theorem IsCycle.pow_apply_eq_zero {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    {D : ZMod d → Set X} (h : IsCycle P ψ d D) (n : ℕ) {i j : ZMod d} {x : X} (hx : x ∈ D i)
    (hj : j ≠ i + n) : (P ^ n) x (D j) = 0 := by
  have := isMarkovKernel_pow P n
  have h1 := h.pow_apply n hx
  rw [← prob_compl_eq_zero_iff (h.measurableSet _)] at h1
  exact measure_mono_null (Set.disjoint_left.1 (h.disjoint _ _ hj)) h1

/-! ### The set `E_C` of small times -/

/-- `E_C` (5.40), MT p. 112: the times `n ≥ 1` at which `C` is `δₙν`-small for some `δₙ > 0`. -/
def smallTimes (P : Kernel X X) (C : Set X) (ν : Measure X) : Set ℕ :=
  {n | 0 < n ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ C, δ • ν ≤ (P ^ n) x}

/-- Scalar multiplication of measures is monotone in the scalar. -/
theorem smul_measure_le_smul {a b : ℝ≥0∞} (h : a ≤ b) (μ : Measure X) : a • μ ≤ b • μ :=
  Measure.le_intro fun B _ _ => by
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_left h _

/-- `E_C` is closed under addition when `ν(C) > 0` (MT p. 113):
`P^{n+m}(x, B) ≥ ∫_C Pⁿ(x, dy) Pᵐ(y, B) ≥ δₙ ν(C) δₘ ν(B)`. -/
theorem smallTimes_isAddClosed (P : Kernel X X) {C : Set X} {ν : Measure X} (hνC : 0 < ν C) :
    IsAddClosed (smallTimes P C ν) := by
  rintro n ⟨hn, δn, hδn, hn'⟩ m ⟨hm, δm, hδm, hm'⟩
  refine ⟨Nat.add_pos_left hn m, δn * ν C * δm, ENNReal.mul_pos (ENNReal.mul_pos hδn.ne'
    hνC.ne').ne' hδm.ne', fun x hx => ?_⟩
  have h1 : δn * ν C ≤ (P ^ n) x C := by
    have := hn' x hx C
    rwa [Measure.smul_apply, smul_eq_mul] at this
  calc (δn * ν C * δm) • ν = (δn * ν C) • (δm • ν) := by rw [smul_smul]
    _ ≤ ((P ^ n) x C) • (δm • ν) := smul_measure_le_smul h1 _
    _ ≤ (P ^ (n + m)) x := smul_le_pow_add_of_le P hm' x

/-- The index of a `ν_M`-small set lies in `E_C`. -/
theorem mem_smallTimes_of_isSmallSet {P : Kernel X X} {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) : M ∈ smallTimes P C ν :=
  ⟨hC.2.1, 1, one_pos, fun x hx => by rw [one_smul]; exact hC.2.2.2 x hx⟩

/-- An element of `E_C` makes `C` small. -/
theorem isSmallSet_of_mem_smallTimes {P : Kernel X X} {ν : Measure X} {C : Set X}
    (hCm : MeasurableSet C) (hν : ν ≠ 0) {n : ℕ} (hn : n ∈ smallTimes P C ν) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ IsSmallSet P n (δ • ν) C := by
  obtain ⟨hn0, δ, hδ, h⟩ := hn
  exact ⟨δ, hδ, hCm, hn0, smul_measure_ne_zero hν hδ.ne', h⟩

/-- The minorizing measure of a small set `C` with `φ(C) > 0` is an irreducibility measure
(MT p. 114; Proposition 5.5.4 (ii) for small sets). -/
theorem IsSmallSet.isPhiIrreducible {P : Kernel X X} [IsMarkovKernel P] {M : ℕ} {ν : Measure X}
    {C : Set X} (hC : IsSmallSet P M ν C) {φ : Measure X} (hφ : IsPhiIrreducible P φ)
    (hφC : 0 < φ C) : IsPhiIrreducible P ν := by
  intro B hB hνB x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC.1 x).1 (hφ C hC.1 hφC x)
  have h1 := pow_add_ge_of_le P (m := n + 1) hC.2.2.2 x hB
  have h2 := pow_le_hitProb P hB (n + M) x
  rw [show n + M + 1 = n + 1 + M by omega] at h2
  exact (ENNReal.mul_pos hn.ne' hνB.ne').trans_le (h1.trans h2)

/-- `(∫ c dμ) ρ ≤ μK` when `c(y) ρ ≤ K(y, ·)` for every `y`. -/
theorem smul_le_comp_of_le {Y : Type*} [MeasurableSpace Y] (K : Kernel X Y) (μ : Measure X)
    {ρ : Measure Y} {c : X → ℝ≥0∞} (hc : Measurable c) (h : ∀ y, c y • ρ ≤ K y) :
    (∫⁻ y, c y ∂μ) • ρ ≤ K ∘ₘ μ :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hB K.aemeasurable,
      ← lintegral_mul_const _ hc]
    refine lintegral_mono fun y => ?_
    have := h y B
    rwa [Measure.smul_apply, smul_eq_mul] at this

/-- The estimate of MT p. 113: if `Pᵏ(w, C) ≥ η > 0` on `A` and `∫_C ν(dy) Pʳ(y, A) > 0`, then
`2M + k + r ∈ E_C`, via
`P^{M+r+k+M}(x, B) ≥ ∫_C Pᴹ(x, dy) ∫_A Pʳ(y, dw) ∫_C Pᵏ(w, dz) Pᴹ(z, B)`. -/
theorem mem_smallTimes_of_return {P : Kernel X X} {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) {A : Set X} (hA : MeasurableSet A) {k : ℕ} {η : ℝ≥0∞}
    (hη : 0 < η) (hk : ∀ w ∈ A, η ≤ (P ^ k) w C) {r : ℕ}
    (hr : 0 < ((P ^ r : Kernel X X) ∘ₘ ν.restrict C) A) :
    M + (r + (k + M)) ∈ smallTimes P C ν := by
  have ha : ∀ w ∈ A, η • ν ≤ (P ^ (k + M)) w := fun w hw =>
    (smul_measure_le_smul (hk w hw) ν).trans (smul_le_pow_add_of_le P hC.2.2.2 w)
  have hb : ∀ y, ((P ^ r) y A * η) • ν ≤ (P ^ (r + (k + M))) y := fun y => by
    rw [← smul_smul]
    exact smul_le_pow_add_of_le P (C := A) ha y
  have hcm : Measurable fun y => (P ^ r) y A * η := (Kernel.measurable_coe _ hA).mul_const _
  refine ⟨by have := hC.2.1; omega, ((P ^ r : Kernel X X) ∘ₘ ν.restrict C) A * η,
    ENNReal.mul_pos hr.ne' hη.ne', fun x hx => ?_⟩
  have hval : ((P ^ r : Kernel X X) ∘ₘ ν.restrict C) A * η = ∫⁻ y, (P ^ r) y A * η ∂ν.restrict C :=
    by rw [measure_kernel_apply _ _ hA, lintegral_mul_const _ (Kernel.measurable_coe _ hA)]
  rw [hval, show M + (r + (k + M)) = (r + (k + M)) + M by omega, Kernel.pow_add,
    Kernel.comp_apply]
  calc (∫⁻ y, (P ^ r) y A * η ∂ν.restrict C) • ν ≤ (P ^ (r + (k + M))) ∘ₘ ν.restrict C :=
        smul_le_comp_of_le _ _ hcm hb
    _ ≤ (P ^ (r + (k + M))) ∘ₘ ν := comp_le_comp _ Measure.restrict_le_self
    _ ≤ (P ^ (r + (k + M))) ∘ₘ (P ^ M) x := comp_le_comp _ (hC.2.2.2 x hx)
    _ = ((P ^ M) x).bind ⇑(P ^ (r + (k + M))) := rfl

/-! ### The sets `D*_i` -/

/-- `D*_i = {y : Σ_{k ≥ 1, k + i ≡ 0} Pᵏ(y, C) > 0}` (MT p. 113): the states from which `C` is
reached at times `k ≡ −i (mod d)`. -/
def cycleSet (P : Kernel X X) (C : Set X) (d : ℕ) (i : ZMod d) : Set X :=
  {y | ∃ k : ℕ, 0 < k ∧ (k : ZMod d) + i = 0 ∧ 0 < (P ^ k) y C}

/-- `D*_i` as a countable union. -/
theorem cycleSet_eq_iUnion (P : Kernel X X) (C : Set X) (d : ℕ) (i : ZMod d) :
    cycleSet P C d i = ⋃ k : ℕ, {y | 0 < k ∧ (k : ZMod d) + i = 0 ∧ 0 < (P ^ k) y C} := by
  ext y; simp [cycleSet]

/-- `D*_i` is measurable. -/
theorem measurableSet_cycleSet (P : Kernel X X) {C : Set X} (hC : MeasurableSet C) (d : ℕ)
    (i : ZMod d) : MeasurableSet (cycleSet P C d i) := by
  rw [cycleSet_eq_iUnion]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases h : 0 < k ∧ (k : ZMod d) + i = 0
  · simp only [h.1, h.2, true_and]
    exact measurableSet_lt measurable_const (Kernel.measurable_coe _ hC)
  · have : {y : X | 0 < k ∧ (k : ZMod d) + i = 0 ∧ 0 < (P ^ k) y C} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
    rw [this]
    exact MeasurableSet.empty

/-- By irreducibility, `X = ⋃ D*_i` (MT p. 113). -/
theorem iUnion_cycleSet (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {C : Set X} (hC : MeasurableSet C) (hφC : 0 < φ C) (d : ℕ) :
    ⋃ i, cycleSet P C d i = univ := by
  refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC y).1 (hφ C hC hφC y)
  exact ⟨-((n + 1 : ℕ) : ZMod d), n + 1, by omega, by ring, hn⟩

/-- **The key estimate of Theorem 5.4.4** (MT pp. 113–114): `ψ(D*_i ∩ D*_k) = 0` for `i ≠ k`,
where `d = g.c.d. E_C`. -/
theorem measure_cycleSet_inter (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {M : ℕ} {ν : Measure X} {C : Set X} (hC : IsSmallSet P M ν C)
    (hνC : 0 < ν C) {d : ℕ} (hd : d = setGcd (smallTimes P C ν)) {i j : ZMod d} (hij : i ≠ j) :
    ψ (cycleSet P C d i ∩ cycleSet P C d j) = 0 := by
  by_contra hne
  have hpos := pos_iff_ne_zero.2 hne
  set A : ℕ → ℕ → ℕ → Set X := fun k l q => {w | (0 < k ∧ (k : ZMod d) + i = 0) ∧
    (0 < l ∧ (l : ZMod d) + j = 0) ∧ ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ k) w C ∧
      ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ l) w C} with hAdef
  have hsub : cycleSet P C d i ∩ cycleSet P C d j ⊆ ⋃ k, ⋃ l, ⋃ q, A k l q := by
    rintro w ⟨⟨k, hk0, hki, hk⟩, ⟨l, hl0, hlj, hl⟩⟩
    obtain ⟨q₁, hq₁⟩ := ENNReal.exists_inv_nat_lt hk.ne'
    obtain ⟨q₂, hq₂⟩ := ENNReal.exists_inv_nat_lt hl.ne'
    refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨l, mem_iUnion.2 ⟨max q₁ q₂, ⟨hk0, hki⟩, ⟨hl0, hlj⟩,
      le_trans ?_ hq₁.le, le_trans ?_ hq₂.le⟩⟩⟩
    · gcongr
      exact (Nat.cast_le.2 (le_max_left q₁ q₂)).trans le_self_add
    · gcongr
      exact (Nat.cast_le.2 (le_max_right q₁ q₂)).trans le_self_add
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hsub))
  obtain ⟨l, hl⟩ := exists_measure_pos_of_iUnion hk
  obtain ⟨q, hq⟩ := exists_measure_pos_of_iUnion hl
  obtain ⟨w₀, ⟨hk0, hki⟩, ⟨hl0, hlj⟩, -, -⟩ := nonempty_of_measure_ne_zero hq.ne'
  have hAm : MeasurableSet (A k l q) := by
    have : A k l q = {w | ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ k) w C ∧
        ((q : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ l) w C} := by
      ext w; simp [hAdef, hk0, hki, hl0, hlj]
    rw [this]
    exact (measurableSet_le measurable_const (Kernel.measurable_coe _ hC.1)).inter
      (measurableSet_le measurable_const (Kernel.measurable_coe _ hC.1))
  have hη : 0 < ((q : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
  have hρ : ν.restrict C ≠ 0 := by rw [Ne, Measure.restrict_eq_zero]; exact hνC.ne'
  obtain ⟨r, hr⟩ := exists_pow_comp_pos hψ hρ hAm hq
  have h1 := mem_smallTimes_of_return hC hAm (k := k) hη (fun w hw => hw.2.2.1) hr
  have h2 := mem_smallTimes_of_return hC hAm (k := l) hη (fun w hw => hw.2.2.2) hr
  have hS := smallTimes_isAddClosed P hνC
  have hMmem := mem_smallTimes_of_isSmallSet hC
  have e1 := (ZMod.natCast_eq_zero_iff _ d).2 (hd ▸ setGcd_dvd hS hMmem hC.2.1 h1)
  have e2 := (ZMod.natCast_eq_zero_iff _ d).2 (hd ▸ setGcd_dvd hS hMmem hC.2.1 h2)
  push_cast at e1 e2
  exact hij (by linear_combination hki - hlj - e1 + e2)

/-! ### Theorem 5.4.4 -/

/-- **Theorem 5.4.4**, existence (MT p. 113): with `d = g.c.d. E_C`, the sets
`D_i = D ∩ D*_i`, for an absorbing full set `D` avoiding `⋃_{i ≠ k} D*_i ∩ D*_k`, form a
`d`-cycle. -/
theorem exists_isCycle_gcd (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    ∃ D : ZMod (setGcd (smallTimes P C ν)) → Set X,
      IsCycle P ψ (setGcd (smallTimes P C ν)) D ∧
        ∀ i, D i ⊆ cycleSet P C (setGcd (smallTimes P C ν)) i := by
  set d := setGcd (smallTimes P C ν) with hd
  have hd0 : 0 < d := setGcd_pos (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  have : NeZero d := ⟨hd0.ne'⟩
  have hDs := measurableSet_cycleSet P hC.1 d
  set N : Set X := ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), cycleSet P C d i ∩ cycleSet P C d j with hNdef
  have hNm : MeasurableSet N := MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => (hDs i).inter (hDs j)
  have hN : ψ N = 0 := measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => measure_cycleSet_inter P hψ.2.1 hC hνC hd hij
  have hfull : IsFull ψ Nᶜ := by rw [IsFull, compl_compl]; exact hN
  obtain ⟨D, hDsub, -, hDm, hDabs, hDfull⟩ := proposition_4_2_3_ii hψ hNm.compl hfull
  have hcov := iUnion_cycleSet P hψ.2.1 hC.1 hψC d
  have hnotN : ∀ x ∈ D, ∀ i j, x ∈ cycleSet P C d i → x ∈ cycleSet P C d j → i = j :=
    fun x hx i j hi hj => by
      by_contra hij
      exact hDsub hx (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hij, hi, hj⟩⟩⟩)
  refine ⟨fun i => D ∩ cycleSet P C d i, ⟨fun i => hDm.inter (hDs i), fun i j hij =>
    Set.disjoint_left.2 fun x hi hj => hij (hnotN x hi.1 i j hi.2 hj.2), fun i x hx => ?_, ?_⟩,
    fun i => inter_subset_right⟩
  · -- the chain moves from `D_i` to `D_{i+1}`
    have hzero : ∀ j, j ≠ i + 1 → P x (D ∩ cycleSet P C d j) = 0 := fun j hj => by
      by_contra hne
      have hsub : D ∩ cycleSet P C d j ⊆
          ⋃ k : ℕ, {y | 0 < k ∧ (k : ZMod d) + j = 0 ∧ 0 < (P ^ k) y C} :=
        fun y hy => by rw [← cycleSet_eq_iUnion]; exact hy.2
      obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion
        ((pos_iff_ne_zero.2 hne).trans_le (measure_mono hsub))
      obtain ⟨y, hk0, hkj, -⟩ := nonempty_of_measure_ne_zero hk.ne'
      have hreach : 0 < (P ^ (1 + k)) x C := by
        rw [pow_add_pos_iff P 1 k x hC.1, pow_one]
        exact hk.trans_le (measure_mono fun y hy => hy.2.2)
      have hx' : x ∈ cycleSet P C d (j - 1) :=
        ⟨1 + k, by omega, by push_cast; linear_combination hkj, hreach⟩
      exact hj (by linear_combination (hnotN x hx.1 i (j - 1) hx.2 hx').symm)
    have hD1 : P x D = 1 := hDabs x hx.1
    have hcover : D ⊆ (D ∩ cycleSet P C d (i + 1)) ∪
        ⋃ j, ⋃ (_ : j ≠ i + 1), D ∩ cycleSet P C d j := fun y hy => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov ▸ mem_univ y : y ∈ ⋃ i, cycleSet P C d i)
      by_cases hji : j = i + 1
      · exact Or.inl ⟨hy, hji ▸ hj⟩
      · exact Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hji, hy, hj⟩⟩)
    have hnull : P x (⋃ j, ⋃ (_ : j ≠ i + 1), D ∩ cycleSet P C d j) = 0 :=
      measure_iUnion_null fun j => measure_iUnion_null fun hj => hzero j hj
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = P x D := hD1.symm
      _ ≤ P x (D ∩ cycleSet P C d (i + 1)) + P x (⋃ j, ⋃ (_ : j ≠ i + 1),
          D ∩ cycleSet P C d j) := (measure_mono hcover).trans (measure_union_le _ _)
      _ = P x (D ∩ cycleSet P C d (i + 1)) := by rw [hnull, add_zero]
  · -- the complement of the union is `ψ`-null
    refine measure_mono_null (compl_subset_compl.2 fun y hy => ?_) hDfull
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov ▸ mem_univ y : y ∈ ⋃ i, cycleSet P C d i)
    exact mem_iUnion.2 ⟨j, hy, hj⟩

/-- A positive mass on a countable union sits on one of the sets (any countable index). -/
theorem exists_measure_pos_of_iUnion' {ι : Type*} [Countable ι] {μ : Measure X} {s : ι → Set X}
    (h : 0 < μ (⋃ i, s i)) : ∃ i, 0 < μ (s i) := by
  by_contra hc
  push Not at hc
  rw [measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (hc i)] at h
  exact lt_irrefl _ h

/-- For any `d'`-cycle there is a class `D'_k` charged by `ν`, and a state of `C ∩ D'_j` is in
`D'_k` after `n ∈ E_C` steps: `j + n = k` (MT p. 114). -/
theorem exists_class_of_isCycle (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {d' : ℕ} (hd' : 0 < d')
    {D' : ZMod d' → Set X} (h : IsCycle P ψ d' D') :
    ∃ k : ZMod d', ∀ n ∈ smallTimes P C ν, ∀ j, ∀ x ∈ C ∩ D' j, j + n = k := by
  have : NeZero d' := ⟨hd'.ne'⟩
  have hνψ : ν ≪ ψ := hψ.2.2 ν (hC.isPhiIrreducible hψ.2.1 hψC)
  have hνN : ν (⋃ j, D' j)ᶜ = 0 := hνψ h.null_compl
  have hcov : C ⊆ (⋃ j, D' j ∩ C) ∪ (⋃ j, D' j)ᶜ := fun x hx => by
    by_cases hU : x ∈ ⋃ j, D' j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hU
      exact Or.inl (mem_iUnion.2 ⟨j, hj, hx⟩)
    · exact Or.inr hU
  have hU : 0 < ν (⋃ j, D' j ∩ C) := by
    have := hνC.trans_le ((measure_mono hcov).trans (measure_union_le _ _))
    rwa [hνN, add_zero] at this
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion' hU
  refine ⟨k, fun n hn j x hx => ?_⟩
  obtain ⟨-, δ, hδ, hδn⟩ := hn
  have hpos : 0 < (P ^ n) x (D' k) := by
    have h1 := hδn x hx.1 (D' k ∩ C)
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact (ENNReal.mul_pos hδ.ne' hk.ne').trans_le (h1.trans (measure_mono inter_subset_left))
  by_contra hne
  exact hpos.ne' (h.pow_apply_eq_zero n hx.2 (Ne.symm hne))

/-- **Theorem 5.4.4**, maximality (MT p. 114): for every `d'`-cycle, `d'` divides
`d = g.c.d. E_C`. -/
theorem dvd_gcd_of_isCycle (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {d' : ℕ} (hd' : 0 < d')
    {D' : ZMod d' → Set X} (h : IsCycle P ψ d' D') : d' ∣ setGcd (smallTimes P C ν) := by
  have : NeZero d' := ⟨hd'.ne'⟩
  obtain ⟨k, hk⟩ := exists_class_of_isCycle P hψ hC hψC hνC hd' h
  -- a state of `C` in one of the classes
  have hψU : 0 < ψ (C ∩ ⋃ j, D' j) := by
    have hle : ψ C ≤ ψ (C ∩ ⋃ j, D' j) + ψ (⋃ j, D' j)ᶜ := by
      rw [← measure_inter_add_sdiff C (MeasurableSet.iUnion h.measurableSet), sdiff_eq]
      gcongr
      exact inter_subset_right
    rw [h.null_compl, add_zero] at hle
    exact hψC.trans_le hle
  obtain ⟨x, hxC, hxU⟩ := nonempty_of_measure_ne_zero hψU.ne'
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxU
  have hS := smallTimes_isAddClosed P hνC
  have hMmem := mem_smallTimes_of_isSmallSet hC
  refine dvd_setGcd hS hMmem hC.2.1 fun n hn => ?_
  have e1 := hk n hn j x ⟨hxC, hj⟩
  have e2 := hk (n + n) (hS n hn n hn) j x ⟨hxC, hj⟩
  refine (ZMod.natCast_eq_zero_iff n d').1 ?_
  push_cast at e2
  linear_combination e2 - e1

/-- **Theorem 5.4.4**, comparison of cycles (MT p. 114). Let `D` be a `d`-cycle with
`D_i ⊆ D*_i`, `d = g.c.d. E_C`, as constructed in `exists_isCycle_gcd`, and `D'` a `d'`-cycle,
so that `d' ∣ d`. Then for some `k`, every `D_i` lies in `D'_{k + i}` up to a `ψ`-null set: each
`D'_j` is, up to null sets, a union of classes of `D`. -/
theorem isCycle_subset_ae (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C)
    {D : ZMod (setGcd (smallTimes P C ν)) → Set X}
    (hDsub : ∀ i, D i ⊆ cycleSet P C (setGcd (smallTimes P C ν)) i)
    {d' : ℕ} (hd' : 0 < d') {D' : ZMod d' → Set X} (h : IsCycle P ψ d' D') :
    ∃ k : ZMod d', ∀ i, ψ (D i \ D' (k + ZMod.castHom
      (dvd_gcd_of_isCycle P hψ hC hψC hνC hd' h) (ZMod d') i)) = 0 := by
  have : NeZero d' := ⟨hd'.ne'⟩
  have hdvd := dvd_gcd_of_isCycle P hψ hC hψC hνC hd' h
  obtain ⟨k, hk⟩ := exists_class_of_isCycle P hψ hC hψC hνC hd' h
  have hMmem := mem_smallTimes_of_isSmallSet hC
  -- states of `C` lie in `D'_k`
  have hCk : ∀ j, ∀ x ∈ C ∩ D' j, j = k := fun j x hx => by
    have e := hk M hMmem j x hx
    have hM0 : (M : ZMod d') = 0 := (ZMod.natCast_eq_zero_iff M d').2 (hdvd.trans
      (setGcd_dvd (smallTimes_isAddClosed P hνC) hMmem hC.2.1 hMmem))
    rw [hM0, add_zero] at e
    exact e
  refine ⟨k, fun i => measure_mono_null (fun y hy => ?_) h.null_compl⟩
  intro hyU
  obtain ⟨j, hj⟩ := mem_iUnion.1 hyU
  obtain ⟨n, hn0, hni, hn⟩ := hDsub i hy.1
  -- `Pⁿ(y, C ∩ D'_{j+n}) > 0`, so `j + n = k`
  have := isMarkovKernel_pow P n
  have h1 := h.pow_apply n hj
  rw [← prob_compl_eq_zero_iff (h.measurableSet _)] at h1
  have hpos : 0 < (P ^ n) y (C ∩ D' (j + n)) := by
    have hle : (P ^ n) y C ≤ (P ^ n) y (C ∩ D' (j + n)) + (P ^ n) y (D' (j + n))ᶜ := by
      rw [← measure_inter_add_sdiff C (h.measurableSet (j + n)), sdiff_eq]
      gcongr
      exact inter_subset_right
    rw [h1, add_zero] at hle
    exact hn.trans_le hle
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hjn := hCk (j + n) x hx
  have hcast := congrArg (ZMod.castHom hdvd (ZMod d')) hni
  rw [map_add, map_natCast, map_zero] at hcast
  refine hy.2 ?_
  have : j = k + ZMod.castHom hdvd (ZMod d') i := by linear_combination hjn - hcast
  rw [← this]
  exact hj

/-- **Theorem 5.4.4**, uniqueness (MT p. 114): any two `d`-cycles, `d = g.c.d. E_C`, agree up to
`ψ`-null sets after a relabelling `i ↦ k + i`. -/
theorem theorem_5_4_4_unique (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C)
    {D D' : ZMod (setGcd (smallTimes P C ν)) → Set X}
    (hD : IsCycle P ψ (setGcd (smallTimes P C ν)) D)
    (hD' : IsCycle P ψ (setGcd (smallTimes P C ν)) D') :
    ∃ k, ∀ i, ψ (symmDiff (D i) (D' (k + i))) = 0 := by
  have hd0 : 0 < setGcd (smallTimes P C ν) := setGcd_pos (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  have : NeZero (setGcd (smallTimes P C ν)) := ⟨hd0.ne'⟩
  obtain ⟨D₀, hD₀, hD₀sub⟩ := exists_isCycle_gcd P hψ hC hψC hνC
  -- comparison of a `d`-cycle with the constructed one
  have hcomp : ∀ E : ZMod (setGcd (smallTimes P C ν)) → Set X,
      IsCycle P ψ (setGcd (smallTimes P C ν)) E →
      ∃ k, ∀ i, ψ (symmDiff (D₀ i) (E (k + i))) = 0 := fun E hE => by
    obtain ⟨k, hk⟩ := isCycle_subset_ae P hψ hC hψC hνC hD₀sub hd0 hE
    simp only [ZMod.castHom_apply, ZMod.cast_id] at hk
    refine ⟨k, fun i => ?_⟩
    have h2 : ψ (E (k + i) \ D₀ i) = 0 := by
      have hsub : E (k + i) \ D₀ i ⊆ (⋃ i', D₀ i')ᶜ ∪
          ⋃ i', ⋃ (_ : i' ≠ i), D₀ i' \ E (k + i') := fun y hy => by
        by_cases hU : y ∈ ⋃ i', D₀ i'
        · obtain ⟨i', hi'⟩ := mem_iUnion.1 hU
          have hne : i' ≠ i := fun h => hy.2 (h ▸ hi')
          refine Or.inr (mem_iUnion.2 ⟨i', mem_iUnion.2 ⟨hne, hi', fun hE' => ?_⟩⟩)
          exact Set.disjoint_left.1 (hE.disjoint (k + i') (k + i)
            (fun h => hne (add_left_cancel h))) hE' hy.1
        · exact Or.inl hU
      refine measure_mono_null hsub (measure_union_null hD₀.null_compl ?_)
      exact measure_iUnion_null fun i' => measure_iUnion_null fun _ => hk i'
    exact measure_union_null (hk i) h2
  obtain ⟨k₁, hk₁⟩ := hcomp D hD
  obtain ⟨k₂, hk₂⟩ := hcomp D' hD'
  refine ⟨k₂ - k₁, fun i => ?_⟩
  have h1 := hk₁ (i - k₁)
  have h2 := hk₂ (i - k₁)
  rw [add_sub_cancel] at h1
  rw [show k₂ + (i - k₁) = k₂ - k₁ + i by ring] at h2
  refine measure_mono_null ((symmDiff_triangle (D i) (D₀ (i - k₁)) (D' (k₂ - k₁ + i))).trans
    (sup_le_sup (le_of_eq (symmDiff_comm _ _)) le_rfl)) ?_
  exact measure_union_null h1 h2

/-- **Theorem 5.4.4** (MT p. 113). Let `ψ` be a maximal irreducibility measure, `C ∈ B⁺(X)` a
`ν_M`-small set with `ν_M(C) > 0`, and `d = g.c.d. E_C`. (i)–(ii) There is a `d`-cycle.
Maximality: every `d'`-cycle has `d' ∣ d`; and any two `d`-cycles agree up to `ψ`-null sets after
relabelling. -/
theorem theorem_5_4_4 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    (∃ D, IsCycle P ψ (setGcd (smallTimes P C ν)) D) ∧
      (∀ d' (D' : ZMod d' → Set X), 0 < d' → IsCycle P ψ d' D' →
        d' ∣ setGcd (smallTimes P C ν)) ∧
      ∀ D D' : ZMod (setGcd (smallTimes P C ν)) → Set X,
        IsCycle P ψ (setGcd (smallTimes P C ν)) D →
        IsCycle P ψ (setGcd (smallTimes P C ν)) D' →
        ∃ k, ∀ i, ψ (symmDiff (D i) (D' (k + i))) = 0 := by
  obtain ⟨D, hD, -⟩ := exists_isCycle_gcd P hψ hC hψC hνC
  exact ⟨⟨D, hD⟩, fun d' D' hd' h => dvd_gcd_of_isCycle P hψ hC hψC hνC hd' h,
    fun D D' hD hD' => theorem_5_4_4_unique P hψ hC hψC hνC hD hD'⟩

/-- MT p. 113, from Lemma D.7.4: `C` is `δₙν`-small at every large multiple `nd` of
`d = g.c.d. E_C`. -/
theorem exists_isSmallSet_mul_gcd {P : Kernel X X} {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hνC : 0 < ν C) :
    ∃ N, ∀ n ≥ N, ∃ δ : ℝ≥0∞, 0 < δ ∧
      IsSmallSet P (n * setGcd (smallTimes P C ν)) (δ • ν) C := by
  obtain ⟨N, hN⟩ := lemma_D_7_4 (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  exact ⟨N, fun n hn => isSmallSet_of_mem_smallTimes hC.1 hC.2.2.1 (hN n hn)⟩

/-- MT p. 114: a small set `C ∈ B⁺(X)` with `ν(C) > 0` lies, up to a `ψ`-null set, inside one
class of any `d`-cycle. -/
theorem exists_class_subset_ae (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {d : ℕ} (hd : 0 < d)
    {D : ZMod d → Set X} (h : IsCycle P ψ d D) : ∃ k, ψ (C \ D k) = 0 := by
  obtain ⟨k, hk⟩ := exists_class_of_isCycle P hψ hC hψC hνC hd h
  refine ⟨k - M, measure_mono_null (fun x hx => ?_) h.null_compl⟩
  intro hU
  obtain ⟨j, hj⟩ := mem_iUnion.1 hU
  have e := hk M (mem_smallTimes_of_isSmallSet hC) j x ⟨hx.1, hj⟩
  exact hx.2 (by rwa [show k - M = j by linear_combination -e])

/-! ### The period -/

/-- `d` is the **period** of the chain (MT p. 114): a `d`-cycle exists, and `d' ≤ d` for every
`d'`-cycle. -/
def IsPeriod (P : Kernel X X) (ψ : Measure X) (d : ℕ) : Prop :=
  0 < d ∧ (∃ D, IsCycle P ψ d D) ∧ ∀ d' (D' : ZMod d' → Set X), 0 < d' → IsCycle P ψ d' D' → d' ≤ d

/-- The chain is **aperiodic** (MT p. 114) if its period is `1`. -/
def IsAperiodic (P : Kernel X X) (ψ : Measure X) : Prop := IsPeriod P ψ 1

/-- The chain is **strongly aperiodic** (MT p. 114) if there is a `ν₁`-small set `A` with
`ν₁(A) > 0`. -/
def IsStronglyAperiodic (P : Kernel X X) : Prop := ∃ ν A, IsSmallSet P 1 ν A ∧ 0 < ν A

/-- The period is unique. -/
theorem IsPeriod.unique {P : Kernel X X} {ψ : Measure X} {d d' : ℕ} (h : IsPeriod P ψ d)
    (h' : IsPeriod P ψ d') : d = d' := by
  obtain ⟨hd0, ⟨D, hD⟩, hmax⟩ := h
  obtain ⟨hd0', ⟨D', hD'⟩, hmax'⟩ := h'
  exact le_antisymm (hmax' d D hd0 hD) (hmax d' D' hd0' hD')

/-- By Theorem 5.4.4, `g.c.d. E_C` is the period, for every `ν`-small `C ∈ B⁺(X)` with
`ν(C) > 0` (MT p. 114: the cycle does not depend on the small set chosen). -/
theorem isPeriod_gcd (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    IsPeriod P ψ (setGcd (smallTimes P C ν)) := by
  obtain ⟨h1, h2, -⟩ := theorem_5_4_4 P hψ hC hψC hνC
  have hd0 : 0 < setGcd (smallTimes P C ν) := setGcd_pos (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  exact ⟨hd0, h1, fun d' D' hd' h => Nat.le_of_dvd hd0 (h2 d' D' hd' h)⟩

/-- The period equals `g.c.d. E_C` for every such `C`. -/
theorem IsPeriod.eq_gcd {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    (h : IsPeriod P ψ d) (hψ : IsMaximalIrreducibility P ψ) {M : ℕ} {ν : Measure X} {C : Set X}
    (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    d = setGcd (smallTimes P C ν) :=
  h.unique (isPeriod_gcd P hψ hC hψC hνC)

/-- On a countably generated space, every `ψ`-irreducible chain has a period. -/
theorem exists_isPeriod [MeasurableSpace.CountablyGenerated X] (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) : ∃ d, IsPeriod P ψ d := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  exact ⟨_, isPeriod_gcd P hψ hC hψC hνC⟩

/-- `E_C` does not change when `ν` is multiplied by a constant `0 < c < ∞`. -/
theorem smallTimes_smul (P : Kernel X X) (C : Set X) (ν : Measure X) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ∞) : smallTimes P C (c • ν) = smallTimes P C ν := by
  ext n
  constructor
  · rintro ⟨hn, δ, hδ, h⟩
    refine ⟨hn, δ * c, ENNReal.mul_pos hδ.ne' hc0, fun x hx => ?_⟩
    rw [← smul_smul]; exact h x hx
  · rintro ⟨hn, δ, hδ, h⟩
    refine ⟨hn, δ * c⁻¹, ENNReal.mul_pos hδ.ne' (ENNReal.inv_ne_zero.2 hct), fun x hx => ?_⟩
    rw [smul_smul, mul_assoc, ENNReal.inv_mul_cancel hc0 hct, mul_one]
    exact h x hx

/-- Irreducibility of a skeleton `Pᵐ`, `m ≥ 1`, gives irreducibility of `P`. -/
theorem isPhiIrreducible_of_pow_skeleton (P : Kernel X X) [IsMarkovKernel P] {m : ℕ}
    (hm : 1 ≤ m) {φ : Measure X}
    (h : haveI := isMarkovKernel_pow P m; IsPhiIrreducible (P ^ m) φ) : IsPhiIrreducible P φ := by
  have := isMarkovKernel_pow P m
  intro A hA hpos x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff (P ^ m) hA x).1 (h A hA hpos x)
  refine (hitProb_pos_iff P hA x).2 ⟨m * (n + 1) - 1, ?_⟩
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity)), pow_mul]
  exact hn

/-- **Proposition 5.4.5 (i)** (MT p. 114): a strongly aperiodic chain satisfies the
minorization condition (5.2), with the book's normalisation `ν(Cᶜ) = 0`. -/
theorem proposition_5_4_5_i (P : Kernel X X) [IsMarkovKernel P] (h : IsStronglyAperiodic P) :
    ∃ M : Minorization P, M.IsConcentrated := by
  obtain ⟨ν, A, hA, hνA⟩ := h
  have hle : ∀ x ∈ A, ν ≤ P x := fun x hx => by
    have := hA.2.2.2 x hx
    rwa [pow_one] at this
  have hfin : ν A ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hνA.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx A).trans prob_le_one)
  exact ⟨Minorization.ofLe hA.1 hle hνA hfin, Minorization.ofLe_isConcentrated _ _ _ _⟩

/-- **Proposition 5.4.5 (ii)** (MT p. 114): on a countably generated space the resolvent
`K_{a_ε}`, `0 < ε < 1`, of a `ψ`-irreducible chain is strongly aperiodic. -/
theorem proposition_5_4_5_ii [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {ε : ℝ≥0∞}
    (hε0 : 0 < ε) (hε1 : ε < 1) : IsStronglyAperiodic (resolvent P ε) := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, -, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hc : 0 < (1 - ε) * ε ^ m :=
    ENNReal.mul_pos (tsub_pos_of_lt hε1).ne' (pow_ne_zero _ hε0.ne')
  refine ⟨((1 - ε) * ε ^ m) • ν, C, ⟨hC.1, one_pos, smul_measure_ne_zero hC.2.2.1 hc.ne',
    fun x hx => ?_⟩, ?_⟩
  · rw [pow_one]
    exact (smul_measure_le_smul le_rfl _).trans (le_trans (Measure.le_intro fun B _ _ => by
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      gcongr
      exact hC.2.2.2 x hx) (smul_pow_le_resolvent P ε m x))
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc.ne' hνC.ne'

/-- For an aperiodic chain, `E_C` contains every large time. -/
theorem exists_forall_mem_smallTimes_of_aperiodic (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {M : ℕ}
    {ν : Measure X} {C : Set X} (hC : IsSmallSet P M ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) :
    ∃ N, ∀ n ≥ N, n ∈ smallTimes P C ν := by
  have h1 : setGcd (smallTimes P C ν) = 1 := (hap.eq_gcd hψ hC hψC hνC).symm
  obtain ⟨N, hN⟩ := lemma_D_7_4 (smallTimes_isAddClosed P hνC)
    (mem_smallTimes_of_isSmallSet hC) hC.2.1
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rwa [h1, mul_one] at this

/-- **Proposition 5.4.5 (iii)** (MT p. 114). On a countably generated space, if a `ψ`-irreducible
chain is aperiodic, then every skeleton `Pᵐ`, `m ≥ 1`, is `ψ`-irreducible (with `ψ` maximal) and
aperiodic, and some skeleton is strongly aperiodic. -/
theorem proposition_5_4_5_iii [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    (hap : IsAperiodic P ψ) :
    (∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
      IsMaximalIrreducibility (P ^ m) ψ ∧ IsAperiodic (P ^ m) ψ) ∧
      ∃ m, 1 ≤ m ∧ IsStronglyAperiodic (P ^ m) := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  refine ⟨fun m hm => ?_, ?_⟩
  · have := isMarkovKernel_pow P m
    -- irreducibility of the skeleton
    have hirr : IsPhiIrreducible (P ^ m) ψ := by
      intro A hA hpos x
      obtain ⟨j, hj⟩ := (hitProb_pos_iff P hC.1 x).1 (hψ.2.1 C hC.1 hψC x)
      obtain ⟨r, hr⟩ := exists_pow_comp_pos hψ.2.1 hC.2.2.1 hA hpos
      set q := N + (j + 1) + (r + 1) with hq
      have hn : m * q - (j + 1) - (r + 1) ≥ N := by
        have : q ≤ m * q := Nat.le_mul_of_pos_left q hm
        omega
      obtain ⟨-, δ, hδ, hδn⟩ := hN _ hn
      set n := m * q - (j + 1) - (r + 1)
      have hν' : ∀ y ∈ C, δ • ((P ^ (r + 1) : Kernel X X) ∘ₘ ν) ≤ (P ^ (n + (r + 1))) y :=
        fun y hy => by
          rw [show n + (r + 1) = (r + 1) + n by omega, Kernel.pow_add P (r + 1) n,
            Kernel.comp_apply,
            ← Measure.comp_smul]
          exact comp_le_comp _ (hδn y hy)
      have h1 := pow_add_ge_of_le P (m := j + 1) hν' x hA
      have heq : j + 1 + (n + (r + 1)) = m * q := by
        have : q ≤ m * q := Nat.le_mul_of_pos_left q hm
        omega
      rw [heq, Measure.smul_apply, smul_eq_mul] at h1
      have hpos' : 0 < ((P ^ m) ^ q) x A := by
        rw [← pow_mul]
        exact (ENNReal.mul_pos hj.ne' (ENNReal.mul_pos hδ.ne' hr.ne').ne').trans_le h1
      refine (hitProb_pos_iff (P ^ m) hA x).2 ⟨q - 1, ?_⟩
      rwa [Nat.sub_add_cancel (by omega)]
    have hmax : IsMaximalIrreducibility (P ^ m) ψ :=
      ⟨hψ.1, hirr, fun φ hφ => hψ.2.2 φ (isPhiIrreducible_of_pow_skeleton P hm hφ)⟩
    refine ⟨hmax, ?_⟩
    -- aperiodicity of the skeleton
    obtain ⟨-, δ, hδ, hδn⟩ := hN (m * (N + 1)) (by nlinarith)
    have hCm : IsSmallSet (P ^ m) (N + 1) (δ • ν) C :=
      ⟨hC.1, by omega, smul_measure_ne_zero hC.2.2.1 hδ.ne', fun x hx => by
        rw [← pow_mul]; exact hδn x hx⟩
    have hδC : 0 < (δ • ν) C := by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ.ne' hνC.ne'
    have hδt : δ ≠ ∞ := by
      have := isMarkovKernel_pow P (m * (N + 1))
      intro htop
      obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
      have := (hδn x hx C).trans prob_le_one
      rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.top_mul hνC.ne'] at this
      exact absurd this (by simp)
    have hper := isPeriod_gcd (P ^ m) hmax hCm hψC hδC
    rw [smallTimes_smul _ _ _ hδ.ne' hδt] at hper
    -- every `t ≥ N + 1` lies in `E_C` for the skeleton
    have hmem : ∀ t, N ≤ t → t + 1 ∈ smallTimes (P ^ m) C ν := fun t ht => by
      obtain ⟨-, δ', hδ', h'⟩ := hN (m * (t + 1)) (by nlinarith)
      exact ⟨by omega, δ', hδ', fun x hx => by rw [← pow_mul]; exact h' x hx⟩
    have hS := smallTimes_isAddClosed (P ^ m) hνC
    have h1 := setGcd_dvd hS (hmem N le_rfl) (by omega) (hmem N le_rfl)
    have h2 := setGcd_dvd hS (hmem N le_rfl) (by omega) (hmem (N + 1) (by omega))
    have hg : setGcd (smallTimes (P ^ m) C ν) = 1 :=
      Nat.dvd_one.1 (by simpa using (Nat.dvd_sub h2 h1))
    rwa [hg] at hper
  · obtain ⟨-, δ, hδ, hδn⟩ := hN (N + 1) (by omega)
    refine ⟨N + 1, by omega, δ • ν, C, ⟨hC.1, one_pos, smul_measure_ne_zero hC.2.2.1 hδ.ne',
      fun x hx => by rw [pow_one]; exact hδn x hx⟩, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ.ne' hνC.ne'

/-- **Proposition 5.4.6** (MT p. 115): for a `d`-cycle, each `D_i` is an absorbing
`ψ`-irreducible set for the chain `Φ_d` with kernel `Pᵈ` (with irreducibility measure `ψ`
restricted to `D_i`). -/
theorem proposition_5_4_6 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {d : ℕ} {D : ZMod d → Set X}
    (h : IsCycle P ψ d D) (i : ZMod d) :
    haveI := isMarkovKernel_pow P d
    IsAbsorbingIrreducibleSet (P ^ d) (ψ.restrict (D i)) (D i) := by
  have := isMarkovKernel_pow P d
  refine ⟨fun x hx => ?_, fun B hB hpos x hx => ?_⟩
  · have := h.pow_apply d hx
    rwa [ZMod.natCast_self, add_zero] at this
  · rw [Measure.restrict_apply hB] at hpos
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P (hB.inter (h.measurableSet i)) x).1
      (hψ _ (hB.inter (h.measurableSet i)) hpos x)
    have hcast : ((n + 1 : ℕ) : ZMod d) = 0 := by
      by_contra hne
      have h0 := h.pow_apply_eq_zero (n + 1) hx (j := i) (by
        intro hc
        exact hne (by linear_combination -hc))
      exact hn.ne' (measure_mono_null inter_subset_right h0)
    obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ d).1 hcast
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq; omega
    refine (hitProb_pos_iff (P ^ d) hB x).2 ⟨q - 1, ?_⟩
    rw [Nat.sub_add_cancel hq0, ← pow_mul, ← hq]
    exact hn.trans_le (measure_mono inter_subset_left)

end MeynTweedie.VUniformErgodicity
