/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.SampledChains
import Ergodicity.CycleAperiodic

/-!
# Uniform transience and recurrence of sets (MT §8.0, §8.2.1, §8.3.1)

Meyn and Tweedie, Chapter 8, pp. 171–185.

**Definitions** (pp. 171, 180).
* `IsUniformlyTransient P A`: `A` is measurable and `E_x[η_A] = U(x, A) ≤ M < ∞` for `x ∈ A`.
* `IsRecurrentSet P A`: `U(x, A) = ∞` for every `x ∈ A`.
* `IsTransientSet P A`: `A` is covered by countably many uniformly transient sets.
* `IsRecurrentChain P ψ` (p. 180): `ψ` is a maximal irreducibility measure and `U(x, A) = ∞` for
  every `x` and every `A ∈ B⁺(X)`; `IsTransientChain P ψ`: `ψ` is maximal and `X` is transient.

**Occupation times and the first-entrance equation.**
* `occTime_of_firstReturn_eq`: on `{τ_A = m}`, `η_A = 1 + η_A ∘ θᵐ`; `occTimeN` is the truncated
  occupation time `Σ_{n=1}^N 1_A(Φₙ)`, with `lintegral_occTimeN` (`E_x[η_A^N] = Σ_{n ≤ N} Pⁿ(x, A)`)
  and `iSup_lintegral_occTimeN` (`sup_N E_x[η_A^N] = U(x, A)`).
* `potKernel_eq_firstReturn`: the **first-entrance equation** for `U` (the limit `z ↑ 1` of
  (8.25) with `A = B`), `U(x, A) = E_x[1 + U(Φ_{τ_A}, A); τ_A < ∞]`, from the strong Markov
  property at `τ_A`; `potKernel_le_hitProb_mul`: `U(x, A) ≤ L(x, A) (1 + sup_A U(·, A))`.
* `occTimeN_le_returnTimeK`: pathwise, `η_A^N ≤ k + η_A^N ∘ θ^{τ_A(k)}` (on `{τ_A(k) < ∞}`).

**Proposition 8.3.1** (p. 183): (i) `proposition_8_3_1_i`, `U(x, A) ≤ 1 + M` everywhere if
`U ≤ M` on `A`; (ii) `proposition_8_3_1_ii`, `L ≡ 1` on `A` makes `A` recurrent, and
`proposition_8_3_1_ii_irreducible`: for a `ψ`-irreducible chain and non-empty `A`, then
`A ∈ B⁺(X)` and `U(x, A) = ∞` for every `x`; (iii) `proposition_8_3_1_iii`,
`L ≤ ε < 1` on `A` gives `U(x, A) ≤ (1 − ε)⁻¹` everywhere; (iv) `proposition_8_3_1_iv`,
`P_x(τ_A(m) < ∞) ≤ ε < 1` on `A` gives `U(x, A) ≤ 1 + m (1 − ε)⁻¹` everywhere.

**Proposition 8.3.2** (`proposition_8_3_2`, p. 184): if `A` is uniformly transient and
`B ⇝ᵃ A`, then `B` is uniformly transient; `proposition_8_3_2_cover`: the set `Ā` of points from
which `A` is accessible is covered by the uniformly transient sets `Ā(m)`;
`isTransientSet_univ_of_uniformlyTransient`: hence a `φ`-irreducible chain with a uniformly
transient set of positive `φ`-measure is transient.

**Proposition 8.3.3** (`proposition_8_3_3`, p. 184): if `Dᶜ` is absorbing and `L(x, Dᶜ) > 0` on
`D`, then `D` is transient.

**Corrections.**
* Proposition 8.3.1 (ii), second part, needs `A ≠ ∅`: the empty set satisfies `L ≡ 1` on `A`
  vacuously but is not in `B⁺(X)` (`proposition_8_3_1_ii_counterexample`).
* In the proof of Proposition 8.3.1 (iii) the bound is first obtained for the truncated sums
  `Σ_{n ≤ N} Pⁿ(x, A)`, which are finite; the book's `U^{(z)}` plays the same role.
* Proposition 8.3.2 as printed ("there is a countable covering of `A` by uniformly transient
  sets") is trivial; the statement proved is the one the proof gives, for `Ā = {L(·, A) > 0}`.
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Definitions -/

/-- A set is **uniformly transient** (MT p. 171) if it is measurable and the expected number of
visits `E_x[η_A] = U(x, A)` is bounded by a finite constant for `x ∈ A`. -/
def IsUniformlyTransient (P : Kernel X X) (A : Set X) : Prop :=
  MeasurableSet A ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, potKernel P x A ≤ M

/-- A set is **recurrent** (MT p. 171) if `U(x, A) = E_x[η_A] = ∞` for every `x ∈ A`. -/
def IsRecurrentSet (P : Kernel X X) (A : Set X) : Prop := ∀ x ∈ A, potKernel P x A = ∞

/-- A set is **transient** (MT p. 180) if it is covered by countably many uniformly transient
sets. -/
def IsTransientSet (P : Kernel X X) (A : Set X) : Prop :=
  ∃ B : ℕ → Set X, (∀ n, IsUniformlyTransient P (B n)) ∧ A ⊆ ⋃ n, B n

/-- The chain is **recurrent** (MT p. 180): it is `ψ`-irreducible (`ψ` maximal) and
`U(x, A) = ∞` for every `x ∈ X` and every `A ∈ B⁺(X)`. -/
def IsRecurrentChain (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsMaximalIrreducibility P ψ ∧ ∀ A, MeasurableSet A → 0 < ψ A → ∀ x, potKernel P x A = ∞

/-- The chain is **transient** (MT p. 180): it is `ψ`-irreducible (`ψ` maximal) and `X` is
transient. -/
def IsTransientChain (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsMaximalIrreducibility P ψ ∧ IsTransientSet P univ

/-- A uniformly transient set is transient. -/
theorem IsUniformlyTransient.isTransientSet {P : Kernel X X} {A : Set X}
    (h : IsUniformlyTransient P A) : IsTransientSet P A :=
  ⟨fun _ => A, fun _ => h, subset_iUnion (fun _ : ℕ => A) 0⟩

/-- A subset of a transient set is transient. -/
theorem IsTransientSet.mono {P : Kernel X X} {A B : Set X} (h : IsTransientSet P A)
    (hBA : B ⊆ A) : IsTransientSet P B := by
  obtain ⟨C, hC, hAC⟩ := h
  exact ⟨C, hC, hBA.trans hAC⟩

/-- The empty set is uniformly transient. -/
theorem isUniformlyTransient_empty (P : Kernel X X) : IsUniformlyTransient P ∅ :=
  ⟨MeasurableSet.empty, 0, ENNReal.zero_ne_top, fun _ hx => absurd hx (notMem_empty _)⟩

/-- A countable union of transient sets is transient. -/
theorem isTransientSet_iUnion {P : Kernel X X} {A : ℕ → Set X}
    (h : ∀ n, IsTransientSet P (A n)) : IsTransientSet P (⋃ n, A n) := by
  choose B hB hAB using h
  refine ⟨fun k => B (Nat.unpair k).1 (Nat.unpair k).2, fun k => hB _ _, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hAB n hn)
  exact mem_iUnion.2 ⟨Nat.pair n m, by rwa [Nat.unpair_pair]⟩

/-! ### Occupation times along the path -/

omit [MeasurableSpace X] in
/-- On `{τ_A = ∞}` the chain never visits `A` after time `0`, so `η_A = 0`. -/
theorem occTime_of_firstReturn_top (A : Set X) {ω : ℕ → X} (h : firstReturn A ω = ⊤) :
    occTime A ω = 0 := by
  have h' : ¬ ∃ n, 1 ≤ n ∧ ω n ∈ A := fun hc => (firstReturn_ne_top_iff A ω).2 hc h
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  have : ω (n + 1) ∉ A := fun hn => h' ⟨n + 1, by omega, hn⟩
  simp [this]

omit [MeasurableSpace X] in
/-- On `{τ_A = m}`, the visits to `A` before time `m` number exactly one (at `m`). -/
theorem sum_range_indicator_of_firstReturn_eq (A : Set X) {ω : ℕ → X} {m : ℕ}
    (h : firstReturn A ω = WithTop.some m) :
    ∑ i ∈ Finset.range m, A.indicator (1 : X → ℝ≥0∞) (ω (i + 1)) = 1 := by
  have hm1 : 1 ≤ m := by
    have := one_le_firstReturn A ω
    rw [h] at this
    exact WithTop.coe_le_coe.1 this
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hmem : ω (k + 1) ∈ A := ((firstReturn_eq_iff A ω k).1 h).2
  have hnot : ∀ j, 1 ≤ j → j < k + 1 → ω j ∉ A := (le_firstReturn_iff A ω (k + 1)).1 h.ge
  rw [Finset.sum_range_succ, indicator_of_mem hmem, Pi.one_apply, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [indicator_of_notMem (hnot (i + 1) (by omega) (by simp at hi; omega))]

omit [MeasurableSpace X] in
/-- On `{τ_A = m}`, `η_A = 1 + η_A ∘ θᵐ`. -/
theorem occTime_of_firstReturn_eq (A : Set X) {ω : ℕ → X} {m : ℕ}
    (h : firstReturn A ω = WithTop.some m) : occTime A ω = 1 + occTime A (shift m ω) := by
  unfold occTime
  rw [← (ENNReal.summable (f := fun n => A.indicator (1 : X → ℝ≥0∞) (ω (n + m + 1)))
    ).sum_add_tsum_nat_add' (f := fun n => A.indicator (1 : X → ℝ≥0∞) (ω (n + 1))) (k := m),
    sum_range_indicator_of_firstReturn_eq A h]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [shift_apply]
  rw [show m + (n + 1) = n + m + 1 by omega]

/-- The truncated occupation time `η_A^N = Σ_{n=1}^N 1_A(Φₙ)`. -/
noncomputable def occTimeN (A : Set X) (N : ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, A.indicator 1 (ω (n + 1))

omit [MeasurableSpace X] in
/-- `η_A^N ≤ N`. -/
theorem occTimeN_le (A : Set X) (N : ℕ) (ω : ℕ → X) : occTimeN A N ω ≤ N := by
  unfold occTimeN
  calc ∑ n ∈ Finset.range N, A.indicator (1 : X → ℝ≥0∞) (ω (n + 1))
      ≤ ∑ _n ∈ Finset.range N, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun n _ => indicator_le_self' (fun _ _ => zero_le_one) _
    _ = N := by simp

omit [MeasurableSpace X] in
/-- On `{τ_A = ∞}`, `η_A^N = 0`. -/
theorem occTimeN_of_firstReturn_top (A : Set X) (N : ℕ) {ω : ℕ → X} (h : firstReturn A ω = ⊤) :
    occTimeN A N ω = 0 := by
  have h' : ¬ ∃ n, 1 ≤ n ∧ ω n ∈ A := fun hc => (firstReturn_ne_top_iff A ω).2 hc h
  refine Finset.sum_eq_zero fun n _ => ?_
  have : ω (n + 1) ∉ A := fun hn => h' ⟨n + 1, by omega, hn⟩
  simp [this]

omit [MeasurableSpace X] in
/-- On `{τ_A = m}`, `η_A^N ≤ 1 + η_A^N ∘ θᵐ`. -/
theorem occTimeN_of_firstReturn_eq (A : Set X) (N : ℕ) {ω : ℕ → X} {m : ℕ}
    (h : firstReturn A ω = WithTop.some m) : occTimeN A N ω ≤ 1 + occTimeN A N (shift m ω) := by
  unfold occTimeN
  calc ∑ n ∈ Finset.range N, A.indicator (1 : X → ℝ≥0∞) (ω (n + 1))
      ≤ ∑ n ∈ Finset.range (m + N), A.indicator (1 : X → ℝ≥0∞) (ω (n + 1)) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    _ = 1 + ∑ n ∈ Finset.range N, A.indicator 1 (shift m ω (n + 1)) := by
        rw [Finset.sum_range_add, sum_range_indicator_of_firstReturn_eq A h]
        rfl

/-- `η_A^N` is measurable. -/
theorem measurable_occTimeN {A : Set X} (hA : MeasurableSet A) (N : ℕ) :
    Measurable (occTimeN (X := X) A N) :=
  Finset.measurable_sum _ fun _ _ => (measurable_one.indicator hA).comp (measurable_pi_apply _)

/-- `E_x[η_A^N] = Σ_{n=1}^N Pⁿ(x, A)`. -/
theorem lintegral_occTimeN (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) (N : ℕ) :
    ∫⁻ ω, occTimeN A N ω ∂pathKernel P x = ∑ n ∈ Finset.range N, (P ^ (n + 1)) x A := by
  unfold occTimeN
  rw [lintegral_finsetSum (f := fun n (ω : ℕ → X) => A.indicator (1 : X → ℝ≥0∞) (ω (n + 1)))
    _ fun n _ => (measurable_one.indicator hA).comp (measurable_pi_apply (n + 1))]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hm : MeasurableSet {ω : ℕ → X | ω (n + 1) ∈ A} := measurable_pi_apply (n + 1) hA
  rw [← pathKernel_coord_mem P x (n + 1) hA, ← lintegral_indicator_one hm]
  rfl

/-- `sup_N E_x[η_A^N] = U(x, A)`. -/
theorem iSup_lintegral_occTimeN (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) : ⨆ N, ∫⁻ ω, occTimeN A N ω ∂pathKernel P x = potKernel P x A := by
  simp_rw [lintegral_occTimeN P x hA, potKernel_apply P x hA]
  exact (ENNReal.tsum_eq_iSup_nat).symm

/-- `Σ_{n=1}^N Pⁿ(x, A) ≤ U(x, A)`. -/
theorem sum_pow_le_potKernel (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A)
    (N : ℕ) : ∑ n ∈ Finset.range N, (P ^ (n + 1)) x A ≤ potKernel P x A := by
  rw [potKernel_apply P x hA]
  exact ENNReal.sum_le_tsum _

/-! ### The first-entrance equation -/

/-- The strong Markov property at `τ_A` under `P_x`, for a nonnegative functional `H`. -/
theorem lintegral_shiftAt_firstReturn (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, H (shiftAt (firstReturn A) ω) ∂pathKernel P x =
      ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
        ∫⁻ ω', H ω' ∂pathKernel P (stoppedState (firstReturn A) ω) ∂pathKernel P x := by
  have h := strong_markov_lintegral P (Measure.dirac x) (proposition_3_4_4 hA).1
    MeasurableSet.univ hH
  rw [pathMeasure_dirac, univ_inter] at h
  exact h

/-- **The first-entrance equation for `U`** (the case `A = B`, `z ↑ 1`, of (8.25), MT p. 179):
`U(x, A) = E_x[1 + U(Φ_{τ_A}, A); τ_A < ∞]`. -/
theorem potKernel_eq_firstReturn (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    potKernel P x A = ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
      (1 + potKernel P (stoppedState (firstReturn A) ω) A) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have hT := measurableSet_firstReturn_ne_top hA
  have hH : Measurable fun ω : ℕ → X => 1 + occTime A ω := measurable_const.add
    (measurable_occTime hA)
  rw [potKernel_eq_lintegral_occTime P x hA, ← lintegral_add_compl _ hT]
  have h0 : ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}ᶜ, occTime A ω ∂pathKernel P x = 0 := by
    refine setLIntegral_eq_zero hT.compl (fun ω hω => ?_)
    simp only [mem_compl_iff, mem_ofPred_eq, ne_eq, not_not] at hω
    exact occTime_of_firstReturn_top A hω
  rw [h0, add_zero]
  calc ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, occTime A ω ∂pathKernel P x
      = ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, 1 + occTime A (shiftAt (firstReturn A) ω)
          ∂pathKernel P x := by
        refine setLIntegral_congr_fun hT fun ω hω => ?_
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hω
        rw [shiftAt_of_eq hm.symm]
        exact occTime_of_firstReturn_eq A hm.symm
    _ = _ := by
        rw [lintegral_shiftAt_firstReturn P x hA hH]
        refine setLIntegral_congr_fun hT fun ω _ => ?_
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
          potKernel_eq_lintegral_occTime P _ hA]

/-- `U(x, A) ≤ L(x, A) (1 + M)` when `U(y, A) ≤ M` for `y ∈ A`. -/
theorem potKernel_le_hitProb_mul (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {M : ℝ≥0∞} (hM : ∀ y ∈ A, potKernel P y A ≤ M) (x : X) :
    potKernel P x A ≤ hitProb P A x * (1 + M) := by
  rw [potKernel_eq_firstReturn P x hA, hitProb, mul_comm, ← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun ω hω =>
    add_le_add le_rfl (hM _ (stoppedState_firstReturn_mem A hω))

/-- If `U(y, A) = ∞` for every `y ∈ A`, then `U(x, A) = ∞` whenever `L(x, A) > 0`. -/
theorem potKernel_eq_top_of_hitProb_pos (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hrec : IsRecurrentSet P A) {x : X} (hx : 0 < hitProb P A x) :
    potKernel P x A = ∞ := by
  rw [potKernel_eq_firstReturn P x hA]
  have : ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
      (1 + potKernel P (stoppedState (firstReturn A) ω) A) ∂pathKernel P x =
      ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, ∞ ∂pathKernel P x :=
    setLIntegral_congr_fun (measurableSet_firstReturn_ne_top hA) fun ω hω => by
      rw [hrec _ (stoppedState_firstReturn_mem A hω), add_top]
  rw [this, setLIntegral_const, ← hitProb, ENNReal.top_mul hx.ne']

/-! ### Return times along the path -/

omit [MeasurableSpace X] in
/-- `min{j ≥ t + 1 : Φⱼ ∈ A} = ∞` iff `τ_A ∘ θᵗ = ∞`. -/
theorem hittingAfter_succ_eq_top_iff (A : Set X) (t : ℕ) (ω : ℕ → X) :
    hittingAfter (fun n (ω : ℕ → X) => ω n) A (t + 1) ω = ⊤ ↔ firstReturn A (shift t ω) = ⊤ := by
  rw [hittingAfter_eq_top_iff, ← not_iff_not, ← ne_eq, firstReturn_ne_top_iff]
  push Not
  constructor
  · rintro ⟨j, hj, hjA⟩
    exact ⟨j - t, by omega, by rw [shift_apply, show t + (j - t) = j by omega]; exact hjA⟩
  · rintro ⟨i, hi, hiA⟩
    exact ⟨t + i, by omega, hiA⟩

omit [MeasurableSpace X] in
/-- If `τ_A ∘ θᵗ = s`, then `min{j ≥ t + 1 : Φⱼ ∈ A} = t + s`. -/
theorem hittingAfter_succ_of_firstReturn_shift (A : Set X) {t s : ℕ} {ω : ℕ → X}
    (h : firstReturn A (shift t ω) = WithTop.some s) :
    hittingAfter (fun n (ω : ℕ → X) => ω n) A (t + 1) ω = WithTop.some (t + s) := by
  have hs1 : 1 ≤ s := by
    have := one_le_firstReturn A (shift t ω)
    rw [h] at this
    exact WithTop.coe_le_coe.1 this
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hmem : shift t ω (k + 1) ∈ A := ((firstReturn_eq_iff A _ k).1 h).2
  have hnot := (le_firstReturn_iff A (shift t ω) (k + 1)).1 h.ge
  refine le_antisymm (hittingAfter_le_of_mem (by omega) hmem) ?_
  by_contra hc
  push Not at hc
  obtain ⟨j, hj, hjA⟩ := hittingAfter_lt_iff.1 hc
  rw [mem_Ico] at hj
  refine hnot (j - t) (by omega) (by omega) ?_
  rw [shift_apply, show t + (j - t) = j by omega]
  exact hjA

omit [MeasurableSpace X] in
/-- `τ_A(k + 1) = τ_A(k) + τ_A ∘ θ^{τ_A(k)}`. -/
theorem returnTimeK_succ_eq_add (A : Set X) {k t s : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = WithTop.some t) (hs : firstReturn A (shift t ω) = WithTop.some s) :
    returnTimeK A (k + 1) ω = WithTop.some (t + s) := by
  rw [returnTimeK_succ_of_eq A h, hittingAfter_succ_of_firstReturn_shift A hs]

omit [MeasurableSpace X] in
/-- `τ_A(k + 1) = ∞` when `τ_A(k) = t` and `τ_A ∘ θᵗ = ∞`. -/
theorem returnTimeK_succ_eq_top (A : Set X) {k t : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = WithTop.some t) (hs : firstReturn A (shift t ω) = ⊤) :
    returnTimeK A (k + 1) ω = ⊤ := by
  rw [returnTimeK_succ_of_eq A h, hittingAfter_succ_eq_top_iff A t ω]
  exact hs

omit [MeasurableSpace X] in
/-- `τ_A(k) ≥ k`. -/
theorem le_returnTimeK (A : Set X) (k : ℕ) (ω : ℕ → X) :
    WithTop.some k ≤ returnTimeK A k ω := by
  induction k with
  | zero => exact zero_le
  | succ k ih =>
    cases hk : returnTimeK A k ω with
    | top => rw [returnTimeK_succ_of_top A hk]; exact le_top
    | coe t =>
      rw [hk] at ih
      have ht := WithTop.coe_le_coe.1 ih
      rw [returnTimeK_succ_of_eq A hk]
      exact (WithTop.coe_le_coe.2 (by omega)).trans (le_hittingAfter ω)

omit [MeasurableSpace X] in
/-- `Φ_{τ_A(k + 1)} ∈ A` on `{τ_A(k + 1) < ∞}`. -/
theorem returnTimeK_mem (A : Set X) {k t : ℕ} {ω : ℕ → X}
    (h : returnTimeK A (k + 1) ω = WithTop.some t) : ω t ∈ A := by
  cases hk : returnTimeK A k ω with
  | top => rw [returnTimeK_succ_of_top A hk] at h; exact absurd h WithTop.top_ne_coe
  | coe m =>
    rw [returnTimeK_succ_of_eq A hk] at h
    have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A)
      (n := m + 1) (ω := ω) (by rw [h]; exact WithTop.coe_ne_top)
    rw [h] at this
    exact this

omit [MeasurableSpace X] in
/-- `Φ_{τ_A(k + 1)} ∈ A` on `{τ_A(k + 1) < ∞}`, in terms of `stoppedState`. -/
theorem stoppedState_returnTimeK_mem (A : Set X) (k : ℕ) {ω : ℕ → X}
    (h : returnTimeK A (k + 1) ω ≠ ⊤) : stoppedState (returnTimeK A (k + 1)) ω ∈ A := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
  rw [stoppedState_of_eq ht.symm]
  exact returnTimeK_mem A ht.symm

omit [MeasurableSpace X] in
/-- **Pathwise bound at the `k`-th return.** `η_A^N ≤ k + η_A^N ∘ θ^{τ_A(k)}` on
`{τ_A(k) < ∞}`, and `η_A^N ≤ k` on `{τ_A(k) = ∞}`. -/
theorem occTimeN_le_returnTimeK (A : Set X) (N k : ℕ) (ω : ℕ → X) :
    occTimeN A N ω ≤ k + {ω | returnTimeK A k ω ≠ ⊤}.indicator
      (fun ω => occTimeN A N (shiftAt (returnTimeK A k) ω)) ω := by
  induction k with
  | zero =>
    have h0 : returnTimeK A 0 ω = WithTop.some 0 := rfl
    rw [indicator_of_mem (show ω ∈ {ω | returnTimeK A 0 ω ≠ ⊤} by
      simp only [mem_ofPred_eq, h0]; exact WithTop.coe_ne_top), shiftAt_of_eq h0, shift_zero]
    simp
  | succ k ih =>
    cases hk : returnTimeK A k ω with
    | top =>
      rw [indicator_of_notMem (show ω ∉ {ω | returnTimeK A k ω ≠ ⊤} by simp [hk])] at ih
      rw [indicator_of_notMem (show ω ∉ {ω | returnTimeK A (k + 1) ω ≠ ⊤} by
        simp [returnTimeK_succ_of_top A hk])]
      push_cast
      exact ih.trans (by simp)
    | coe t =>
      rw [indicator_of_mem (show ω ∈ {ω | returnTimeK A k ω ≠ ⊤} by
        simp only [mem_ofPred_eq, hk]; exact WithTop.coe_ne_top), shiftAt_of_eq hk] at ih
      cases hs : firstReturn A (shift t ω) with
      | top =>
        rw [occTimeN_of_firstReturn_top A N hs, add_zero] at ih
        exact ih.trans (by push_cast; exact le_self_add.trans (le_add_right le_rfl))
      | coe s =>
        have h1 := returnTimeK_succ_eq_add A hk hs
        rw [indicator_of_mem (show ω ∈ {ω | returnTimeK A (k + 1) ω ≠ ⊤} by
          simp only [mem_ofPred_eq, h1]; exact WithTop.coe_ne_top), shiftAt_of_eq h1]
        have h2 := occTimeN_of_firstReturn_eq A N hs
        rw [shift_shift] at h2
        calc occTimeN A N ω ≤ k + occTimeN A N (shift t ω) := ih
          _ ≤ k + (1 + occTimeN A N (shift (t + s) ω)) := add_le_add le_rfl h2
          _ = ((k + 1 : ℕ) : ℝ≥0∞) + occTimeN A N (shift (t + s) ω) := by
            push_cast; ring

/-- The strong Markov property at `τ_A(k)` under `P_x`, for a nonnegative functional `H`. -/
theorem lintegral_shiftAt_returnTimeK (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) (k : ℕ) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in {ω | returnTimeK A k ω ≠ ⊤}, H (shiftAt (returnTimeK A k) ω) ∂pathKernel P x =
      ∫⁻ ω in {ω | returnTimeK A k ω ≠ ⊤},
        ∫⁻ ω', H ω' ∂pathKernel P (stoppedState (returnTimeK A k) ω) ∂pathKernel P x := by
  have h := strong_markov_lintegral P (Measure.dirac x) (isStoppingTime_returnTimeK hA k)
    MeasurableSet.univ hH
  rw [pathMeasure_dirac, univ_inter] at h
  exact h

/-- **The truncated bound at the `(k + 1)`-th return.** If `E_y[η_A^N] ≤ S` for `y ∈ A`, then
`E_x[η_A^N] ≤ (k + 1) + S · P_x(τ_A(k + 1) < ∞)`. -/
theorem lintegral_occTimeN_le_returnTimeK (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {A : Set X} (hA : MeasurableSet A) (N k : ℕ) {S : ℝ≥0∞}
    (hS : ∀ y ∈ A, ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ S) :
    ∫⁻ ω, occTimeN A N ω ∂pathKernel P x ≤
      (k + 1 : ℕ) + S * pathKernel P x {ω | returnTimeK A (k + 1) ω ≠ ⊤} := by
  have hT : MeasurableSet {ω : ℕ → X | returnTimeK A (k + 1) ω ≠ ⊤} :=
    measurableSet_ne_top (isStoppingTime_returnTimeK hA (k + 1))
  have hN := measurable_occTimeN hA N
  calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P x
      ≤ ∫⁻ ω, ((k + 1 : ℕ) : ℝ≥0∞) + {ω | returnTimeK A (k + 1) ω ≠ ⊤}.indicator
          (fun ω => occTimeN A N (shiftAt (returnTimeK A (k + 1)) ω)) ω ∂pathKernel P x :=
        lintegral_mono fun ω => occTimeN_le_returnTimeK A N (k + 1) ω
    _ = (k + 1 : ℕ) + ∫⁻ ω in {ω | returnTimeK A (k + 1) ω ≠ ⊤},
          occTimeN A N (shiftAt (returnTimeK A (k + 1)) ω) ∂pathKernel P x := by
        have := isMarkovKernel_pathKernel P
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator hT]
    _ ≤ (k + 1 : ℕ) + S * pathKernel P x {ω | returnTimeK A (k + 1) ω ≠ ⊤} := by
        rw [lintegral_shiftAt_returnTimeK P x hA (k + 1) hN, ← setLIntegral_const]
        exact add_le_add le_rfl (setLIntegral_mono measurable_const fun ω hω =>
          hS _ (stoppedState_returnTimeK_mem A k hω))

/-- **The truncated bound at the first return.** If `E_y[η_A^N] ≤ S` for `y ∈ A`, then
`E_x[η_A^N] ≤ L(x, A) (1 + S)`. -/
theorem lintegral_occTimeN_le_hitProb (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {A : Set X} (hA : MeasurableSet A) (N : ℕ) {S : ℝ≥0∞}
    (hS : ∀ y ∈ A, ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ S) :
    ∫⁻ ω, occTimeN A N ω ∂pathKernel P x ≤ hitProb P A x * (1 + S) := by
  have := isMarkovKernel_pathKernel P
  have hT := measurableSet_firstReturn_ne_top hA
  have hN := measurable_occTimeN hA N
  have hH : Measurable fun ω : ℕ → X => 1 + occTimeN A N ω := measurable_const.add hN
  calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P x
      ≤ ∫⁻ ω, {ω | firstReturn A ω ≠ ⊤}.indicator
          (fun ω => 1 + occTimeN A N (shiftAt (firstReturn A) ω)) ω ∂pathKernel P x := by
        refine lintegral_mono fun ω => ?_
        cases h : firstReturn A ω with
        | top => rw [occTimeN_of_firstReturn_top A N h]; exact zero_le
        | coe m =>
          rw [indicator_of_mem (show ω ∈ {ω | firstReturn A ω ≠ ⊤} by
            simp only [mem_ofPred_eq, h]; exact WithTop.coe_ne_top), shiftAt_of_eq h]
          exact occTimeN_of_firstReturn_eq A N h
    _ = ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
          ∫⁻ ω', 1 + occTimeN A N ω' ∂pathKernel P (stoppedState (firstReturn A) ω)
            ∂pathKernel P x := by
        rw [lintegral_indicator hT, lintegral_shiftAt_firstReturn P x hA hH]
    _ ≤ ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, 1 + S ∂pathKernel P x := by
        refine setLIntegral_mono measurable_const fun ω hω => ?_
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
        exact add_le_add le_rfl (hS _ (stoppedState_firstReturn_mem A hω))
    _ = hitProb P A x * (1 + S) := by rw [setLIntegral_const, mul_comm]; rfl

/-- `S ≤ c + ε S`, `S < ∞` and `ε < 1` give `S ≤ c / (1 − ε)`. -/
theorem le_div_of_le_add_mul {S c ε : ℝ≥0∞} (hS : S ≠ ∞) (hε : ε < 1) (h : S ≤ c + ε * S) :
    S ≤ c / (1 - ε) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (tsub_pos_of_lt hε).ne') (Or.inl (by simp)), mul_comm,
    ENNReal.sub_mul (fun _ _ => hS), one_mul]
  exact tsub_le_iff_right.2 h

/-! ### Proposition 8.3.1 -/

/-- **Proposition 8.3.1 (i)** (MT p. 183): if `U(x, A) ≤ M` for `x ∈ A`, then
`U(x, A) ≤ 1 + M` for every `x ∈ X`; indeed `U(x, A) ≤ L(x, A) (1 + M)` (8.32). -/
theorem proposition_8_3_1_i (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {M : ℝ≥0∞} (hM : ∀ y ∈ A, potKernel P y A ≤ M) (x : X) :
    potKernel P x A ≤ 1 + M :=
  (potKernel_le_hitProb_mul P hA hM x).trans
    (mul_le_of_le_one_left' (hitProb_le_one P A x))

/-- A uniformly transient set has `U(x, A)` bounded on all of `X`. -/
theorem IsUniformlyTransient.exists_bound {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (h : IsUniformlyTransient P A) : ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x, potKernel P x A ≤ M := by
  obtain ⟨hA, M, hM, hb⟩ := h
  exact ⟨1 + M, by simp [hM], proposition_8_3_1_i P hA hb⟩

/-- A measurable subset of a uniformly transient set is uniformly transient. -/
theorem IsUniformlyTransient.mono {P : Kernel X X} [IsMarkovKernel P] {A B : Set X}
    (h : IsUniformlyTransient P A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    IsUniformlyTransient P B := by
  obtain ⟨M, hM, hb⟩ := h.exists_bound
  exact ⟨hB, M, hM, fun x _ => (measure_mono hBA).trans (hb x)⟩

/-- The union of two uniformly transient sets is uniformly transient. -/
theorem IsUniformlyTransient.union {P : Kernel X X} [IsMarkovKernel P] {A B : Set X}
    (hA : IsUniformlyTransient P A) (hB : IsUniformlyTransient P B) :
    IsUniformlyTransient P (A ∪ B) := by
  obtain ⟨M, hM, hb⟩ := hA.exists_bound
  obtain ⟨M', hM', hb'⟩ := hB.exists_bound
  exact ⟨hA.1.union hB.1, M + M', ENNReal.add_ne_top.2 ⟨hM, hM'⟩, fun x _ =>
    (measure_union_le A B).trans (add_le_add (hb x) (hb' x))⟩

/-- **Proposition 8.3.1 (ii)** (MT p. 183): if `L(x, A) = 1` for every `x ∈ A`, then `A` is
recurrent. -/
theorem proposition_8_3_1_ii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (h : ∀ x ∈ A, hitProb P A x = 1) : IsRecurrentSet P A := by
  set m := ⨅ y ∈ A, potKernel P y A with hm
  have hge : ∀ x ∈ A, 1 + m ≤ potKernel P x A := fun x hx => by
    rw [potKernel_eq_firstReturn P x hA]
    calc 1 + m = ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, 1 + m ∂pathKernel P x := by
          rw [setLIntegral_const, ← hitProb, h x hx, mul_one]
      _ ≤ _ := setLIntegral_mono ((measurable_const.add
          ((Kernel.measurable_coe _ hA).comp (measurable_stoppedState
            (proposition_3_4_4 hA).1)))) fun ω hω =>
          add_le_add le_rfl (iInf₂_le _ (stoppedState_firstReturn_mem A hω))
  have hmm : 1 + m ≤ m := le_iInf₂ hge
  have hmt : m = ∞ := by
    by_contra hc
    exact absurd hmm (not_le.2 (by rw [add_comm]; exact ENNReal.lt_add_right hc one_ne_zero))
  intro x hx
  exact top_le_iff.1 (hmt ▸ (le_add_self.trans (hge x hx)))

/-- **Proposition 8.3.1 (ii)**, second part (MT p. 183): for a `ψ`-irreducible chain and a
**non-empty** `A` with `L(x, A) = 1` on `A`, `A ∈ B⁺(X)` and `U(x, A) = ∞` for every `x ∈ X`. -/
theorem proposition_8_3_1_ii_irreducible (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hne : A.Nonempty)
    (h : ∀ x ∈ A, hitProb P A x = 1) : 0 < ψ A ∧ ∀ x, potKernel P x A = ∞ := by
  set Ainf := {x | hitProb P A x = 1} with hAinf
  have hm : MeasurableSet Ainf := (measurable_hitProb P hA) (measurableSet_singleton 1)
  have habs : IsAbsorbing P Ainf := by
    intro x hx
    have hint : ∫⁻ y, hitProb P A y ∂P x = 1 := by
      rw [← lintegral_add_compl _ hA, setLIntegral_congr_fun hA (fun y hy => h y hy),
        setLIntegral_const, one_mul, ← hitProb_first_step P hA x]
      exact hx
    exact measure_setOf_eq_one (measurable_hitProb P hA) (hitProb_le_one P A) hint
  have hfull := proposition_4_2_3_i hψ.2.1 hm (hne.mono fun x hx => h x hx) habs
  have hpos : 0 < ψ A := by
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := hψ.hitSet_null hA h0
    have h2 : ψ Ainf = 0 := measure_mono_null (fun x (hx : hitProb P A x = 1) => by
      change 0 < hitProb P A x
      rw [hx]; exact one_pos) h1
    exact hψ.1 (Measure.measure_univ_eq_zero.1 (by
      rw [← union_compl_self Ainf]; exact measure_union_null h2 hfull))
  exact ⟨hpos, fun x => potKernel_eq_top_of_hitProb_pos P hA (proposition_8_3_1_ii P hA h)
    (hψ.2.1 A hA hpos x)⟩

/-- **Correction to Proposition 8.3.1 (ii)**: `A ≠ ∅` is needed. The empty set satisfies
`L(x, A) = 1` for every `x ∈ A` vacuously, but it is not in `B⁺(X)`. -/
theorem proposition_8_3_1_ii_counterexample (P : Kernel X X) [IsMarkovKernel P]
    (ψ : Measure X) : (∀ x ∈ (∅ : Set X), hitProb P ∅ x = 1) ∧ ¬ 0 < ψ ∅ := by
  simp

/-- **Proposition 8.3.1 (iii)** (MT p. 183): if `L(x, A) ≤ ε < 1` for `x ∈ A`, then
`U(x, A) ≤ (1 − ε)⁻¹` for every `x ∈ X`; in particular `A` is uniformly transient. -/
theorem proposition_8_3_1_iii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : ε < 1) (h : ∀ x ∈ A, hitProb P A x ≤ ε) (x : X) :
    potKernel P x A ≤ (1 - ε)⁻¹ := by
  have := isMarkovKernel_pathKernel P
  rw [← iSup_lintegral_occTimeN P x hA]
  refine iSup_le fun N => ?_
  set S := ⨆ y ∈ A, ∫⁻ ω, occTimeN A N ω ∂pathKernel P y with hSdef
  have hS : ∀ y ∈ A, ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ S := fun y hy =>
    le_iSup₂ (f := fun y _ => ∫⁻ ω, occTimeN A N ω ∂pathKernel P y) y hy
  have hSfin : S ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (iSup₂_le fun y _ => ?_)
    calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ ∫⁻ _, (N : ℝ≥0∞) ∂pathKernel P y :=
          lintegral_mono fun ω => occTimeN_le A N ω
      _ = N := by simp
  have hSle : S ≤ ε / (1 - ε) := by
    refine le_div_of_le_add_mul hSfin hε (iSup₂_le fun y hy => ?_)
    calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ hitProb P A y * (1 + S) :=
          lintegral_occTimeN_le_hitProb P y hA N hS
      _ ≤ ε * (1 + S) := mul_le_mul_left (h y hy) _
      _ = ε + ε * S := by rw [mul_add, mul_one]
  calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P x ≤ hitProb P A x * (1 + S) :=
        lintegral_occTimeN_le_hitProb P x hA N hS
    _ ≤ 1 * (1 + ε / (1 - ε)) :=
        mul_le_mul' (hitProb_le_one P A x) (add_le_add le_rfl hSle)
    _ = (1 - ε) / (1 - ε) + ε / (1 - ε) := by
        rw [ENNReal.div_self (tsub_pos_of_lt hε).ne' (by simp), one_mul]
    _ = (1 - ε)⁻¹ := by
        rw [ENNReal.div_add_div_same, tsub_add_cancel_of_le hε.le, one_div]

/-- **Proposition 8.3.1 (iv)** (MT p. 183): if `P_x(τ_A(m) < ∞) ≤ ε < 1` for `x ∈ A`, then
`U(x, A) ≤ m (1 − ε)⁻¹` on `A` (8.35), and `U(x, A) ≤ 1 + m (1 − ε)⁻¹` for every `x ∈ X`. -/
theorem proposition_8_3_1_iv (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (m : ℕ) {ε : ℝ≥0∞} (hε : ε < 1)
    (h : ∀ x ∈ A, pathKernel P x {ω | returnTimeK A m ω ≠ ⊤} ≤ ε) :
    (∀ x ∈ A, potKernel P x A ≤ m / (1 - ε)) ∧ ∀ x, potKernel P x A ≤ 1 + m / (1 - ε) := by
  have := isMarkovKernel_pathKernel P
  have hA' : ∀ x ∈ A, potKernel P x A ≤ m / (1 - ε) := by
    rcases m with _ | k
    · intro x hx
      have h1 := h x hx
      have : pathKernel P x {ω : ℕ → X | returnTimeK A 0 ω ≠ ⊤} = 1 := by
        have : {ω : ℕ → X | returnTimeK A 0 ω ≠ ⊤} = univ :=
          eq_univ_of_forall fun ω => by
            change (WithTop.some 0 : WithTop ℕ) ≠ ⊤; exact WithTop.coe_ne_top
        rw [this, measure_univ]
      rw [this] at h1
      exact absurd hε (not_lt.2 h1)
    intro x hx
    rw [← iSup_lintegral_occTimeN P x hA]
    refine iSup_le fun N => ?_
    set S := ⨆ y ∈ A, ∫⁻ ω, occTimeN A N ω ∂pathKernel P y with hSdef
    have hS : ∀ y ∈ A, ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ S := fun y hy =>
      le_iSup₂ (f := fun y _ => ∫⁻ ω, occTimeN A N ω ∂pathKernel P y) y hy
    have hSfin : S ≠ ∞ := by
      refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (iSup₂_le fun y _ => ?_)
      calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤ ∫⁻ _, (N : ℝ≥0∞) ∂pathKernel P y :=
            lintegral_mono fun ω => occTimeN_le A N ω
        _ = N := by simp
    have hSle : S ≤ (k + 1 : ℕ) / (1 - ε) := by
      refine le_div_of_le_add_mul hSfin hε (iSup₂_le fun y hy => ?_)
      calc ∫⁻ ω, occTimeN A N ω ∂pathKernel P y ≤
            (k + 1 : ℕ) + S * pathKernel P y {ω | returnTimeK A (k + 1) ω ≠ ⊤} :=
            lintegral_occTimeN_le_returnTimeK P y hA N k hS
        _ ≤ (k + 1 : ℕ) + ε * S := by rw [mul_comm]; gcongr; exact h y hy
    exact (hS x hx).trans hSle
  exact ⟨hA', proposition_8_3_1_i P hA hA'⟩

/-! ### Proposition 8.3.2 -/

/-- **Proposition 8.3.2** (MT p. 184): if `A` is uniformly transient and `B ⇝ᵃ A` for a
sampling distribution `a`, then `B` is uniformly transient: `δ U(x, B) ≤ ∫ U(x, dy) K_a(y, A)
≤ U(x, A)`. -/
theorem proposition_8_3_2 (P : Kernel X X) [IsMarkovKernel P] {A B : Set X}
    (hA : IsUniformlyTransient P A) (hB : MeasurableSet B) {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) (hBA : SampledAccessible P a B A) : IsUniformlyTransient P B := by
  obtain ⟨M, hM, hb⟩ := hA.exists_bound
  obtain ⟨δ, hδ, hK⟩ := hBA
  refine ⟨hB, M / δ, ENNReal.div_ne_top hM hδ.ne', fun x _ => ?_⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl hδ.ne') (Or.inr hM), mul_comm]
  calc δ * potKernel P x B = ∫⁻ _ in B, δ ∂potKernel P x := by rw [setLIntegral_const]
    _ ≤ ∫⁻ y in B, sampledKernel P a y A ∂potKernel P x :=
        setLIntegral_mono (Kernel.measurable_coe _ hA.1) hK
    _ ≤ ∫⁻ y, sampledKernel P a y A ∂potKernel P x := setLIntegral_le_lintegral _ _
    _ ≤ potKernel P x A := lemma_5_5_2_iii P ha x hA.1
    _ ≤ M := hb x

/-- `Ā(m) ⇝ A` for the uniform sampling distribution on `{1, …, m}`, with `δ = m⁻²`. -/
theorem sampledAccessible_hitSetLevel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (m : ℕ) : SampledAccessible P (uniformDist m) (hitSetLevel P A m) A := by
  refine ⟨(m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞)⁻¹, ENNReal.mul_pos (by simp) (by simp), fun x hx => ?_⟩
  rw [sampledKernel_uniformDist_apply P m x hA]
  refine mul_le_mul' le_rfl ?_
  have heq : ∑ n ∈ Finset.Icc 1 m, (P ^ n) x A = ∑ n ∈ Finset.range m, (P ^ (n + 1)) x A := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun n _ => by rw [add_comm]
  rw [heq]
  exact hx

/-- **Proposition 8.3.2**, the covering (MT p. 184): if `A` is uniformly transient, the set
`Ā = {x : L(x, A) > 0}` is covered by the uniformly transient sets `Ā(m)`. -/
theorem proposition_8_3_2_cover (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : IsUniformlyTransient P A) : IsTransientSet P (hitSet P A) := by
  refine ⟨hitSetLevel P A, fun m => ?_, (lemma_4_2_6 P hA.1).1.le⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : hitSetLevel P A 0 = ∅ := by
      ext x; simp [hitSetLevel]
    rw [this]; exact isUniformlyTransient_empty P
  · exact proposition_8_3_2 P hA (measurableSet_hitSetLevel P hA.1 m)
      (isSamplingDist_uniformDist hm) (sampledAccessible_hitSetLevel P hA.1 m)

/-- A `φ`-irreducible chain with a uniformly transient set `A`, `φ(A) > 0`, is transient: `X` is
covered by the uniformly transient sets `Ā(m)`. -/
theorem isTransientSet_univ_of_uniformlyTransient (P : Kernel X X) [IsMarkovKernel P]
    {φ : Measure X} (hφ : IsPhiIrreducible P φ) {A : Set X} (hA : IsUniformlyTransient P A)
    (hpos : 0 < φ A) : IsTransientSet P univ := by
  have : hitSet P A = univ := eq_univ_of_forall fun x => hφ A hA.1 hpos x
  rw [← this]
  exact proposition_8_3_2_cover P hA

/-! ### Proposition 8.3.3 -/

/-- **The Markov property at a fixed time** under `P_x`:
`P_x(Φₙ ∈ C, θⁿΦ ∈ S) = ∫_C Pⁿ(x, dy) P_y(S)`. -/
theorem pathKernel_coord_inter_shift (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ)
    {C : Set X} (hC : MeasurableSet C) {S : Set (ℕ → X)} (hS : MeasurableSet S) :
    pathKernel P x ({ω | ω n ∈ C} ∩ shift n ⁻¹' S) = ∫⁻ y in C, pathKernel P y S ∂(P ^ n) x := by
  have := isMarkovKernel_pathKernel P
  have hG : MeasurableSet[natFilt n] {ω : ℕ → X | ω n ∈ C} :=
    measurableSet_coord_natFilt le_rfl hC
  have hGm : MeasurableSet {ω : ℕ → X | ω n ∈ C} := measurable_pi_apply n hC
  have hi : Measurable (S.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hS
  have h := markov_lintegral P (Measure.dirac x) hG hi
  rw [pathMeasure_dirac] at h
  have hsh : MeasurableSet (shift n ⁻¹' S) := measurable_shift n hS
  have e1 : ∫⁻ ω in {ω : ℕ → X | ω n ∈ C}, S.indicator 1 (shift n ω) ∂pathKernel P x =
      pathKernel P x ({ω | ω n ∈ C} ∩ shift n ⁻¹' S) := by
    calc ∫⁻ ω in {ω : ℕ → X | ω n ∈ C}, S.indicator 1 (shift n ω) ∂pathKernel P x
        = ∫⁻ ω in {ω : ℕ → X | ω n ∈ C}, (shift n ⁻¹' S).indicator 1 ω ∂pathKernel P x := rfl
      _ = _ := by rw [lintegral_indicator_one hsh, Measure.restrict_apply hsh, inter_comm]
  simp_rw [lintegral_indicator_one hS] at h
  have hk : Measurable fun y => pathKernel P y S := Kernel.measurable_coe _ hS
  rw [← e1, h, ← lintegral_indicator hGm]
  have e2 : ({ω : ℕ → X | ω n ∈ C}.indicator fun ω => pathKernel P (ω n) S) =
      fun ω => C.indicator (fun y => pathKernel P y S) (ω n) := by
    ext ω; by_cases h : ω n ∈ C <;> simp [h]
  rw [e2, ← lintegral_map (hk.indicator hC) (measurable_pi_apply n), pathKernel_map_coord,
    lintegral_indicator hC]

/-- From an absorbing set `F`, `Pⁿ(y, F)` is nondecreasing in `n`. -/
theorem IsAbsorbing.pow_mono {P : Kernel X X} [IsMarkovKernel P] {F : Set X}
    (habs : IsAbsorbing P F) (hF : MeasurableSet F) (y : X) {a b : ℕ} (hab : a ≤ b) :
    (P ^ a) y F ≤ (P ^ b) y F := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Kernel.pow_add_apply_eq_lintegral P a c y hF]
  calc (P ^ a) y F = ∫⁻ _ in F, 1 ∂(P ^ a) y := by rw [setLIntegral_const, one_mul]
    _ = ∫⁻ z in F, (P ^ c) z F ∂(P ^ a) y :=
        setLIntegral_congr_fun hF fun z hz => (habs.pow_apply hF c hz).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- **Proposition 8.3.3** (MT p. 184): if `Dᶜ` is absorbing and `L(x, Dᶜ) > 0` for every
`x ∈ D`, then `D` is transient. It is covered by the sets
`B(m) = {y ∈ D : Pᵐ(y, Dᶜ) ≥ m⁻¹}`, each uniformly transient by Proposition 8.3.1 (iv). -/
theorem proposition_8_3_3 (P : Kernel X X) [IsMarkovKernel P] {D : Set X}
    (hD : MeasurableSet D) (habs : IsAbsorbing P Dᶜ) (hL : ∀ x ∈ D, 0 < hitProb P Dᶜ x) :
    IsTransientSet P D := by
  have := isMarkovKernel_pathKernel P
  set B : ℕ → Set X := fun m => {y ∈ D | ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (P ^ (m + 1)) y Dᶜ} with hB
  have hBm : ∀ m, MeasurableSet (B m) := fun m =>
    hD.inter (measurableSet_le measurable_const (Kernel.measurable_coe _ hD.compl))
  refine ⟨B, fun m => ?_, fun x hx => ?_⟩
  · -- `B m` is uniformly transient, by Proposition 8.3.1 (iv) with `τ_{B m}(m + 1)`
    set ε : ℝ≥0∞ := 1 - ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ with hεdef
    have hε : ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (by simp)
    have hbound : ∀ y ∈ B m, pathKernel P y {ω | returnTimeK (B m) (m + 1) ω ≠ ⊤} ≤ ε := by
      intro y hy
      have hsub : {ω : ℕ → X | returnTimeK (B m) (m + 1) ω ≠ ⊤} ⊆
          {ω | ω (m + 1) ∈ D} ∪ ({ω | ω (m + 1) ∈ Dᶜ} ∩
            shift (m + 1) ⁻¹' {ω | firstReturn D ω ≠ ⊤}) := by
        intro ω hω
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
        have htm : m + 1 ≤ t := by
          have := le_returnTimeK (B m) (m + 1) ω
          rw [← ht] at this
          exact WithTop.coe_le_coe.1 this
        have hDt : ω t ∈ D := (returnTimeK_mem (B m) ht.symm).1
        by_cases hm1 : ω (m + 1) ∈ D
        · exact Or.inl hm1
        · refine Or.inr ⟨hm1, (firstReturn_ne_top_iff D _).2 ⟨t - (m + 1), ?_, ?_⟩⟩
          · by_contra hc
            have : t = m + 1 := by omega
            exact hm1 (this ▸ hDt)
          · rw [shift_apply, show m + 1 + (t - (m + 1)) = t by omega]; exact hDt
      calc pathKernel P y {ω | returnTimeK (B m) (m + 1) ω ≠ ⊤}
          ≤ pathKernel P y {ω | ω (m + 1) ∈ D} + pathKernel P y ({ω | ω (m + 1) ∈ Dᶜ} ∩
              shift (m + 1) ⁻¹' {ω | firstReturn D ω ≠ ⊤}) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ = (P ^ (m + 1)) y D + 0 := by
            rw [pathKernel_coord_mem P y _ hD, pathKernel_coord_inter_shift P y (m + 1)
              hD.compl (measurableSet_firstReturn_ne_top hD)]
            congr 1
            refine setLIntegral_eq_zero hD.compl fun z hz => ?_
            have := habs.hitProb_compl hD.compl hz
            rw [compl_compl] at this
            exact this
        _ ≤ ε := by
            have := isMarkovKernel_pow P (m + 1)
            have hc := prob_compl_eq_one_sub (μ := (P ^ (m + 1)) y) hD.compl
            rw [compl_compl] at hc
            rw [add_zero, hc]
            exact tsub_le_tsub_left hy.2 1
    obtain ⟨-, hall⟩ := proposition_8_3_1_iv P (hBm m) (m + 1) hε hbound
    refine ⟨hBm m, 1 + ((m + 1 : ℕ) : ℝ≥0∞) / (1 - ε), ?_, fun x _ => hall x⟩
    refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.div_ne_top (by simp) ?_⟩
    exact (tsub_pos_of_lt hε).ne'
  · -- the sets `B m` cover `D`
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P hD.compl x).1 (hL x hx)
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hn.ne'
    refine mem_iUnion.2 ⟨max n k, hx, ?_⟩
    calc ((max n k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ :=
          ENNReal.inv_le_inv.2 (by exact_mod_cast (by omega : k ≤ max n k + 1))
      _ ≤ (P ^ (n + 1)) x Dᶜ := hk.le
      _ ≤ (P ^ (max n k + 1)) x Dᶜ := habs.pow_mono hD.compl x (by omega)

end MeynTweedie.Ergodicity
