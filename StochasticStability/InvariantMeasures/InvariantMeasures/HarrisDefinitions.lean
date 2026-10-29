/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.DriftCriteria

/-!
# Infinitely many visits and Harris recurrence: definitions (MT §9.0–9.1)

Meyn and Tweedie, Chapter 9, pp. 199–200.

**The event `{Φ ∈ A i.o.}` and `Q`.**
* `ioSet A = {Φ ∈ A i.o.} = ⋂_N ⋃_{k ≥ N} {Φₖ ∈ A}` (p. 199), `measurableSet_ioSet`;
  `mem_ioSet_iff_occTime`: it is the event `{η_A = ∞}`.
* `harrisQ P A x = Q(x, A) = P_x{Φ ∈ A i.o.}` (9.1), with `harrisQ_eq_occTime` (`= P_x(η_A = ∞)`),
  `harrisQ_le_hitProb` (`Q ≤ L`, p. 199), `measurable_harrisQ` and `harrisQ_mono`.
* `potKernel_eq_top_of_harrisQ_pos` and `harrisQ_eq_zero_of_potKernel_ne_top`: `Q(x, A) > 0`
  forces `U(x, A) = E_x[η_A] = ∞`.
* `IsShiftInvariant E`: `θᵐω ∈ E ↔ ω ∈ E` for every `m` (`{Φ ∈ A i.o.}` is such an event).
  `pathKernel_inter_ne_top_of_shiftInvariant`: the strong Markov property at a stopping time `ζ`
  for such events, `P_x(E ∩ {ζ < ∞}) = E_x[P_{Φ_ζ}(E); ζ < ∞]`;
  `pathKernel_shiftInvariant_eq_pow`: `P_x(E) = ∫ Pⁿ(x, dy) P_y(E)`.
* **(9.2)** (`harrisQ_eq_firstReturn`, p. 199): `Q(x, A) = E_x[Q(Φ_{τ_A}, A); τ_A < ∞]`, and in
  kernel form `harrisQ_eq_tabooPotKernel`, `Q(x, A) = ∫_A U_A(x, dy) Q(y, A)`, from
  `setLIntegral_firstReturn_eq_tabooPotKernel` (the law of `Φ_{τ_A}` on `{τ_A < ∞}` is
  `U_A(x, ·)`);
  `harrisQ_eq_lintegral_pow`: `Q(x, A) = ∫ Pⁿ(x, dy) Q(y, A)`; `harrisQ_ge_stopping`.
* `pathKernel_occTime_ge_succ`: `P_x(η_A ≥ k + 1) = E_x[P_{Φ_{τ_A}}(η_A ≥ k); τ_A < ∞]`, and
  `le_occTime_of_returnTimeK`: `τ_A(k) < ∞` implies `η_A ≥ k`.

**Harris recurrence** (p. 199).
* `IsHarrisRecurrentSet P A`: `Q(x, A) = 1` for every `x ∈ A`; `IsHarris P ψ`: `ψ` is a maximal
  irreducibility measure and every set in `B⁺(X)` is Harris recurrent.
* `IsHarrisRecurrentSet.isRecurrentSet` (p. 200): a Harris recurrent set is recurrent.

**Corrections.** None.
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The event `{Φ ∈ A i.o.}` -/

/-- The event `{Φ ∈ A i.o.} = ⋂_N ⋃_{k ≥ N} {Φₖ ∈ A}` (MT p. 199). -/
def ioSet (A : Set X) : Set (ℕ → X) := {ω | ∀ N, ∃ k, N ≤ k ∧ ω k ∈ A}

omit [MeasurableSpace X] in
/-- `{Φ ∈ A i.o.}` written as a limsup of events. -/
theorem ioSet_eq_iInter (A : Set X) :
    ioSet A = ⋂ N, ⋃ k, ⋃ (_ : N ≤ k), {ω : ℕ → X | ω k ∈ A} := by
  ext ω; simp [ioSet]

/-- `{Φ ∈ A i.o.}` is an event. -/
theorem measurableSet_ioSet {A : Set X} (hA : MeasurableSet A) : MeasurableSet (ioSet A) := by
  rw [ioSet_eq_iInter]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ => measurable_pi_apply k hA

omit [MeasurableSpace X] in
/-- `{Φ ∈ A i.o.}` is invariant under the shift. -/
theorem shift_mem_ioSet_iff (A : Set X) (m : ℕ) (ω : ℕ → X) :
    shift m ω ∈ ioSet A ↔ ω ∈ ioSet A := by
  constructor
  · intro h N
    obtain ⟨k, hk, hkA⟩ := h N
    exact ⟨m + k, by omega, hkA⟩
  · intro h N
    obtain ⟨k, hk, hkA⟩ := h (N + m)
    refine ⟨k - m, by omega, ?_⟩
    rw [shift_apply, show m + (k - m) = k by omega]
    exact hkA

omit [MeasurableSpace X] in
/-- `{Φ ∈ A i.o.}` is monotone in `A`. -/
theorem ioSet_mono {A B : Set X} (h : A ⊆ B) : ioSet A ⊆ ioSet B := fun _ hω N => by
  obtain ⟨k, hk, hkA⟩ := hω N
  exact ⟨k, hk, h hkA⟩

omit [MeasurableSpace X] in
/-- A path in `A` infinitely often returns to `A`: `{Φ ∈ A i.o.} ⊆ {τ_A < ∞}`. -/
theorem ioSet_subset_firstReturn (A : Set X) : ioSet A ⊆ {ω | firstReturn A ω ≠ ⊤} := by
  intro ω hω
  obtain ⟨k, hk, hkA⟩ := hω 1
  exact (firstReturn_ne_top_iff A ω).2 ⟨k, hk, hkA⟩

omit [MeasurableSpace X] in
/-- The truncated occupation times are monotone in the horizon. -/
theorem occTimeN_mono (A : Set X) (ω : ℕ → X) {M N : ℕ} (h : M ≤ N) :
    occTimeN A M ω ≤ occTimeN A N ω :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

omit [MeasurableSpace X] in
/-- `η_A ≥ η_A^N`. -/
theorem occTimeN_le_occTime (A : Set X) (N : ℕ) (ω : ℕ → X) : occTimeN A N ω ≤ occTime A ω :=
  ENNReal.sum_le_tsum _

omit [MeasurableSpace X] in
/-- A visit at time `j ≥ 1` adds one to the truncated occupation time. -/
theorem occTimeN_add_one_le (A : Set X) (ω : ℕ → X) {M j : ℕ} (hj : M < j) (hjA : ω j ∈ A) :
    occTimeN A M ω + 1 ≤ occTimeN A j ω := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e : occTimeN A (i + 1) ω = occTimeN A i ω + A.indicator 1 (ω (i + 1)) :=
    Finset.sum_range_succ _ _
  rw [e, indicator_of_mem hjA, Pi.one_apply]
  gcongr
  exact occTimeN_mono A ω (by omega)

omit [MeasurableSpace X] in
/-- `{Φ ∈ A i.o.} = {η_A = ∞}` (MT p. 199). -/
theorem mem_ioSet_iff_occTime (A : Set X) (ω : ℕ → X) :
    ω ∈ ioSet A ↔ occTime A ω = ∞ := by
  constructor
  · intro h
    have hk : ∀ k : ℕ, ∃ M, (k : ℝ≥0∞) ≤ occTimeN A M ω := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨M, hM⟩ := ih
        obtain ⟨j, hj, hjA⟩ := h (M + 1)
        refine ⟨j, ?_⟩
        calc ((k + 1 : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) + 1 := by push_cast; ring
          _ ≤ occTimeN A M ω + 1 := by gcongr
          _ ≤ occTimeN A j ω := occTimeN_add_one_le A ω (by omega) hjA
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨M, hM⟩ := hk ⌈(r : ℝ)⌉₊
    calc (r : ℝ≥0∞) ≤ (⌈(r : ℝ)⌉₊ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ occTimeN A M ω := hM
      _ ≤ occTime A ω := occTimeN_le_occTime A M ω
  · intro h
    by_contra hω
    simp only [ioSet, mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨N, hN⟩ := hω
    have heq : occTime A ω = occTimeN A N ω := by
      unfold occTime occTimeN
      refine tsum_eq_sum fun b hb => ?_
      rw [Finset.mem_range, not_lt] at hb
      exact indicator_of_notMem (hN (b + 1) (by omega)) _
    have hlt : occTimeN A N ω < ∞ := (occTimeN_le A N ω).trans_lt (ENNReal.natCast_lt_top N)
    rw [heq] at h
    exact hlt.ne h

/-! ### `Q(x, A)` -/

/-- `Q(x, A) = P_x{Φ ∈ A i.o.}` (9.1), MT p. 199. -/
noncomputable def harrisQ (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) : ℝ≥0∞ :=
  pathKernel P x (ioSet A)

/-- `Q(x, A) = P_x(η_A = ∞)`. -/
theorem harrisQ_eq_occTime (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    harrisQ P A x = pathKernel P x {ω | occTime A ω = ∞} := by
  rw [harrisQ]
  congr 1
  ext ω
  exact mem_ioSet_iff_occTime A ω

/-- `x ↦ Q(x, A)` is measurable. -/
theorem measurable_harrisQ (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : Measurable (harrisQ P A) :=
  Kernel.measurable_coe _ (measurableSet_ioSet hA)

/-- `Q(x, A) ≤ 1`. -/
theorem harrisQ_le_one (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    harrisQ P A x ≤ 1 := by
  have := isMarkovKernel_pathKernel P
  exact prob_le_one

/-- `Q(x, ·)` is monotone. -/
theorem harrisQ_mono (P : Kernel X X) [IsMarkovKernel P] {A B : Set X} (h : A ⊆ B) (x : X) :
    harrisQ P A x ≤ harrisQ P B x :=
  measure_mono (ioSet_mono h)

/-- `Q(x, A) ≤ L(x, A)` (MT p. 199). -/
theorem harrisQ_le_hitProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    harrisQ P A x ≤ hitProb P A x :=
  measure_mono (ioSet_subset_firstReturn A)

/-- If `Q(x, A) > 0` then `U(x, A) = E_x[η_A] = ∞`. -/
theorem potKernel_eq_top_of_harrisQ_pos (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {x : X} (hQ : 0 < harrisQ P A x) : potKernel P x A = ∞ := by
  rw [potKernel_eq_lintegral_occTime P x hA]
  have hm : MeasurableSet (ioSet A) := measurableSet_ioSet hA
  refine top_unique ?_
  calc (∞ : ℝ≥0∞) = ∫⁻ _ in ioSet A, ∞ ∂pathKernel P x := by
        rw [setLIntegral_const, ENNReal.top_mul (show pathKernel P x (ioSet A) ≠ 0 from hQ.ne')]
    _ = ∫⁻ ω in ioSet A, occTime A ω ∂pathKernel P x :=
        (setLIntegral_congr_fun hm fun ω hω => (mem_ioSet_iff_occTime A ω).1 hω).symm
    _ ≤ ∫⁻ ω, occTime A ω ∂pathKernel P x := setLIntegral_le_lintegral _ _

/-- If `U(x, A) < ∞` then `Q(x, A) = 0`: finitely many visits, almost surely. -/
theorem harrisQ_eq_zero_of_potKernel_ne_top (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {x : X} (hU : potKernel P x A ≠ ∞) : harrisQ P A x = 0 := by
  by_contra h
  exact hU (potKernel_eq_top_of_harrisQ_pos P hA (pos_iff_ne_zero.2 h))

/-! ### Shift-invariant events and the strong Markov property -/

/-- An event `E` of path space is **shift invariant** if `θᵐω ∈ E ↔ ω ∈ E` for every `m`: whether
it occurs does not depend on any initial segment of the path. -/
def IsShiftInvariant (E : Set (ℕ → X)) : Prop := ∀ (m : ℕ) (ω : ℕ → X), shift m ω ∈ E ↔ ω ∈ E

omit [MeasurableSpace X] in
/-- `{Φ ∈ A i.o.}` is shift invariant. -/
theorem isShiftInvariant_ioSet (A : Set X) : IsShiftInvariant (ioSet A) :=
  shift_mem_ioSet_iff A

/-- **The strong Markov property for shift-invariant events.** For a stopping time `ζ`,
`P_x(E ∩ {ζ < ∞}) = E_x[P_{Φ_ζ}(E); ζ < ∞]`. -/
theorem pathKernel_inter_ne_top_of_shiftInvariant (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ) {E : Set (ℕ → X)}
    (hE : MeasurableSet E) (hinv : IsShiftInvariant E) :
    pathKernel P x (E ∩ {ω | τ ω ≠ ⊤}) =
      ∫⁻ ω in {ω | τ ω ≠ ⊤}, pathKernel P (stoppedState τ ω) E ∂pathKernel P x := by
  have hi : Measurable (E.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hE
  have h := strong_markov_lintegral P (Measure.dirac x) hτ MeasurableSet.univ hi
  rw [pathMeasure_dirac, univ_inter] at h
  simp_rw [lintegral_indicator_one hE] at h
  rw [← h]
  have hT := measurableSet_ne_top hτ
  have hset : E ∩ {ω | τ ω ≠ ⊤} = {ω | τ ω ≠ ⊤} ∩ shiftAt τ ⁻¹' E := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    constructor
    · rintro ⟨hω, hne⟩
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
      refine ⟨hne, ?_⟩
      rw [shiftAt_of_eq hm.symm]
      exact (hinv m ω).2 hω
    · rintro ⟨hne, hω⟩
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [shiftAt_of_eq hm.symm] at hω
      exact ⟨(hinv m ω).1 hω, hne⟩
  have hpre : MeasurableSet (shiftAt τ ⁻¹' E) := measurable_shiftAt hτ hE
  have e : ∫⁻ ω in {ω | τ ω ≠ ⊤}, E.indicator 1 (shiftAt τ ω) ∂pathKernel P x =
      ∫⁻ ω in {ω | τ ω ≠ ⊤}, (shiftAt τ ⁻¹' E).indicator 1 ω ∂pathKernel P x := rfl
  rw [hset, e, lintegral_indicator_one hpre, Measure.restrict_apply hpre, inter_comm]

/-- For a shift-invariant event, `P_x(E) = ∫ Pⁿ(x, dy) P_y(E)`. -/
theorem pathKernel_shiftInvariant_eq_pow (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ)
    {E : Set (ℕ → X)} (hE : MeasurableSet E) (hinv : IsShiftInvariant E) :
    pathKernel P x E = ∫⁻ y, pathKernel P y E ∂(P ^ n) x := by
  have hi : Measurable (E.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hE
  have h := markov_lintegral_univ P (Measure.dirac x) n hi
  rw [pathMeasure_dirac] at h
  simp_rw [lintegral_indicator_one hE] at h
  have hpre : MeasurableSet (shift n ⁻¹' E) := measurable_shift n hE
  have hset : shift n ⁻¹' E = E := by ext ω; exact hinv n ω
  have e1 : ∫⁻ ω, E.indicator 1 (shift n ω) ∂pathKernel P x = pathKernel P x E := by
    change ∫⁻ ω, (shift n ⁻¹' E).indicator 1 ω ∂pathKernel P x = _
    rw [lintegral_indicator_one hpre, hset]
  rw [← e1, h, ← lintegral_map (Kernel.measurable_coe _ hE) (measurable_pi_apply n),
    pathKernel_map_coord]

/-- **(9.2)**, MT p. 199: `Q(x, A) = E_x[Q(Φ_{τ_A}, A); τ_A < ∞]`, by the strong Markov property
at `τ_A`. -/
theorem harrisQ_eq_firstReturn (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    harrisQ P A x = ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
      harrisQ P A (stoppedState (firstReturn A) ω) ∂pathKernel P x := by
  have h := pathKernel_inter_ne_top_of_shiftInvariant P x (proposition_3_4_4 hA).1
    (measurableSet_ioSet hA) (isShiftInvariant_ioSet A)
  rw [inter_eq_left.2 (ioSet_subset_firstReturn A)] at h
  exact h

/-- **The law of `Φ_{τ_A}` is `U_A(x, ·)`** (MT p. 67): for measurable `f ≥ 0`,
`E_x[f(Φ_{τ_A}); τ_A < ∞] = ∫_A f(y) U_A(x, dy)`. -/
theorem setLIntegral_firstReturn_eq_tabooPotKernel (P : Kernel X X) [IsMarkovKernel P]
    {A : Set X} (hA : MeasurableSet A) (x : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, f (stoppedState (firstReturn A) ω) ∂pathKernel P x =
      ∫⁻ y in A, f y ∂tabooPotKernel P hA x := by
  have hτ := (proposition_3_4_4 (X := X) hA).1
  have hpiece : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | firstReturn A ω = WithTop.some (n + 1)} :=
    fun n => measurableSet_firstReturn_eq hA (n + 1)
  have hset : {ω : ℕ → X | firstReturn A ω ≠ ⊤} =
      ⋃ n : ℕ, {ω | firstReturn A ω = WithTop.some (n + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 h
      have h1 := one_le_firstReturn A ω
      rw [← hm] at h1
      have h1' : 1 ≤ m := WithTop.coe_le_coe.1 h1
      exact ⟨m - 1, by rw [← hm, show m - 1 + 1 = m by omega]⟩
    · rintro ⟨n, hn⟩; rw [hn]; exact WithTop.coe_ne_top
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ =>
      {ω : ℕ → X | firstReturn A ω = WithTop.some (n + 1)}) := fun i j hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (by
      have := hi.symm.trans hj
      exact Nat.succ_injective (WithTop.coe_inj.1 this))
  rw [hset, lintegral_iUnion hpiece hdisj]
  have hfA : Measurable (A.indicator f) := hf.indicator hA
  have hterm : ∀ n : ℕ, ∫⁻ ω in {ω | firstReturn A ω = WithTop.some (n + 1)},
      f (stoppedState (firstReturn A) ω) ∂pathKernel P x =
      ∫⁻ w, A.indicator f w ∂tabooKernel P hA n x := by
    intro n
    rw [← setLIntegral_le_firstReturn P hA n x hfA]
    have hle : MeasurableSet {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn A ω} :=
      measurableSet_le_firstReturn hA (n + 1)
    rw [← lintegral_indicator (hpiece n), ← lintegral_indicator hle]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : firstReturn A ω = WithTop.some (n + 1)
    · rw [indicator_of_mem (show ω ∈ {ω | firstReturn A ω = WithTop.some (n + 1)} from h1),
        indicator_of_mem (show ω ∈ {ω | WithTop.some (n + 1) ≤ firstReturn A ω} from h1.ge),
        stoppedState_of_eq h1, indicator_of_mem ((firstReturn_eq_iff A ω n).1 h1).2]
    · rw [indicator_of_notMem (show ω ∉ {ω | firstReturn A ω = WithTop.some (n + 1)} from h1)]
      by_cases h2 : WithTop.some (n + 1) ≤ firstReturn A ω
      · rw [indicator_of_mem (show ω ∈ {ω | WithTop.some (n + 1) ≤ firstReturn A ω} from h2),
          indicator_of_notMem fun hA' => h1 ((firstReturn_eq_iff A ω n).2 ⟨h2, hA'⟩)]
      · rw [indicator_of_notMem (show ω ∉ {ω | WithTop.some (n + 1) ≤ firstReturn A ω} from h2)]
  simp_rw [hterm]
  rw [← lintegral_indicator hA]
  change _ = ∫⁻ w, A.indicator f w ∂(Measure.sum fun n => tabooKernel P hA n x)
  rw [lintegral_sum_measure]

/-- **(9.2)** in kernel form (MT p. 199): `Q(x, A) = ∫_A U_A(x, dy) Q(y, A)`. -/
theorem harrisQ_eq_tabooPotKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    harrisQ P A x = ∫⁻ y in A, harrisQ P A y ∂tabooPotKernel P hA x := by
  rw [harrisQ_eq_firstReturn P hA x,
    setLIntegral_firstReturn_eq_tabooPotKernel P hA x (measurable_harrisQ P hA)]

/-- `Q(x, A) = ∫ Pⁿ(x, dy) Q(y, A)`. -/
theorem harrisQ_eq_lintegral_pow (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) (n : ℕ) :
    harrisQ P A x = ∫⁻ y, harrisQ P A y ∂(P ^ n) x :=
  pathKernel_shiftInvariant_eq_pow P x n (measurableSet_ioSet hA) (isShiftInvariant_ioSet A)

/-- For any stopping time `ζ`, `Q(x, A) ≥ E_x[Q(Φ_ζ, A); ζ < ∞]`. -/
theorem harrisQ_ge_stopping (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) :
    ∫⁻ ω in {ω | τ ω ≠ ⊤}, harrisQ P A (stoppedState τ ω) ∂pathKernel P x ≤ harrisQ P A x := by
  have h := pathKernel_inter_ne_top_of_shiftInvariant P x hτ (measurableSet_ioSet hA)
    (isShiftInvariant_ioSet A)
  unfold harrisQ
  rw [← h]
  exact measure_mono inter_subset_left

/-! ### Occupation times along the first return -/

/-- `{η_A ≥ k}` is an event. -/
theorem measurableSet_le_occTime {A : Set X} (hA : MeasurableSet A) (k : ℝ≥0∞) :
    MeasurableSet {ω : ℕ → X | k ≤ occTime A ω} :=
  measurableSet_le measurable_const (measurable_occTime hA)

/-- **The first-entrance identity for occupation times**: `P_x(η_A ≥ k + 1) =
E_x[P_{Φ_{τ_A}}(η_A ≥ k); τ_A < ∞]`. -/
theorem pathKernel_occTime_ge_succ (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) (k : ℝ≥0∞) :
    pathKernel P x {ω | k + 1 ≤ occTime A ω} = ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
      pathKernel P (stoppedState (firstReturn A) ω) {ω | k ≤ occTime A ω} ∂pathKernel P x := by
  have hS := measurableSet_le_occTime hA k
  have hi : Measurable ({ω : ℕ → X | k ≤ occTime A ω}.indicator (1 : (ℕ → X) → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have h := lintegral_shiftAt_firstReturn P x hA hi
  simp_rw [lintegral_indicator_one hS] at h
  rw [← h]
  have hT := measurableSet_firstReturn_ne_top (X := X) hA
  have hτ := (proposition_3_4_4 (X := X) hA).1
  have hset : {ω : ℕ → X | k + 1 ≤ occTime A ω} = {ω | firstReturn A ω ≠ ⊤} ∩
      shiftAt (firstReturn A) ⁻¹' {ω | k ≤ occTime A ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    rcases eq_or_ne (firstReturn A ω) ⊤ with htop | hne
    · rw [occTime_of_firstReturn_top A htop]
      simp [htop]
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [occTime_of_firstReturn_eq A hm.symm, shiftAt_of_eq hm.symm, add_comm 1]
      simp only [hne, ne_eq, not_false_eq_true, true_and]
      exact ENNReal.add_le_add_iff_right ENNReal.one_ne_top
  have hpre : MeasurableSet (shiftAt (firstReturn A) ⁻¹' {ω : ℕ → X | k ≤ occTime A ω}) :=
    measurable_shiftAt hτ hS
  have e : ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, {ω : ℕ → X | k ≤ occTime A ω}.indicator 1
      (shiftAt (firstReturn A) ω) ∂pathKernel P x = ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤},
      (shiftAt (firstReturn A) ⁻¹' {ω : ℕ → X | k ≤ occTime A ω}).indicator 1 ω
        ∂pathKernel P x := rfl
  rw [hset, e, lintegral_indicator_one hpre, Measure.restrict_apply hpre, inter_comm]

omit [MeasurableSpace X] in
/-- If `τ_A(k) = t` then the chain has visited `A` at least `k` times by time `t`. -/
theorem le_occTimeN_of_returnTimeK (A : Set X) (k : ℕ) {ω : ℕ → X} {t : ℕ}
    (h : returnTimeK A k ω = WithTop.some t) : (k : ℝ≥0∞) ≤ occTimeN A t ω := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rcases hk : returnTimeK A k ω with _ | s
    · rw [returnTimeK_succ_of_top A hk] at h
      exact absurd h WithTop.top_ne_coe
    · have hs := returnTimeK_succ_of_eq A hk
      have hst : s + 1 ≤ t := by
        have := le_hittingAfter (u := fun n (ω : ℕ → X) => ω n) (s := A) (n := s + 1) ω
        rw [← hs, h] at this
        exact WithTop.coe_le_coe.1 this
      have htA : ω t ∈ A := returnTimeK_mem A h
      calc ((k + 1 : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) + 1 := by push_cast; ring
        _ ≤ occTimeN A s ω + 1 := by gcongr; exact ih hk
        _ ≤ occTimeN A t ω := occTimeN_add_one_le A ω (by omega) htA

omit [MeasurableSpace X] in
/-- `τ_A(k) < ∞` implies `η_A ≥ k`. -/
theorem le_occTime_of_returnTimeK (A : Set X) (k : ℕ) {ω : ℕ → X}
    (h : returnTimeK A k ω ≠ ⊤) : (k : ℝ≥0∞) ≤ occTime A ω := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
  exact (le_occTimeN_of_returnTimeK A k ht.symm).trans (occTimeN_le_occTime A t ω)

/-! ### Harris recurrence -/

/-- A set `A` is **Harris recurrent** (MT p. 199) if `Q(x, A) = P_x(η_A = ∞) = 1` for every
`x ∈ A`. -/
def IsHarrisRecurrentSet (P : Kernel X X) [IsMarkovKernel P] (A : Set X) : Prop :=
  ∀ x ∈ A, harrisQ P A x = 1

/-- The chain is **Harris (recurrent)** (MT p. 199): it is `ψ`-irreducible, with `ψ` a maximal
irreducibility measure, and every set in `B⁺(X)` is Harris recurrent. -/
def IsHarris (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsMaximalIrreducibility P ψ ∧ ∀ A, MeasurableSet A → 0 < ψ A → IsHarrisRecurrentSet P A

/-- A Harris recurrent set is recurrent (MT p. 200): almost surely infinitely many visits give an
infinite expected number of visits. -/
theorem IsHarrisRecurrentSet.isRecurrentSet {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (h : IsHarrisRecurrentSet P A) : IsRecurrentSet P A := fun x hx =>
  potKernel_eq_top_of_harrisQ_pos P hA (by rw [h x hx]; exact one_pos)

end MeynTweedie.InvariantMeasures
