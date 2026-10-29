/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.Comparison

/-!
# Regular sets and the kernel `G_A` (MT §11.1, §11.3.2)

Copied for Chapter 13 from the Chapter 11 project
(`DriftRegularity/RegularSets.lean`), with the namespace changed to
`MeynTweedie.FErgodicity` and the imports to this project's modules.

Meyn and Tweedie, pp. 256, 258, 267–268, 270.

**Definitions.**
* `IsRegularSet P ψ C` (11.1), p. 256: `C` is measurable and `sup_{x ∈ C} E_x[τ_B] < ∞` for every
  `B ∈ B⁺(X)`; `IsRegularChain P ψ`: `X` is a countable union of regular sets;
  `IsRegularOn P ψ S`: `S` is a countable union of regular sets (the book's "`Φ` restricted to `S`
  is regular", for an absorbing `S`: hitting times from `S` do not depend on the restriction);
  `IsRegularMeasure P ψ μ` (p. 270): `E_μ[τ_B] < ∞` for every `B ∈ B⁺(X)`.
* `meanHitTime P A x = E_x[σ_A]`; `regV P A = V_A = 1 + E_·[σ_A]` (11.22);
  `gKernelFn P A f x = G_A(x, f) = E_x[Σ_{k=0}^{σ_A} f(Φ_k)]` (11.21);
  `tabooPotFn P A f x = U_A(x, f) = E_x[Σ_{k=1}^{τ_A} f(Φ_k)]`, with
  `tabooPotFn_indicator` (`U_A(x, 1_B) = U_A(x, B)`, the taboo potential kernel of (3.34)).

**Basic facts.**
* `IsRegularSet.subset`, `isRegularSet_empty`, `IsRegularSet.union`, `isRegularChain_iff`.
* `meanReturnTime_eq_one_add` (first-step analysis): `E_x[τ_A] = 1 + ∫ P(x, dy) E_y[σ_A]`;
  `meanHitTime_of_mem`, `meanHitTime_of_notMem`, `meanHitTime_le_meanReturnTime`;
  measurability of `E_·[τ_A]`, `E_·[σ_A]`.

**Theorem 11.3.5** (p. 267):
* (i) `theorem_11_3_5_i`: `P G_A = G_A − I + I_A U_A`, in the form
  `P G_A(x, f) + f(x) = G_A(x, f) + 1_A(x) U_A(x, f)`; `lintegral_gKernelFn`: `P G_A = U_A`;
* (ii) `theorem_11_3_5_ii`: `P V_A = V_A − 1` off `A` (11.23), and `P V_A(x) = E_x[τ_A]` on `A`;
  `regV_driftV2`: if `sup_{x ∈ C} E_x[τ_C] ≤ b`, `V_C` solves `PV + 1 ≤ V + b 1_C`;
* (iii) `theorem_11_3_5_iii`: `V_A − 1 = E_·[σ_A]` solves `PV ≤ V − 1` on `Aᶜ` (11.25), and is
  the pointwise minimal nonnegative measurable solution.

**Correction.** (11.24) states `P V_A(x) = E_x[τ_A] − 1` for `x ∈ A`. The correct value is
`E_x[τ_A]`: for `x ∈ A`, `V_A(x) = 1` and `P V_A(x) = E_x[1 + σ_A ∘ θ] = E_x[τ_A]`
(`theorem_11_3_5_ii`). On the one-point space, `A = X`: `P V_A = 1` while `E[τ_A] − 1 = 0`
(`eq_11_24_counterexample`). The consequences drawn from (11.24) (that `V_C` satisfies (V2) for a
regular `C ∈ B⁺(X)`) hold with `b = sup_C E_x[τ_C]`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Regular sets, chains and measures -/

/-- A set `C` is **regular** (11.1), MT p. 256: it is measurable and
`sup_{x ∈ C} E_x[τ_B] < ∞` for every `B ∈ B⁺(X)`. -/
def IsRegularSet (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (C : Set X) : Prop :=
  MeasurableSet C ∧ ∀ B, MeasurableSet B → 0 < ψ B →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P B x ≤ M

/-- The chain is **regular** (MT p. 256): `X` is covered by countably many regular sets. -/
def IsRegularChain (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsRegularSet P ψ (C n)) ∧ ⋃ n, C n = univ

/-- The chain is **regular on `S`**: `S` is a countable union of regular sets. For an absorbing
`S` this is the book's "`Φ` restricted to `S` is regular" (MT p. 258). -/
def IsRegularOn (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (S : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsRegularSet P ψ (C n)) ∧ ⋃ n, C n = S

/-- A measure `μ` is **regular** (MT p. 270): `E_μ[τ_B] = ∫ μ(dx) E_x[τ_B] < ∞` for every
`B ∈ B⁺(X)`. -/
def IsRegularMeasure (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (μ : Measure X) :
    Prop :=
  ∀ B, MeasurableSet B → 0 < ψ B → ∫⁻ x, meanReturnTime P B x ∂μ ≠ ∞

/-- A measurable subset of a regular set is regular. -/
theorem IsRegularSet.subset {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {C D : Set X}
    (hC : IsRegularSet P ψ C) (hD : MeasurableSet D) (hDC : D ⊆ C) : IsRegularSet P ψ D :=
  ⟨hD, fun B hB hψB => by
    obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
    exact ⟨M, hM, fun x hx => h x (hDC hx)⟩⟩

/-- The empty set is regular. -/
theorem isRegularSet_empty (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) :
    IsRegularSet P ψ ∅ :=
  ⟨MeasurableSet.empty, fun _ _ _ => ⟨0, ENNReal.zero_ne_top, fun _ hx => absurd hx (by simp)⟩⟩

/-- The union of two regular sets is regular. -/
theorem IsRegularSet.union {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {C D : Set X}
    (hC : IsRegularSet P ψ C) (hD : IsRegularSet P ψ D) : IsRegularSet P ψ (C ∪ D) :=
  ⟨hC.1.union hD.1, fun B hB hψB => by
    obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
    obtain ⟨M', hM', h'⟩ := hD.2 B hB hψB
    refine ⟨max M M', max_ne_top hM hM', fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact (h x hx).trans (le_max_left _ _)
    · exact (h' x hx).trans (le_max_right _ _)⟩

/-- A chain is regular iff it is regular on `X`. -/
theorem isRegularChain_iff (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) :
    IsRegularChain P ψ ↔ IsRegularOn P ψ univ := Iff.rfl

/-! ### Mean hitting times -/

/-- The mean hitting time `E_x[σ_A]` (`σ_A = ∞` counted as `∞`). -/
noncomputable def meanHitTime (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, ENat.toENNReal (firstHit A ω) ∂pathKernel P x

/-- `ω ↦ σ_A(ω)` is measurable into `[0, ∞]`. -/
theorem measurable_toENNReal_firstHit {A : Set X} (hA : MeasurableSet A) :
    Measurable fun ω : ℕ → X => ENat.toENNReal (firstHit A ω) :=
  measurable_toENNReal (measurableSet_lt_firstHit hA)

/-- `ω ↦ τ_A(ω)` is measurable into `[0, ∞]`. -/
theorem measurable_toENNReal_firstReturn {A : Set X} (hA : MeasurableSet A) :
    Measurable fun ω : ℕ → X => ENat.toENNReal (firstReturn A ω) :=
  measurable_toENNReal (measurableSet_lt_firstReturn hA)

omit [MeasurableSpace X] in
/-- `ℕ ∪ {∞} → [0, ∞]` on a natural number. -/
theorem toENNReal_some (n : ℕ) : ENat.toENNReal (WithTop.some n) = n := ENat.toENNReal_coe n

omit [MeasurableSpace X] in
/-- `ℕ ∪ {∞} → [0, ∞]` commutes with `· + 1`. -/
theorem toENNReal_add_one (e : WithTop ℕ) :
    ENat.toENNReal (e + 1 : WithTop ℕ) = ENat.toENNReal e + 1 := by
  cases e with
  | top =>
    simp only [WithTop.top_add]
    change ENat.toENNReal (⊤ : ℕ∞) = ENat.toENNReal (⊤ : ℕ∞) + 1
    rw [ENat.toENNReal_top, top_add]
  | coe m =>
    rw [show (WithTop.some m : WithTop ℕ) + 1 = WithTop.some (m + 1) from rfl, toENNReal_some,
      toENNReal_some, Nat.cast_succ]

/-- `x ↦ E_x[σ_A]` is measurable. -/
theorem measurable_meanHitTime (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : Measurable (meanHitTime P A) :=
  (measurable_toENNReal_firstHit hA).lintegral_kernel

/-- `x ↦ E_x[τ_A]` is measurable. -/
theorem measurable_meanReturnTime (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : Measurable (meanReturnTime P A) :=
  (measurable_toENNReal_firstReturn hA).lintegral_kernel

/-- `E_x[σ_A] = 0` for `x ∈ A`. -/
theorem meanHitTime_of_mem (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {x : X} (hx : x ∈ A) : meanHitTime P A x = 0 := by
  have := isMarkovKernel_pathKernel P
  have hm : MeasurableSet {ω : ℕ → X | ω 0 ∈ A} := measurable_pi_apply 0 hA
  have hnull : pathKernel P x {ω | ω 0 ∈ A}ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hm, pathKernel_zero_mem P x hA, indicator_of_mem hx,
      Pi.one_apply]
  have hae : (fun ω => ENat.toENNReal (firstHit A ω)) =ᵐ[pathKernel P x] fun _ => 0 := by
    refine measure_mono_null (fun ω hω => ?_) hnull
    intro h0
    apply hω
    change ENat.toENNReal (firstHit A ω) = 0
    rw [(firstHit_eq_zero_iff A ω).2 h0, toENNReal_some, Nat.cast_zero]
  rw [meanHitTime, lintegral_congr_ae hae, lintegral_zero]

/-- `E_x[σ_A] = E_x[τ_A]` for `x ∉ A`. -/
theorem meanHitTime_of_notMem (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {x : X} (hx : x ∉ A) : meanHitTime P A x = meanReturnTime P A x := by
  have hnull : pathKernel P x {ω | ω 0 ∈ A} = 0 := by
    rw [pathKernel_zero_mem P x hA, indicator_of_notMem hx]
  refine lintegral_congr_ae (measure_mono_null (fun ω hω => ?_) hnull)
  by_contra h0
  exact hω (congrArg ENat.toENNReal (firstHit_eq_firstReturn A (show ω 0 ∉ A from h0)))

/-- `σ_A ≤ τ_A`, so `E_x[σ_A] ≤ E_x[τ_A]`. -/
theorem meanHitTime_le_meanReturnTime (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) : meanHitTime P A x ≤ meanReturnTime P A x := by
  by_cases hx : x ∈ A
  · rw [meanHitTime_of_mem P hA hx]; exact zero_le
  · rw [meanHitTime_of_notMem P hA hx]

/-- **First-step analysis**: `E_x[τ_A] = 1 + ∫ P(x, dy) E_y[σ_A]`. -/
theorem meanReturnTime_eq_one_add (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    meanReturnTime P A x = 1 + ∫⁻ y, meanHitTime P A y ∂P x := by
  have := isMarkovKernel_pathKernel P
  have h : ∀ ω : ℕ → X, ENat.toENNReal (firstReturn A ω) =
      ENat.toENNReal (firstHit A (shift 1 ω)) + 1 := fun ω => by
    rw [firstReturn_eq_firstHit_shift, toENNReal_add_one]
  simp_rw [meanReturnTime, h]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, add_comm,
    lintegral_shift_one P x (measurable_toENNReal_firstHit hA)]
  rfl

/-! ### The kernels `G_A` and `U_A` -/

/-- `G_A(x, f) = E_x[Σ_{k=0}^{σ_A} f(Φ_k)]` (11.21), MT p. 267. -/
noncomputable def gKernelFn (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (f : X → ℝ≥0∞)
    (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, sumBefore (fun ω => firstHit A ω + 1) (fun k ω => f (ω k)) ω ∂pathKernel P x

/-- `U_A(x, f) = E_x[Σ_{k=1}^{τ_A} f(Φ_k)]`, the taboo potential of `f` (3.34). -/
noncomputable def tabooPotFn (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (f : X → ℝ≥0∞)
    (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, sumBefore (firstReturn A) (fun k ω => f (ω (k + 1))) ω ∂pathKernel P x

/-- `V_A(x) = G_A(x, X) = 1 + E_x[σ_A]` (11.22), MT p. 267. -/
noncomputable def regV (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) : ℝ≥0∞ :=
  1 + meanHitTime P A x

/-- `V_A` is measurable. -/
theorem measurable_regV (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) :
    Measurable (regV P A) :=
  measurable_const.add (measurable_meanHitTime P hA)

/-- `V_A = 1` on `A`. -/
theorem regV_of_mem (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {x : X} (hx : x ∈ A) : regV P A x = 1 := by
  rw [regV, meanHitTime_of_mem P hA hx, add_zero]

/-- `V_A ≤ 1 + E_·[τ_A]`. -/
theorem regV_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) (x : X) :
    regV P A x ≤ 1 + meanReturnTime P A x :=
  add_le_add le_rfl (meanHitTime_le_meanReturnTime P hA x)

/-- `{k < σ_A + 1}` is an event. -/
theorem measurableSet_lt_firstHit_add_one {A : Set X} (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < firstHit A ω + 1} := by
  rcases k with _ | k
  · have : {ω : ℕ → X | ((0 : ℕ) : WithTop ℕ) < firstHit A ω + 1} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact lt_of_lt_of_le (by norm_num) (le_add_self : (1 : WithTop ℕ) ≤ firstHit A ω + 1)
    rw [this]; exact MeasurableSet.univ
  · have : {ω : ℕ → X | ((k + 1 : ℕ) : WithTop ℕ) < firstHit A ω + 1} =
        {ω | (k : WithTop ℕ) < firstHit A ω} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [Nat.cast_succ, WithTop.add_lt_add_iff_right WithTop.one_ne_top]
    rw [this]; exact measurableSet_lt_firstHit hA k

/-- `U_A(x, 1_B) = U_A(x, B)`: `tabooPotFn` integrates the taboo potential kernel (3.34). -/
theorem tabooPotFn_indicator (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooPotFn P A (B.indicator 1) x = tabooPotKernel P hA x B := by
  rw [tabooPotKernel_eq_lintegral P hA x hB, tabooPotFn]
  refine lintegral_congr fun ω => tsum_congr fun n => ?_
  have hiff : (n : WithTop ℕ) < firstReturn A ω ↔ WithTop.some (n + 1) ≤ firstReturn A ω := by
    cases h : firstReturn A ω with
    | top => simp
    | coe m =>
      rw [Nat.cast_withTop]
      rw [WithTop.coe_lt_coe, WithTop.coe_le_coe]
      omega
  by_cases h1 : (n : WithTop ℕ) < firstReturn A ω
  · rw [indicator_of_mem (show ω ∈ {ω | (n : WithTop ℕ) < firstReturn A ω} from h1)]
    change B.indicator 1 (ω (n + 1)) = _
    by_cases h2 : ω (n + 1) ∈ B
    · rw [indicator_of_mem h2, indicator_of_mem (show ω ∈ {ω : ℕ → X | ω (n + 1) ∈ B} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω} from ⟨h2, hiff.1 h1⟩)]
      simp only [Pi.one_apply]
    · rw [indicator_of_notMem h2, indicator_of_notMem (show ω ∉ {ω : ℕ → X | ω (n + 1) ∈ B} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω} from fun h => h2 h.1)]
  · rw [indicator_of_notMem (show ω ∉ {ω | (n : WithTop ℕ) < firstReturn A ω} from h1),
      indicator_of_notMem (show ω ∉ {ω : ℕ → X | ω (n + 1) ∈ B} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω} from fun h => h1 (hiff.2 h.2))]

/-- `P G_A = U_A`: `∫ P(x, dy) G_A(y, f) = U_A(x, f)` (proof of Theorem 11.3.5). -/
theorem lintegral_gKernelFn (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∫⁻ y, gKernelFn P A f y ∂P x = tabooPotFn P A f x := by
  have hm : Measurable (sumBefore (fun ω : ℕ → X => firstHit A ω + 1) fun k ω => f (ω k)) :=
    measurable_sumBefore (measurableSet_lt_firstHit_add_one hA)
      fun k => hf.comp (measurable_pi_apply k)
  unfold gKernelFn tabooPotFn
  rw [← lintegral_shift_one P x hm]
  refine lintegral_congr fun ω => ?_
  have h := firstReturn_eq_firstHit_shift A ω
  unfold sumBefore
  refine tsum_congr fun k => ?_
  simp only [Set.indicator_apply, mem_ofPred_eq, ← h, shift]
  rw [add_comm 1 k]

omit [MeasurableSpace X] in
/-- `Σ_{k<τ+1} F_k = F_0 + Σ_{k<τ} F_{k+1}`. -/
theorem sumBefore_add_one {Ω : Type*} (τ : Ω → WithTop ℕ) (F : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    sumBefore (fun ω => τ ω + 1) F ω = F 0 ω + sumBefore τ (fun k => F (k + 1)) ω := by
  unfold sumBefore
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine congrArg₂ (· + ·) ?_ (tsum_congr fun k => ?_)
  · have h0 : ((0 : ℕ) : WithTop ℕ) < τ ω + 1 :=
      lt_of_lt_of_le (by norm_num) (le_add_self : (1 : WithTop ℕ) ≤ τ ω + 1)
    exact indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : WithTop ℕ) < τ ω + 1} from h0) _
  · have hiff : ((k + 1 : ℕ) : WithTop ℕ) < τ ω + 1 ↔ (k : WithTop ℕ) < τ ω := by
      rw [Nat.cast_succ, WithTop.add_lt_add_iff_right WithTop.one_ne_top]
    simp only [Set.indicator_apply, mem_ofPred_eq, hiff]

/-- `G_A(x, f) = f(x) + 1_{Aᶜ}(x) U_A(x, f)`. -/
theorem gKernelFn_eq (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    gKernelFn P A f x = f x + Aᶜ.indicator (tabooPotFn P A f) x := by
  have := isMarkovKernel_pathKernel P
  have hm : MeasurableSet {ω : ℕ → X | ω 0 ∈ A} := measurable_pi_apply 0 hA
  have hτm : Measurable (sumBefore (firstReturn A) fun k (ω : ℕ → X) => f (ω (k + 1))) :=
    measurable_sumBefore (measurableSet_lt_firstReturn hA)
      fun k => hf.comp (measurable_pi_apply (k + 1))
  simp_rw [gKernelFn, sumBefore_add_one]
  rw [lintegral_add_left (f := fun ω : ℕ → X => f (ω 0)) (hf.comp (measurable_pi_apply 0)),
    lintegral_coord_zero P x hf]
  refine congrArg (f x + ·) ?_
  by_cases hx : x ∈ A
  · have hnull : pathKernel P x {ω | ω 0 ∈ A}ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hm, pathKernel_zero_mem P x hA, indicator_of_mem hx,
        Pi.one_apply]
    rw [indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx)]
    have hae : (fun ω => sumBefore (firstHit A) (fun k (ω : ℕ → X) => f (ω (k + 1))) ω)
        =ᵐ[pathKernel P x] fun _ => 0 := by
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro h0
      apply hω
      change sumBefore (firstHit A) (fun k (ω : ℕ → X) => f (ω (k + 1))) ω = 0
      rw [sumBefore_eq_of_eq (τ' := fun _ => WithTop.some 0) ((firstHit_eq_zero_iff A ω).2 h0)]
      simp [sumBefore]
    rw [lintegral_congr_ae hae, lintegral_zero]
  · have hnull : pathKernel P x {ω | ω 0 ∈ A} = 0 := by
      rw [pathKernel_zero_mem P x hA, indicator_of_notMem hx]
    rw [indicator_of_mem (show x ∈ Aᶜ from hx), tabooPotFn]
    refine lintegral_congr_ae (measure_mono_null (fun ω hω => ?_) hnull)
    by_contra h0
    exact hω (sumBefore_eq_of_eq (firstHit_eq_firstReturn A (show ω 0 ∉ A from h0)) _)

/-- **Theorem 11.3.5 (i)** (MT p. 267): `P G_A = G_A − I + I_A U_A`, in the form
`P G_A(x, f) + f(x) = G_A(x, f) + 1_A(x) U_A(x, f)`. -/
theorem theorem_11_3_5_i (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∫⁻ y, gKernelFn P A f y ∂P x + f x = gKernelFn P A f x + A.indicator (tabooPotFn P A f) x := by
  rw [lintegral_gKernelFn P hA hf, gKernelFn_eq P hA hf, add_assoc,
    indicator_compl_add_self_apply, add_comm]

/-- `V_A = G_A(·, X)` (11.22). -/
theorem gKernelFn_one (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    gKernelFn P A (fun _ => 1) x = regV P A x := by
  have := isMarkovKernel_pathKernel P
  have h : ∀ ω : ℕ → X, sumBefore (fun ω => firstHit A ω + 1) (fun _ _ => (1 : ℝ≥0∞)) ω =
      1 + ENat.toENNReal (firstHit A ω) := fun ω =>
    (toENNReal_eq_sumBefore_one (fun ω => firstHit A ω + 1) ω).symm.trans
      ((toENNReal_add_one _).trans (add_comm _ _))
  simp_rw [gKernelFn, h]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  rfl

/-- `P V_A = E_·[τ_A]` everywhere. -/
theorem lintegral_regV (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (x : X) : ∫⁻ y, regV P A y ∂P x = meanReturnTime P A x := by
  rw [meanReturnTime_eq_one_add P hA x]
  simp_rw [regV]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- **Theorem 11.3.5 (ii)** (MT p. 267): `P V_A(x) = V_A(x) − 1` for `x ∉ A` (11.23), and
`P V_A(x) = E_x[τ_A]` for `x ∈ A` (the corrected (11.24)). -/
theorem theorem_11_3_5_ii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) :
    (∀ x ∉ A, ∫⁻ y, regV P A y ∂P x + 1 = regV P A x) ∧
      ∀ x ∈ A, ∫⁻ y, regV P A y ∂P x = meanReturnTime P A x := by
  refine ⟨fun x hx => ?_, fun x _ => lintegral_regV P hA x⟩
  rw [lintegral_regV P hA x, regV, meanHitTime_of_notMem P hA hx, add_comm]

/-- **The correction to (11.24).** For any chain, any state `x` and `A = X`,
`P V_A(x) = 1` while `E_x[τ_A] − 1 = 0`: the book's (11.24) fails. -/
theorem eq_11_24_counterexample (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    ∫⁻ y, regV P univ y ∂P x = 1 ∧ meanReturnTime P univ x - 1 = 0 := by
  have := isMarkovKernel_pathKernel P
  have h1 : ∀ ω : ℕ → X, firstReturn univ ω = 1 := fun ω => by
    rw [firstReturn_eq_firstHit_shift, (firstHit_eq_zero_iff univ _).2 (mem_univ _)]
    rfl
  have hm : meanReturnTime P univ x = 1 := by
    simp_rw [meanReturnTime, h1]
    rw [show ENat.toENNReal (1 : WithTop ℕ) = 1 from toENNReal_some 1 |>.trans Nat.cast_one,
      lintegral_const, measure_univ, mul_one]
  rw [lintegral_regV P MeasurableSet.univ x, hm]
  exact ⟨rfl, tsub_self 1⟩

/-- If `sup_{x ∈ C} E_x[τ_C] ≤ b`, then `V_C` solves (V2): `PV_C + 1 ≤ V_C + b 1_C`
(MT Theorem 11.3.5 (ii), p. 267, with the corrected (11.24)). -/
theorem regV_drift (P : Kernel X X) [IsMarkovKernel P] {C : Set X} (hC : MeasurableSet C)
    {b : ℝ≥0∞} (hb : ∀ x ∈ C, meanReturnTime P C x ≤ b) (x : X) :
    ∫⁻ y, regV P C y ∂P x + 1 ≤ regV P C x + C.indicator (fun _ => b) x := by
  by_cases hx : x ∈ C
  · rw [lintegral_regV P hC x, regV_of_mem P hC hx, indicator_of_mem hx, add_comm]
    exact add_le_add le_rfl (hb x hx)
  · rw [(theorem_11_3_5_ii P hC).1 x hx, indicator_of_notMem hx, add_zero]

/-- **Theorem 11.3.5 (iii)** (MT p. 267): `V = V_A − 1 = E_·[σ_A]` solves (11.25),
`PV ≤ V − 1` on `Aᶜ` (in the form `PV + 1 ≤ V`), and it is the pointwise minimal nonnegative
measurable solution: every such `W` has `E_x[σ_A] ≤ W(x)` for every `x`. -/
theorem theorem_11_3_5_iii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) :
    (∀ x ∉ A, ∫⁻ y, meanHitTime P A y ∂P x + 1 ≤ meanHitTime P A x) ∧
      ∀ W : X → ℝ≥0∞, Measurable W → (∀ x ∉ A, ∫⁻ y, W y ∂P x + 1 ≤ W x) →
        ∀ x, meanHitTime P A x ≤ W x := by
  refine ⟨fun x hx => ?_, fun W hW hdrift x => ?_⟩
  · rw [meanHitTime_of_notMem P hA hx, meanReturnTime_eq_one_add P hA x, add_comm]
  · have h := lintegral_sumBefore_firstHit_le P hA (z := fun _ => W) (ε := fun _ _ => 1)
      (fun _ => hW) (fun _ => measurable_const) (fun _ => hdrift) x
    simp_rw [← toENNReal_eq_sumBefore_one (firstHit A)] at h
    exact h

end MeynTweedie.FErgodicity
