/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.FNorm
import LimitTheorems.RegularityConverse
import LimitTheorems.CountableInvariant

/-!
# `f`-regular sets and the drift condition (V3) (MT §14.1.1, §14.2.1)

Meyn and Tweedie, pp. 339–344. Throughout `f : X → [0, ∞]` is measurable; the book's standing
`f ≥ 1` is a hypothesis where it is used.

**Sums along the path.**
* `fSumReturn P B f x = E_x[Σ_{k=0}^{τ_B − 1} f(Φ_k)]`, the quantity of (14.2), (14.10) and of the
  definition of `f`-regularity; `fSumReturn_one` (`= E_x[τ_B]` for `f ≡ 1`),
  `meanReturnTime_le_fSumReturn` (for `f ≥ 1`), `le_fSumReturn` (`f(x) ≤ E_x[Σ_{k<τ_B} f(Φ_k)]`),
  `fSumReturn_mono`, `fSumReturn_anti_set`.
* `sumBefore_add_le_of_shift`, `lintegral_sumBefore_le_stopping`: the **strong Markov bound**
  `E_x[Σ_{k<T} F_k] ≤ E_x[Σ_{k<ζ} F_k] + E_x[E_{Φ_ζ}[Σ_{k<T} F_k]; ζ < ∞]` for a stopping time `ζ`
  and a random time with `T ≤ t + T ∘ θᵗ`; `fSumReturn_le_stopping` is the case `T = τ_B` used
  for (14.12) and throughout the chapter.
* `lintegral_tabooPotKernel`: `∫ U_A(x, dy) f(y) = U_A(x, f) = E_x[Σ_{k=1}^{τ_A} f(Φ_k)]`.

**`π` through a set** (Theorem 10.4.9 for functions, the identity used in Proposition 14.1.1).
* `lintegral_eq_tabooPotFn`: `π(f) = ∫_A π(dy) U_A(y, f)`;
* `lintegral_eq_fSumReturn`: `π(f) = ∫_A π(dy) E_y[Σ_{k=0}^{τ_A − 1} f(Φ_k)]`.

**Definitions** (p. 339 and p. 343).
* `IsFRegularSet P ψ f C`: `sup_{x ∈ C} E_x[Σ_{k<τ_B} f(Φ_k)] < ∞` for every `B ∈ B⁺(X)`;
  `IsFRegularState`, `IsFRegularMeasure`, `IsFRegularChain` (a countable cover by `f`-regular
  sets), `IsFRegularOn` (the chain restricted to `S`).
* `DriftV3 P V f b C`: the `f`-modulated drift (V3), (14.16), `PV ≤ V − f + b 1_C`, written
  `PV + f ≤ V + b 1_C`; `DriftV3.driftV2` (for `f ≥ 1` it implies (V2)), and (14.17)
  (`driftV3_of_bounds`).

**Results.**
* **Proposition 14.1.1** (`proposition_14_1_1`, p. 339).
* **Lemma 14.2.1** (`lemma_14_2_1`, p. 343): `{V < ∞}` is absorbing and full.
* **Theorem 14.2.2** (`theorem_14_2_2`, the Comparison Theorem, p. 344), both inequalities.

**Corrections.** Proposition 14.1.1 needs `C ≠ ∅`: `∅` satisfies (14.10) vacuously with
`π(∅) = 0`, and a null recurrent chain is then a counterexample
(`proposition_14_1_1_counterexample`, the forward recurrence time chain of a renewal law with
infinite mean); the book's step "`C` is Harris recurrent, hence `C ∈ B⁺(X)`" needs `C ≠ ∅`. The
proposition also needs `f ≥ 1` for the positivity conclusion (the book's standing assumption).
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Sums before the return time -/

/-- `E_x[Σ_{k=0}^{τ_B − 1} f(Φ_k)]` (MT (14.2), p. 337), with `τ_B` the first return time. -/
noncomputable def fSumReturn (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (f : X → ℝ≥0∞)
    (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => f (ω k)) ω ∂pathKernel P x

/-- The path sum `Σ_{k<τ_B} f(Φ_k)` is measurable. -/
theorem measurable_sumBefore_firstReturn {B : Set X} (hB : MeasurableSet B) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (sumBefore (firstReturn B) fun k (ω : ℕ → X) => f (ω k)) :=
  measurable_sumBefore (measurableSet_lt_firstReturn hB) fun k => hf.comp (measurable_pi_apply k)

/-- `x ↦ E_x[Σ_{k<τ_B} f(Φ_k)]` is measurable. -/
theorem measurable_fSumReturn (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) : Measurable (fSumReturn P B f) :=
  (measurable_sumBefore_firstReturn hB hf).lintegral_kernel

/-- For `f ≡ 1` the sum is the mean return time: `E_x[Σ_{k<τ_B} 1] = E_x[τ_B]`. -/
theorem fSumReturn_one (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (x : X) :
    fSumReturn P B (fun _ => 1) x = meanReturnTime P B x :=
  (meanReturnTime_eq_sumBefore B x).symm

/-- `E_x[Σ_{k<τ_B} f(Φ_k)]` is monotone in `f`. -/
theorem fSumReturn_mono (P : Kernel X X) [IsMarkovKernel P] (B : Set X) {f g : X → ℝ≥0∞}
    (hfg : f ≤ g) (x : X) : fSumReturn P B f x ≤ fSumReturn P B g x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k ω => hfg (ω k)) ω

omit [MeasurableSpace X] in
/-- `τ_{B'} ≤ τ_B` for `B ⊆ B'`. -/
theorem firstReturn_anti {B B' : Set X} (h : B ⊆ B') (ω : ℕ → X) :
    firstReturn B' ω ≤ firstReturn B ω := by
  refine WithTop.forall_coe_le_iff_le.1 fun n hn => ?_
  exact (le_firstReturn_iff B ω n).2 fun j h1 h2 hj => (le_firstReturn_iff B' ω n).1 hn j h1 h2
    (h hj)

/-- `E_x[Σ_{k<τ_B} f(Φ_k)]` decreases when `B` increases. -/
theorem fSumReturn_anti_set (P : Kernel X X) [IsMarkovKernel P] {B B' : Set X} (h : B ⊆ B')
    (f : X → ℝ≥0∞) (x : X) : fSumReturn P B' f x ≤ fSumReturn P B f x :=
  lintegral_mono fun ω => sumBefore_mono_time (firstReturn_anti h) _ ω

/-- For `f ≥ 1`, `E_x[τ_B] ≤ E_x[Σ_{k<τ_B} f(Φ_k)]`. -/
theorem meanReturnTime_le_fSumReturn (P : Kernel X X) [IsMarkovKernel P] (B : Set X)
    {f : X → ℝ≥0∞} (hf : ∀ x, 1 ≤ f x) (x : X) : meanReturnTime P B x ≤ fSumReturn P B f x := by
  rw [← fSumReturn_one]; exact fSumReturn_mono P B hf x

omit [MeasurableSpace X] in
/-- The term `k = 0` of `Σ_{k<τ_B} F_k`. -/
theorem le_sumBefore_firstReturn (B : Set X) (F : ℕ → (ℕ → X) → ℝ≥0∞) (ω : ℕ → X) :
    F 0 ω ≤ sumBefore (firstReturn B) F ω := by
  have h0 : ((0 : ℕ) : WithTop ℕ) < firstReturn B ω :=
    lt_of_lt_of_le (by rw [Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 one_pos)
      (one_le_firstReturn B ω)
  unfold sumBefore
  calc F 0 ω = {ω | ((0 : ℕ) : WithTop ℕ) < firstReturn B ω}.indicator (F 0) ω :=
        (indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : WithTop ℕ) < firstReturn B ω} from h0) _).symm
    _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ => {ω | (k : WithTop ℕ) < firstReturn B ω}.indicator
          (F k) ω) 0

/-- `f(x) ≤ E_x[Σ_{k<τ_B} f(Φ_k)]`: the term `k = 0`. -/
theorem le_fSumReturn (P : Kernel X X) [IsMarkovKernel P] (B : Set X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (x : X) : f x ≤ fSumReturn P B f x := by
  rw [← lintegral_coord_zero P x hf]
  exact lintegral_mono fun ω => le_sumBefore_firstReturn B (fun k ω => f (ω k)) ω

/-! ### The strong Markov bound for sums -/

omit [MeasurableSpace X] in
/-- `Σ_{k<t+s} F_k = Σ_{k<t} F_k + Σ_{j<s} F_{t+j}` for a natural `t` and `s ∈ ℕ ∪ {∞}`. -/
theorem tsum_indicator_lt_add (F : ℕ → ℝ≥0∞) (t : ℕ) (s : WithTop ℕ) :
    ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ) + s}.indicator F k =
      ∑ k ∈ range t, F k + ∑' j : ℕ, {j : ℕ | (j : WithTop ℕ) < s}.indicator (fun j => F (t + j)) j
    := by
  have hsplit := Summable.sum_add_tsum_nat_add' (f := fun k : ℕ =>
    {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ) + s}.indicator F k) (k := t) ENNReal.summable
  rw [← hsplit]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (k : WithTop ℕ) < (t : WithTop ℕ) + s := by
      have : (k : WithTop ℕ) < t := by exact_mod_cast Finset.mem_range.1 hk
      exact lt_of_lt_of_le this le_self_add
    exact indicator_of_mem (show k ∈ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ) + s} from hk') _
  · refine tsum_congr fun j => ?_
    have hiff : ((j + t : ℕ) : WithTop ℕ) < (t : WithTop ℕ) + s ↔ (j : WithTop ℕ) < s := by
      rw [Nat.cast_add, add_comm (j : WithTop ℕ)]
      exact WithTop.add_lt_add_iff_left (WithTop.natCast_ne_top t)
    by_cases hj : (j : WithTop ℕ) < s
    · rw [indicator_of_mem (show j + t ∈ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ) + s} from
        hiff.2 hj), indicator_of_mem (show j ∈ {j : ℕ | (j : WithTop ℕ) < s} from hj), add_comm]
    · rw [indicator_of_notMem (show j + t ∉ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ) + s} from
        fun h => hj (hiff.1 h)), indicator_of_notMem (show j ∉ {j : ℕ | (j : WithTop ℕ) < s} from
        hj)]

omit [MeasurableSpace X] in
/-- `sumBefore` as a sum over `ℕ` of an indicator in the index. -/
theorem sumBefore_eq_tsum {Ω : Type*} (τ : Ω → WithTop ℕ) (F : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    sumBefore τ F ω = ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < τ ω}.indicator (fun k => F k ω) k := by
  unfold sumBefore
  refine tsum_congr fun k => ?_
  by_cases hk : (k : WithTop ℕ) < τ ω
  · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_mem (show k ∈ {k : ℕ | (k : WithTop ℕ) < τ ω} from hk)]
  · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_notMem (show k ∉ {k : ℕ | (k : WithTop ℕ) < τ ω} from hk)]

omit [MeasurableSpace X] in
/-- **Pathwise splitting at a time `t`.** If `T ω ≤ t + T(θᵗω)`, then
`Σ_{k<T} f(Φ_k) ≤ Σ_{k<t} f(Φ_k) + (Σ_{k<T} f(Φ_k)) ∘ θᵗ`. -/
theorem sumBefore_add_le_of_shift {T : (ℕ → X) → WithTop ℕ} {f : X → ℝ≥0∞} {ω : ℕ → X} {t : ℕ}
    (hT : T ω ≤ (t : WithTop ℕ) + T (shift t ω)) :
    sumBefore T (fun k ω => f (ω k)) ω ≤ ∑ k ∈ range t, f (ω k) +
      sumBefore T (fun k ω => f (ω k)) (shift t ω) := by
  have h1 := sumBefore_mono_time (τ := fun _ => T ω) (τ' := fun _ => (t : WithTop ℕ) +
    T (shift t ω)) (fun _ => hT) (fun k (_ : ℕ → X) => f (ω k)) ω
  rw [sumBefore_eq_tsum, sumBefore_eq_tsum, tsum_indicator_lt_add] at h1
  rw [sumBefore_eq_tsum, sumBefore_eq_tsum (fun ω => T ω)]
  refine h1.trans (add_le_add le_rfl (le_of_eq (tsum_congr fun j => ?_)))
  simp only [shift]

omit [MeasurableSpace X] in
/-- On `{ζ = t}`, `Σ_{k<ζ} F_k = Σ_{k<t} F_k`, for a general process `F`. -/
theorem sumBefore_of_eq' {Ω : Type*} {ζ : Ω → WithTop ℕ} {F : ℕ → Ω → ℝ≥0∞} {ω : Ω} {t : ℕ}
    (h : ζ ω = t) : sumBefore ζ F ω = ∑ k ∈ range t, F k ω := by
  rw [sumBefore_eq_tsum, h, tsum_eq_sum (s := range t) fun k hk => indicator_of_notMem
    (show k ∉ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ)} from fun h' =>
      hk (Finset.mem_range.2 (by exact_mod_cast h'))) _]
  refine Finset.sum_congr rfl fun k hk => indicator_of_mem
    (show k ∈ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ)} from by
      exact_mod_cast Finset.mem_range.1 hk) _

omit [MeasurableSpace X] in
/-- On `{ζ = t}`, `Σ_{k<ζ} F_k = Σ_{k<t} F_k`. -/
theorem sumBefore_of_eq {ζ : (ℕ → X) → WithTop ℕ} {f : X → ℝ≥0∞} {ω : ℕ → X} {t : ℕ}
    (h : ζ ω = t) : sumBefore ζ (fun k ω => f (ω k)) ω = ∑ k ∈ range t, f (ω k) := by
  rw [sumBefore_eq_tsum, h, tsum_eq_sum (s := range t) fun k hk => indicator_of_notMem
    (show k ∉ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ)} from fun h' =>
      hk (Finset.mem_range.2 (by exact_mod_cast h'))) _]
  refine Finset.sum_congr rfl fun k hk => indicator_of_mem
    (show k ∈ {k : ℕ | (k : WithTop ℕ) < (t : WithTop ℕ)} from by
      exact_mod_cast Finset.mem_range.1 hk) _

omit [MeasurableSpace X] in
/-- `Σ_{k<T} F_k ≤ Σ_{k<∞} F_k`. -/
theorem sumBefore_le_top {Ω : Type*} (T : Ω → WithTop ℕ) (F : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    sumBefore T F ω ≤ sumBefore (fun _ => ⊤) F ω :=
  sumBefore_mono_time (fun _ => le_top) F ω

/-- **The strong Markov bound for sums.** Let `ζ` be a stopping time and `T` a random time with
`T ≤ t + T ∘ θᵗ` for every `t` (for instance a first return or first hitting time). Then
`E_x[Σ_{k<T} f(Φ_k)] ≤ E_x[Σ_{k<ζ} f(Φ_k)] + E_x[h(Φ_ζ); ζ < ∞]` with
`h(y) = E_y[Σ_{k<T} f(Φ_k)]`. -/
theorem lintegral_sumBefore_le_stopping (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {ζ : (ℕ → X) → WithTop ℕ} (hζ : IsStoppingTime (natFilt (X := X)) ζ)
    {T : (ℕ → X) → WithTop ℕ} (hTm : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < T ω})
    (hT : ∀ ω (t : ℕ), T ω ≤ (t : WithTop ℕ) + T (shift t ω)) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω, sumBefore T (fun k ω => f (ω k)) ω ∂pathKernel P x ≤
      ∫⁻ ω, sumBefore ζ (fun k ω => f (ω k)) ω ∂pathKernel P x +
        ∫⁻ ω in {ω | ζ ω ≠ ⊤}, ∫⁻ ω', sumBefore T (fun k ω => f (ω k)) ω'
          ∂pathKernel P (stoppedState ζ ω) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have hH : Measurable (sumBefore T fun k (ω : ℕ → X) => f (ω k)) :=
    measurable_sumBefore hTm fun k => hf.comp (measurable_pi_apply k)
  have hζm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < ζ ω} :=
    fun n => (natFilt (X := X)).le n _ (measurableSet_lt_of_isStoppingTime hζ n)
  have hS : Measurable (sumBefore ζ fun k (ω : ℕ → X) => f (ω k)) :=
    measurable_sumBefore hζm fun k => hf.comp (measurable_pi_apply k)
  have hT0 := measurableSet_ne_top hζ
  have hpt : ∀ ω, sumBefore T (fun k ω => f (ω k)) ω ≤ sumBefore ζ (fun k ω => f (ω k)) ω +
      {ω | ζ ω ≠ ⊤}.indicator (fun ω => sumBefore T (fun k ω => f (ω k)) (shiftAt ζ ω)) ω :=
    fun ω => by
    cases h : ζ ω with
    | top =>
      rw [indicator_of_notMem (show ω ∉ {ω | ζ ω ≠ ⊤} from by simp [h]), add_zero,
        sumBefore_eq_of_eq (τ := ζ) (τ' := fun _ => ⊤) h]
      exact sumBefore_le_top T _ ω
    | coe t =>
      rw [indicator_of_mem (show ω ∈ {ω | ζ ω ≠ ⊤} from by simp [h]), shiftAt_of_eq h,
        sumBefore_of_eq h]
      exact sumBefore_add_le_of_shift (hT ω t)
  calc ∫⁻ ω, sumBefore T (fun k ω => f (ω k)) ω ∂pathKernel P x
      ≤ ∫⁻ ω, (sumBefore ζ (fun k ω => f (ω k)) ω + {ω | ζ ω ≠ ⊤}.indicator
          (fun ω => sumBefore T (fun k ω => f (ω k)) (shiftAt ζ ω)) ω) ∂pathKernel P x :=
        lintegral_mono hpt
    _ = ∫⁻ ω, sumBefore ζ (fun k ω => f (ω k)) ω ∂pathKernel P x +
          ∫⁻ ω in {ω | ζ ω ≠ ⊤}, sumBefore T (fun k ω => f (ω k)) (shiftAt ζ ω)
            ∂pathKernel P x := by
        rw [lintegral_add_left hS, lintegral_indicator hT0]
    _ = _ := by
        have h := strong_markov_lintegral P (Measure.dirac x) hζ MeasurableSet.univ hH
        rw [pathMeasure_dirac, univ_inter] at h
        rw [h]

omit [MeasurableSpace X] in
/-- `τ_B ≤ t + τ_B ∘ θᵗ` in `ℕ ∪ {∞}`. -/
theorem firstReturn_le_add_shift (B : Set X) (ω : ℕ → X) (t : ℕ) :
    firstReturn B ω ≤ (t : WithTop ℕ) + firstReturn B (shift t ω) := by
  cases h : firstReturn B (shift t ω) with
  | top => rw [WithTop.add_top]; exact le_top
  | coe s =>
    have hs1 : 1 ≤ s := by
      have := one_le_firstReturn B (shift t ω)
      rw [h] at this
      exact WithTop.coe_le_coe.1 this
    have hmem : ω (t + s) ∈ B := (mem_of_firstReturn_eq h : shift t ω s ∈ B)
    refine (firstReturn_le_of_mem (A := B) (j := t + s) (by omega) hmem).trans (le_of_eq ?_)
    rfl

/-- **The strong Markov bound for `E_x[Σ_{k<τ_B} f(Φ_k)]`**: for a stopping time `ζ`,
`E_x[Σ_{k<τ_B} f] ≤ E_x[Σ_{k<ζ} f] + E_x[E_{Φ_ζ}[Σ_{k<τ_B} f]; ζ < ∞]`. -/
theorem fSumReturn_le_stopping (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {ζ : (ℕ → X) → WithTop ℕ} (hζ : IsStoppingTime (natFilt (X := X)) ζ) {B : Set X}
    (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) :
    fSumReturn P B f x ≤ ∫⁻ ω, sumBefore ζ (fun k ω => f (ω k)) ω ∂pathKernel P x +
      ∫⁻ ω in {ω | ζ ω ≠ ⊤}, fSumReturn P B f (stoppedState ζ ω) ∂pathKernel P x :=
  lintegral_sumBefore_le_stopping P x hζ (measurableSet_lt_firstReturn hB)
    (firstReturn_le_add_shift B) hf

/-- If `E_y[Σ_{k<τ_B} f] ≤ M` for `y ∈ A`, then
`E_x[Σ_{k<τ_B} f] ≤ E_x[Σ_{k<τ_A} f] + M` (the strong Markov property at `τ_A`). -/
theorem fSumReturn_le_add_of_forall_le (P : Kernel X X) [IsMarkovKernel P] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f)
    {M : ℝ≥0∞} (hM : ∀ y ∈ A, fSumReturn P B f y ≤ M) (x : X) :
    fSumReturn P B f x ≤ fSumReturn P A f x + M := by
  have := isMarkovKernel_pathKernel P
  refine (fSumReturn_le_stopping P x (proposition_3_4_4 hA).1 hB hf).trans
    (add_le_add le_rfl ?_)
  calc ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, fSumReturn P B f (stoppedState (firstReturn A) ω)
        ∂pathKernel P x ≤ ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, M ∂pathKernel P x := by
        refine setLIntegral_mono measurable_const fun ω hω => hM _ ?_
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
        rw [stoppedState_of_eq ht.symm]
        exact mem_of_firstReturn_eq ht.symm
    _ ≤ M := by
        rw [setLIntegral_const]
        exact mul_le_of_le_one_right' prob_le_one

omit [MeasurableSpace X] in
/-- `σ_B ≤ t + σ_B ∘ θᵗ`. -/
theorem firstHit_le_add_shift (B : Set X) (ω : ℕ → X) (t : ℕ) :
    firstHit B ω ≤ (t : WithTop ℕ) + firstHit B (shift t ω) := by
  cases h : firstHit B (shift t ω) with
  | top => rw [WithTop.add_top]; exact le_top
  | coe s =>
    have hmem : ω (t + s) ∈ B := by
      have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := B) (n := 0)
        (ω := shift t ω) (by
          change firstHit B (shift t ω) ≠ ⊤
          rw [h]; exact WithTop.coe_ne_top)
      change shift t ω (firstHit B (shift t ω)).untopA ∈ B at this
      rw [h] at this
      exact this
    exact (hittingAfter_le_of_mem (u := fun n (ω : ℕ → X) => ω n) (n := 0)
      (Nat.zero_le (t + s)) hmem).trans (le_of_eq rfl)

/-! ### The taboo potential of a function -/

/-- `∫ U_A(x, dy) f(y) = U_A(x, f) = E_x[Σ_{k=1}^{τ_A} f(Φ_k)]`. -/
theorem lintegral_tabooPotKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∫⁻ y, f y ∂tabooPotKernel P hA x = tabooPotFn P A f x := by
  rw [tabooPotKernel, Kernel.sum_apply, lintegral_sum_measure, tabooPotFn,
    lintegral_sumBefore _ (measurableSet_lt_firstReturn hA)
      (F := fun k (ω : ℕ → X) => f (ω (k + 1))) fun k => hf.comp (measurable_pi_apply (k + 1))]
  refine tsum_congr fun n => ?_
  rw [← map_restrict_le_firstReturn P hA n x, lintegral_map hf (measurable_pi_apply (n + 1))]
  congr 1
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  cases h : firstReturn A ω with
  | top => simp
  | coe m =>
    rw [Nat.cast_withTop, WithTop.coe_lt_coe, WithTop.coe_le_coe]
    omega

/-- `x ↦ U_A(x, f)` is measurable. -/
theorem measurable_tabooPotFn (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {f : X → ℝ≥0∞} (hf : Measurable f) : Measurable (tabooPotFn P A f) := by
  have : tabooPotFn P A f = fun x => ∫⁻ y, f y ∂tabooPotKernel P hA x :=
    funext fun x => (lintegral_tabooPotKernel P hA hf x).symm
  rw [this]
  exact hf.lintegral_kernel

omit [MeasurableSpace X] in
/-- The pathwise identity behind the two forms of (10.31):
`Σ_{k<τ_A} f(Φ_k) + Σ_{k<τ_A} (f 1_A)(Φ_{k+1}) = f(Φ₀) + Σ_{k<τ_A} f(Φ_{k+1})`; the middle sum is
`f(Φ_{τ_A}) 1{τ_A < ∞}`. -/
theorem sumBefore_firstReturn_add (A : Set X) (f : X → ℝ≥0∞) (ω : ℕ → X) :
    sumBefore (firstReturn A) (fun k ω => f (ω k)) ω +
      sumBefore (firstReturn A) (fun k ω => A.indicator f (ω (k + 1))) ω =
    f (ω 0) + sumBefore (firstReturn A) (fun k ω => f (ω (k + 1))) ω := by
  cases h : firstReturn A ω with
  | top =>
    have h0 : sumBefore (firstReturn A) (fun k ω => A.indicator f (ω (k + 1))) ω = 0 := by
      refine (ENNReal.tsum_eq_zero.2 fun k => ?_)
      by_cases hk : (k : WithTop ℕ) < firstReturn A ω
      · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn A ω} from hk)]
        have hle : WithTop.some (k + 2) ≤ firstReturn A ω := by rw [h]; exact le_top
        have := (le_firstReturn_iff A ω (k + 2)).1 hle (k + 1) (by omega) (by omega)
        exact indicator_of_notMem this _
      · exact indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstReturn A ω} from hk) _
    rw [h0, add_zero, ← sumBefore_add_one (firstReturn A) (fun k ω => f (ω k)) ω]
    refine sumBefore_eq_of_eq ?_ _
    rw [h]; rfl
  | coe t =>
    have ht1 : 1 ≤ t := by
      have := one_le_firstReturn A ω; rw [h] at this; exact WithTop.coe_le_coe.1 this
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [sumBefore_of_eq' h, sumBefore_of_eq' h, sumBefore_of_eq' h]
    have hmid : ∑ k ∈ range (s + 1), A.indicator f (ω (k + 1)) = f (ω (s + 1)) := by
      rw [Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => ?_, zero_add,
        indicator_of_mem (mem_of_firstReturn_eq h)]
      have hle : WithTop.some (s + 1) ≤ firstReturn A ω := by rw [h]
      exact indicator_of_notMem ((le_firstReturn_iff A ω (s + 1)).1 hle (k + 1) (by omega)
        (by have := Finset.mem_range.1 hk; omega)) _
    rw [hmid, Finset.sum_range_succ', Finset.sum_range_succ, add_comm _ (f (ω 0)), add_assoc]

/-- `E_x[Σ_{k<τ_A} f(Φ_k)] + U_A(x, f 1_A) = f(x) + U_A(x, f)`. -/
theorem fSumReturn_add_tabooPotFn (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    fSumReturn P A f x + tabooPotFn P A (A.indicator f) x = f x + tabooPotFn P A f x := by
  have := isMarkovKernel_pathKernel P
  have h1 := measurable_sumBefore_firstReturn hA hf
  have h2 : Measurable (sumBefore (firstReturn A) fun k (ω : ℕ → X) => A.indicator f (ω (k + 1)))
    := measurable_sumBefore (measurableSet_lt_firstReturn hA)
      fun k => (hf.indicator hA).comp (measurable_pi_apply (k + 1))
  have h3 : Measurable (sumBefore (firstReturn A) fun k (ω : ℕ → X) => f (ω (k + 1))) :=
    measurable_sumBefore (measurableSet_lt_firstReturn hA)
      fun k => hf.comp (measurable_pi_apply (k + 1))
  have h4 := lintegral_add_left (μ := pathKernel P x) (f := fun ω : ℕ → X => f (ω 0))
    (hf.comp (measurable_pi_apply 0))
    (sumBefore (firstReturn A) fun k (ω : ℕ → X) => f (ω (k + 1)))
  rw [fSumReturn, tabooPotFn, tabooPotFn, ← lintegral_add_left h1, ← lintegral_coord_zero P x hf,
    ← h4]
  exact lintegral_congr fun ω => sumBefore_firstReturn_add A f ω

/-! ### The invariant measure through a set: Theorem 10.4.9 for functions -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.9 for functions**, (10.31): for a recurrent chain, an invariant measure `π`
and `A ∈ B⁺(X)` with `π(A) < ∞`, `π(f) = ∫_A π(dy) U_A(y, f)` for measurable `f ≥ 0`. -/
theorem lintegral_eq_tabooPotFn {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) {A : Set X}
    (hA : MeasurableSet A) (hψA : 0 < ψ A) (hπA : π A ≠ ∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂π = ∫⁻ y in A, tabooPotFn P A f y ∂π := by
  conv_lhs => rw [← theorem_10_4_9 hrec hπ hA hψA hπA]
  rw [minimalMeasure, ← lintegral_comp_kernel _ _ hf]
  exact lintegral_congr fun y => lintegral_tabooPotKernel P hA hf y

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.9 for functions**, the form `π(f) = ∫_A π(dy) E_y[Σ_{k=0}^{τ_A − 1} f(Φ_k)]`
(MT p. 246, used in the proof of Proposition 14.1.1). -/
theorem lintegral_eq_fSumReturn {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) {A : Set X}
    (hA : MeasurableSet A) (hψA : 0 < ψ A) (hπA : π A ≠ ∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂π = ∫⁻ y in A, fSumReturn P A f y ∂π := by
  have hfA : Measurable (A.indicator f) := hf.indicator hA
  have h1 := lintegral_eq_tabooPotFn hrec hπ hA hψA hπA hf
  have h2 := lintegral_eq_tabooPotFn hrec hπ hA hψA hπA hfA
  have hfs := measurable_fSumReturn P hA hf
  have hU := measurable_tabooPotFn P hA hf
  have hUA := measurable_tabooPotFn P hA hfA
  -- integrate `fSum + U_A(f 1_A) = f + U_A(f)` over `A`
  have hsum : ∫⁻ y in A, fSumReturn P A f y ∂π + ∫⁻ y, A.indicator f y ∂π =
      ∫⁻ y, A.indicator f y ∂π + ∫⁻ y, f y ∂π :=
    calc ∫⁻ y in A, fSumReturn P A f y ∂π + ∫⁻ y, A.indicator f y ∂π
        = ∫⁻ y in A, fSumReturn P A f y ∂π + ∫⁻ y in A, tabooPotFn P A (A.indicator f) y ∂π := by
          rw [h2]
      _ = ∫⁻ y in A, (fSumReturn P A f y + tabooPotFn P A (A.indicator f) y) ∂π :=
          (lintegral_add_left hfs _).symm
      _ = ∫⁻ y in A, (f y + tabooPotFn P A f y) ∂π :=
          setLIntegral_congr_fun hA fun y _ => fSumReturn_add_tabooPotFn P hA hf y
      _ = ∫⁻ y in A, f y ∂π + ∫⁻ y in A, tabooPotFn P A f y ∂π := lintegral_add_left hf _
      _ = ∫⁻ y, A.indicator f y ∂π + ∫⁻ y, f y ∂π := by rw [← h1, lintegral_indicator hA]
  by_cases hfin : ∫⁻ y, A.indicator f y ∂π = ∞
  · -- both sides are infinite
    have hle : ∫⁻ y, A.indicator f y ∂π ≤ ∫⁻ y in A, fSumReturn P A f y ∂π := by
      rw [lintegral_indicator hA]
      exact setLIntegral_mono hfs fun y _ => le_fSumReturn P A hf y
    have hle' : ∫⁻ y, A.indicator f y ∂π ≤ ∫⁻ y, f y ∂π :=
      lintegral_mono fun y => indicator_le_self A f y
    rw [hfin] at hle hle'
    rw [top_le_iff.1 hle, top_le_iff.1 hle']
  · rw [add_comm (∫⁻ y, A.indicator f y ∂π)] at hsum
    exact (ENNReal.add_left_inj hfin).1 hsum.symm

/-! ### `f`-regularity -/

/-- A set `C` is **`f`-regular** (MT p. 339): it is measurable and
`sup_{x ∈ C} E_x[Σ_{k<τ_B} f(Φ_k)] < ∞` for every `B ∈ B⁺(X)`. -/
def IsFRegularSet (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (C : Set X) : Prop :=
  MeasurableSet C ∧ ∀ B, MeasurableSet B → 0 < ψ B →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, fSumReturn P B f x ≤ M

/-- A state `x` is **`f`-regular** (MT p. 339): `E_x[Σ_{k<τ_B} f(Φ_k)] < ∞` for every
`B ∈ B⁺(X)`. -/
def IsFRegularState (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (x : X) : Prop :=
  ∀ B, MeasurableSet B → 0 < ψ B → fSumReturn P B f x ≠ ∞

/-- A measure `μ` is **`f`-regular** (MT p. 339): `E_μ[Σ_{k<τ_B} f(Φ_k)] < ∞` for every
`B ∈ B⁺(X)`. -/
def IsFRegularMeasure (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (μ : Measure X) : Prop :=
  ∀ B, MeasurableSet B → 0 < ψ B → ∫⁻ x, fSumReturn P B f x ∂μ ≠ ∞

/-- The chain is **`f`-regular** (MT p. 339): `X` is covered by countably many `f`-regular
sets. -/
def IsFRegularChain (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsFRegularSet P ψ f (C n)) ∧ ⋃ n, C n = univ

/-- The chain is **`f`-regular on `S`**: `S` is a countable union of `f`-regular sets (the
book's "`Φ` restricted to `S` is `f`-regular", for an absorbing `S`). -/
def IsFRegularOn (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (S : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsFRegularSet P ψ f (C n)) ∧ ⋃ n, C n = S

/-- A measurable subset of an `f`-regular set is `f`-regular. -/
theorem IsFRegularSet.subset {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} {C D : Set X} (hC : IsFRegularSet P ψ f C) (hD : MeasurableSet D)
    (hDC : D ⊆ C) : IsFRegularSet P ψ f D :=
  ⟨hD, fun B hB hψB => by
    obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
    exact ⟨M, hM, fun x hx => h x (hDC hx)⟩⟩

/-- An `f`-regular set is `g`-regular for `g ≤ f`. -/
theorem IsFRegularSet.mono {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f g : X → ℝ≥0∞} {C : Set X} (hC : IsFRegularSet P ψ f C) (hgf : g ≤ f) :
    IsFRegularSet P ψ g C :=
  ⟨hC.1, fun B hB hψB => by
    obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
    exact ⟨M, hM, fun x hx => (fSumReturn_mono P B hgf x).trans (h x hx)⟩⟩

/-- For `f ≥ 1`, an `f`-regular set is regular. -/
theorem IsFRegularSet.isRegularSet {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : ∀ x, 1 ≤ f x) {C : Set X} (hC : IsFRegularSet P ψ f C) :
    IsRegularSet P ψ C :=
  ⟨hC.1, fun B hB hψB => by
    obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
    exact ⟨M, hM, fun x hx => (meanReturnTime_le_fSumReturn P B hf x).trans (h x hx)⟩⟩

/-- The union of two `f`-regular sets is `f`-regular. -/
theorem IsFRegularSet.union {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} {C D : Set X} (hC : IsFRegularSet P ψ f C) (hD : IsFRegularSet P ψ f D) :
    IsFRegularSet P ψ f (C ∪ D) :=
  ⟨hC.1.union hD.1, fun B hB hψB => by
    obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
    obtain ⟨M', hM', h'⟩ := hD.2 B hB hψB
    refine ⟨max M M', max_ne_top hM hM', fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact (h x hx).trans (le_max_left _ _)
    · exact (h' x hx).trans (le_max_right _ _)⟩

/-- Every state of an `f`-regular set is `f`-regular. -/
theorem IsFRegularSet.isFRegularState {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} {C : Set X} (hC : IsFRegularSet P ψ f C) {x : X} (hx : x ∈ C) :
    IsFRegularState P ψ f x := fun B hB hψB => by
  obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
  exact ne_top_of_le_ne_top hM (h x hx)

/-- A state is `f`-regular iff its Dirac measure is. -/
theorem isFRegularMeasure_dirac_iff {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    IsFRegularMeasure P ψ f (Measure.dirac x) ↔ IsFRegularState P ψ f x := by
  refine forall_congr' fun B => ?_
  refine imp_congr_right fun hB => imp_congr_right fun _ => ?_
  rw [lintegral_dirac' _ (measurable_fSumReturn P hB hf)]

/-- On an `f`-regular set `C` (with `B⁺(X)` non-empty), `f` is bounded: `f(x) ≤ M`. -/
theorem IsFRegularSet.exists_le {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : Measurable f) {C : Set X} (hC : IsFRegularSet P ψ f C)
    (hψ : ψ ≠ 0) : ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, f x ≤ M := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨M, hM, h⟩ := hC.2 univ MeasurableSet.univ hψu
  exact ⟨M, hM, fun x hx => (le_fSumReturn P univ hf x).trans (h x hx)⟩

/-! ### The drift condition (V3) -/

/-- **The drift condition (V3)** (14.16), MT p. 343: `PV ≤ V − f + b 1_C`, written
`PV + f ≤ V + b 1_C` for `V : X → [0, ∞]`. -/
def DriftV3 (P : Kernel X X) (V f : X → ℝ≥0∞) (b : ℝ≥0∞) (C : Set X) : Prop :=
  ∀ x, ∫⁻ y, V y ∂P x + f x ≤ V x + C.indicator (fun _ => b) x

/-- For `f ≥ 1`, (V3) implies (V2). -/
theorem DriftV3.driftV2 {P : Kernel X X} {V f : X → ℝ≥0∞} {b : ℝ≥0∞} {C : Set X}
    (h : DriftV3 P V f b C) (hf : ∀ x, 1 ≤ f x) : DriftV2 P V b C := fun x =>
  (add_le_add le_rfl (hf x)).trans (h x)

/-- Under (V3), `PV ≤ V + b`. -/
theorem DriftV3.le_add {P : Kernel X X} {V f : X → ℝ≥0∞} {b : ℝ≥0∞} {C : Set X}
    (h : DriftV3 P V f b C) (x : X) : ∫⁻ y, V y ∂P x ≤ V x + b :=
  le_self_add.trans ((h x).trans (add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) x)))

/-- (V3) for `f'` follows from (V3) for `f ≥ f'`. -/
theorem DriftV3.mono {P : Kernel X X} {V f f' : X → ℝ≥0∞} {b : ℝ≥0∞} {C : Set X}
    (h : DriftV3 P V f b C) (hf : f' ≤ f) : DriftV3 P V f' b C := fun x =>
  (add_le_add le_rfl (hf x)).trans (h x)

/-- **(14.17)** (MT p. 343): the pair of bounds `f + PV ≤ V` off `C` and `f + PV ≤ b` on `C`
implies (V3). -/
theorem driftV3_of_bounds {P : Kernel X X} {V f : X → ℝ≥0∞} {b : ℝ≥0∞} {C : Set X}
    (hoff : ∀ x ∉ C, f x + ∫⁻ y, V y ∂P x ≤ V x) (hon : ∀ x ∈ C, f x + ∫⁻ y, V y ∂P x ≤ b) :
    DriftV3 P V f b C := fun x => by
  by_cases hx : x ∈ C
  · rw [indicator_of_mem hx, add_comm]; exact (hon x hx).trans le_add_self
  · rw [indicator_of_notMem hx, add_zero, add_comm]; exact hoff x hx

/-- Under (V3) with `b < ∞`, the set `{V < ∞}` is absorbing. -/
theorem isAbsorbing_finite_of_driftV3 {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ≥0∞}
    (hV : Measurable V) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (h : DriftV3 P V f b C) :
    IsAbsorbing P {x | V x ≠ ∞} := by
  intro x hx
  have hPV : ∫⁻ y, V y ∂P x ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx, hb⟩) (h.le_add x)
  have hae := ae_lt_top hV hPV
  have hm : MeasurableSet {y | V y ≠ ∞} := (measurableSet_singleton ∞).compl.preimage hV
  have h0 : P x {y | V y ≠ ∞}ᶜ = 0 := by
    have h1 : P x {y | ¬ V y < ∞} = 0 := ae_iff.1 hae
    have h2 : {y | V y ≠ ∞}ᶜ = {y | ¬ V y < ∞} := by
      ext y; simp [lt_top_iff_ne_top]
    rw [h2, h1]
  exact (prob_compl_eq_zero_iff hm).1 h0

/-- **Lemma 14.2.1** (MT p. 343): for a `φ`-irreducible chain, if (V3) holds (with `b < ∞`) for a
function `V` finite at some `x₀`, then `S_f = {V < ∞}` is absorbing and full. -/
theorem lemma_14_2_1 {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {V f : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞} (hb : b ≠ ∞)
    {C : Set X} (h : DriftV3 P V f b C) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    IsAbsorbing P {x | V x ≠ ∞} ∧ IsFull φ {x | V x ≠ ∞} := by
  have habs := isAbsorbing_finite_of_driftV3 hV hb h
  exact ⟨habs, proposition_4_2_3_i hφ ((measurableSet_singleton ∞).compl.preimage hV)
    ⟨x₀, hx₀⟩ habs⟩

/-! ### Theorem 14.2.2: the Comparison Theorem -/

/-- `E_x[g(Φ_k)] = Pᵏg(x)`. -/
theorem lintegral_coord_eq_pow (P : Kernel X X) [IsMarkovKernel P] (x : X) (k : ℕ)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (ω k) ∂pathKernel P x = ∫⁻ y, g y ∂(P ^ k : Kernel X X) x := by
  rw [← lintegral_map hg (measurable_pi_apply k), pathKernel_map_coord]

/-- `E_x[Σ_{k ≤ N} g(Φ_k)] = Σ_{k ≤ N} Pᵏg(x)`. -/
theorem lintegral_sumBefore_const (P : Kernel X X) [IsMarkovKernel P] (x : X) (N : ℕ)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, sumBefore (fun _ => ((N + 1 : ℕ) : WithTop ℕ)) (fun k ω => g (ω k)) ω ∂pathKernel P x
      = ∑ k ∈ range (N + 1), ∫⁻ y, g y ∂(P ^ k : Kernel X X) x := by
  simp_rw [sumBefore_of_eq (ζ := fun _ => ((N + 1 : ℕ) : WithTop ℕ)) (f := g) rfl]
  rw [lintegral_finsetSum (f := fun k (ω : ℕ → X) => g (ω k)) _
    fun k _ => hg.comp (measurable_pi_apply k)]
  exact Finset.sum_congr rfl fun k _ => lintegral_coord_eq_pow P x k hg

/-- **Theorem 14.2.2** (the Comparison Theorem, MT p. 344): if `PV ≤ V − f + s` for nonnegative
measurable `V`, `f`, `s` (in the form `PV + f ≤ V + s`), then for every `x`, `N` and stopping
time `τ`, (i) `Σ_{k ≤ N} E_x[f(Φ_k)] ≤ V(x) + Σ_{k ≤ N} E_x[s(Φ_k)]` and
(ii) `E_x[Σ_{k<τ} f(Φ_k)] ≤ V(x) + E_x[Σ_{k<τ} s(Φ_k)]`. -/
theorem theorem_14_2_2 (P : Kernel X X) [IsMarkovKernel P] {V f s : X → ℝ≥0∞}
    (hV : Measurable V) (hf : Measurable f) (hs : Measurable s)
    (hdrift : ∀ x, ∫⁻ y, V y ∂P x + f x ≤ V x + s x) (x : X) :
    (∀ N : ℕ, ∑ k ∈ range (N + 1), ∫⁻ y, f y ∂(P ^ k : Kernel X X) x ≤
      V x + ∑ k ∈ range (N + 1), ∫⁻ y, s y ∂(P ^ k : Kernel X X) x) ∧
    ∀ τ : (ℕ → X) → WithTop ℕ, IsStoppingTime (natFilt (X := X)) τ →
      ∫⁻ ω, sumBefore τ (fun k ω => f (ω k)) ω ∂pathKernel P x ≤
        V x + ∫⁻ ω, sumBefore τ (fun k ω => s (ω k)) ω ∂pathKernel P x := by
  have hc : ∀ τ : (ℕ → X) → WithTop ℕ, IsStoppingTime (natFilt (X := X)) τ →
      ∫⁻ ω, sumBefore τ (fun k ω => f (ω k)) ω ∂pathKernel P x ≤
        V x + ∫⁻ ω, sumBefore τ (fun k ω => s (ω k)) ω ∂pathKernel P x := fun τ hτ =>
    comparison_theorem_pathKernel P hV hf hs (D := univ) (fun y _ => hdrift y) hτ
      (fun _ _ _ => mem_univ _) x
  refine ⟨fun N => ?_, hc⟩
  have h := hc (fun _ => ((N + 1 : ℕ) : WithTop ℕ))
    (isStoppingTime_const (natFilt (X := X)) (N + 1))
  rw [lintegral_sumBefore_const P x N hf, lintegral_sumBefore_const P x N hs] at h
  exact h

/-! ### Proposition 14.1.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 14.1.1** (MT p. 339), corrected: let the chain be recurrent with a nonzero
invariant measure `π`, let `f ≥ 1`, and let `C` be a **non-empty** measurable set with
`π(C) < ∞` and `sup_{x ∈ C} E_x[Σ_{n<τ_C} f(Φ_n)] ≤ M < ∞` (14.10). Then `C ∈ B⁺(X)`,
`π(f) ≤ π(C) M < ∞`, and the chain is positive. -/
theorem proposition_14_1_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hC : MeasurableSet C)
    (hne : C.Nonempty) (hπC : π C ≠ ∞) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ x ∈ C, fSumReturn P C f x ≤ M) :
    0 < ψ C ∧ ∫⁻ x, f x ∂π ≤ π C * M ∧ ∫⁻ x, f x ∂π ≠ ∞ ∧ IsPositive P ψ := by
  have hψ := hrec.1
  -- `C` is Harris recurrent, hence in `B⁺(X)`
  have hL : ∀ x ∈ C, hitProb P C x = 1 := fun x hx =>
    hitProb_eq_one_of_meanReturnTime_ne_top hC (ne_top_of_le_ne_top hM
      ((meanReturnTime_le_fSumReturn P C hf1 x).trans (hbound x hx)))
  have hψC := (proposition_8_3_1_ii_irreducible P hψ hC hne hL).1
  have hrep := lintegral_eq_fSumReturn hrec hπ hC hψC hπC hf
  have hle : ∫⁻ x, f x ∂π ≤ π C * M := by
    rw [hrep]
    calc ∫⁻ y in C, fSumReturn P C f y ∂π ≤ ∫⁻ _ in C, M ∂π :=
          setLIntegral_mono measurable_const hbound
      _ = π C * M := by rw [setLIntegral_const, mul_comm]
  have hfin : ∫⁻ x, f x ∂π ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hπC hM) hle
  refine ⟨hψC, hle, hfin, hψ, ?_⟩
  -- `π(X) ≤ π(f) < ∞`, so the normalised `π` is an invariant probability
  have hu : π univ ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin ?_
    calc π univ = ∫⁻ _, (1 : ℝ≥0∞) ∂π := by rw [lintegral_one]
      _ ≤ ∫⁻ x, f x ∂π := lintegral_mono hf1
  have hu0 : π univ ≠ 0 := fun h => hπ0 (Measure.measure_univ_eq_zero.1 h)
  refine ⟨(π univ)⁻¹ • π, ⟨by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hu0 hu]⟩, ?_⟩
  change P ∘ₘ ((π univ)⁻¹ • π) = (π univ)⁻¹ • π
  rw [Measure.comp_smul, hπ.2]

/-- **The counterexample to Proposition 14.1.1 with `C = ∅`.** The forward recurrence time chain
of the renewal law `heavyRenewal` (infinite mean) is recurrent with a nonzero invariant measure
`π`; `C = ∅` has `π(C) = 0 < ∞` and satisfies (14.10) vacuously, for `f ≡ 1`; but the chain is
not positive. -/
theorem proposition_14_1_1_counterexample :
    haveI := isProbabilityMeasure_heavyRenewal
    haveI := isMarkovKernel_fwdRecKernel heavyRenewal
    IsRecurrentChain (fwdRecKernel heavyRenewal) Measure.count ∧
      IsInvariantMeasure (fwdRecKernel heavyRenewal) (fwdRecInv heavyRenewal) ∧
      fwdRecInv heavyRenewal ≠ 0 ∧ fwdRecInv heavyRenewal ∅ ≠ ∞ ∧
      (∀ x ∈ (∅ : Set ℕ), fSumReturn (fwdRecKernel heavyRenewal) ∅ (fun _ => 1) x ≤ 0) ∧
      ¬ IsPositive (fwdRecKernel heavyRenewal) Measure.count := by
  obtain ⟨hrec, -, -, hinv, htop, hnpos⟩ := theorem_10_0_1_counterexample
  refine ⟨hrec, hinv, fun h0 => by simp [h0] at htop, by simp, fun x hx => absurd hx
    (notMem_empty x), hnpos⟩

end MeynTweedie.LimitTheorems
