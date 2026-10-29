/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.FRegularSets

/-!
# The drift characterization of `f`-regularity (MT §14.2.1–14.2.2)

Meyn and Tweedie, pp. 344–346. `ψ` is a maximal irreducibility measure and the state space is
countably generated (petite sets are used through Proposition 5.5.5). `f : X → [0, ∞]` is
measurable, with `f ≥ 1` where the book's standing assumption is used.

**Tools.**
* `lintegral_sumBefore_indicator_le` (the bound (11.27) integrated, from the proof of
  Theorem 11.3.11): for a petite `C` and `B ∈ B⁺(X)` there is `c < ∞` with
  `E_x[Σ_{k<τ_B} 1_C(Φ_k)] ≤ c` for every `x`.
* `sumBefore_indicator_succ_le`, `tabooPotFn_indicator_le`:
  `U_A(x, f 1_A) = E_x[f(Φ_{τ_A}); τ_A < ∞]` is at most `sup_A f`; `tabooPotFn_le`:
  `U_A(x, f) ≤ E_x[Σ_{k<τ_A} f(Φ_k)] + sup_A f`;
  `gKernelFn_le`: `G_A(x, f) ≤ f(x) + E_x[Σ_{k<τ_A} f(Φ_k)] + sup_A f`.
* `driftV3_gKernelFn`: if `U_C(·, f) ≤ b` on `C`, then `V = G_C(·, f)` solves (V3) (from
  Theorem 11.3.5 (i)).

**Results.**
* **Theorem 14.2.3** (p. 344): (i) `theorem_14_2_3_i`, under (V3) with `C` petite, every
  `B ∈ B⁺(X)` has `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ V(x) + c(B)`, and `theorem_14_2_3_i_fRegular`: every
  set on which `V` is bounded is `f`-regular; `isFRegularMeasure_of_driftV3`: every `λ` with
  `λ(V) < ∞` is `f`-regular (MT p. 350); (ii) `theorem_14_2_3_ii`, an `f`-regular `C ∈ B⁺(X)` is
  petite and `V = G_C(·, f)` solves (V3), bounded on every `f`-regular set.
* **Theorem 14.2.4** (`theorem_14_2_4`, p. 345), corrected: `C` is petite, non-empty and has
  `sup_{x ∈ C} E_x[Σ_{k<τ_C} f(Φ_k)] < ∞` (14.19) iff `C` is `f`-regular and `C ∈ B⁺(X)`.
* **Theorem 14.2.5** (`theorem_14_2_5`, p. 346): from an `f`-regular `C ∈ B⁺(X)`, the sets
  `S_f(n) = {G_C(·, f) ≤ n}` are `f`-regular and increasing, and their union `S_f` is full and
  absorbing, with the chain `f`-regular on it (the decomposition (14.20)).
* **Theorem 14.2.6** (`theorem_14_2_6`, p. 346): the chain is `f`-regular iff (V3) holds for a
  petite set and an everywhere finite `V`; every sublevel set of such a `V` is `f`-regular
  (`theorem_14_2_6_sublevel`).
* **Theorem 14.2.7** (`theorem_14_2_7`, p. 346): the chain is `f`-regular iff some petite `C`
  has `E_x[Σ_{k<τ_C} f(Φ_k)]` finite everywhere and bounded on `C`.

**Hypotheses.** The constant `b` in (V3) is finite and test functions are measurable, as in
Chapter 11. Theorems 14.2.3 (ii), 14.2.4, 14.2.5 use `f ≥ 1` (an `f`-regular set is then regular,
hence petite by Proposition 11.3.8).

**Corrections.** Theorem 14.2.4 (i) ⇒ (ii) fails for `C = ∅`, which is petite and satisfies
(14.19) vacuously but is not in `B⁺(X)` (`theorem_14_2_4_counterexample`), as for
Theorem 11.3.14. The book's proof uses that `C` is Harris recurrent, which needs `C ≠ ∅`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### Visits to a petite set before `τ_B` -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The occupation bound behind Theorem 11.3.11** (MT p. 270, (11.27) and Lemma 11.3.10): for a
petite set `C` and `B ∈ B⁺(X)` there is `c < ∞` with `E_x[Σ_{k<τ_B} 1_C(Φ_k)] ≤ c` for every
`x`. -/
theorem lintegral_sumBefore_indicator_le [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) {B : Set X}
    (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x,
      ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω ∂pathKernel P x ≤ c := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨a, ν, hpet⟩ := hC
  obtain ⟨b', ψb, hpet', hmax⟩ := proposition_5_5_5_i P hψ hpet
  have ht : 0 < ψb B := pos_iff_ne_zero.2 fun h0 => hψB.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψb B) 1 with hε₀
  obtain ⟨K, hK⟩ := exists_tail_le hpet'.2.1 hε0
  have hb1 : ∀ k, b' k ≤ 1 := fun k => hpet'.2.1 ▸ ENNReal.le_tsum k
  set w : ℕ → ℝ≥0∞ := fun i => if i < K then 1 else 0 with hwdef
  have hwK : ∀ y, ∫⁻ z, B.indicator 1 z ∂sampledKernel P w y =
      ∑ i ∈ Finset.range K, (P ^ i) y B := fun y => by
    rw [lintegral_indicator_one hB, sampledKernel_apply P w y hB,
      tsum_eq_sum (s := Finset.range K) fun i hi => by
        simp [hwdef, Finset.mem_range.not.1 hi]]
    exact Finset.sum_congr rfl fun i hi => by simp [hwdef, Finset.mem_range.1 hi]
  have hC1 : ∀ y, C.indicator 1 y ≤ ε₀⁻¹ * ∫⁻ z, B.indicator 1 z ∂sampledKernel P w y := by
    intro y
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy, Pi.one_apply, hwK]
      have hhead := le_sum_head P K y hB hεt hK h2 (hpet'.2.2.2 y hy B)
      have hsum : ε₀ ≤ ∑ i ∈ Finset.range K, (P ^ i) y B := hhead.trans
        (Finset.sum_le_sum fun k _ => mul_le_of_le_one_left' (hb1 k))
      calc (1 : ℝ≥0∞) = ε₀⁻¹ * ε₀ := (ENNReal.inv_mul_cancel hε0.ne' hεt).symm
        _ ≤ _ := mul_le_mul' le_rfl hsum
    · rw [indicator_of_notMem hy]; exact zero_le
  set c : ℝ≥0∞ := ε₀⁻¹ * ∑' i, w i * ((i : ℝ≥0∞) + 1) with hcdef
  have hc : c ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hε0.ne') ?_
    rw [tsum_eq_sum (s := Finset.range K) fun i hi => by
      simp [hwdef, Finset.mem_range.not.1 hi]]
    exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top (by simp [hwdef]; split_ifs <;> simp)
      (by simp)
  refine ⟨c, hc, fun x => ?_⟩
  calc ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω ∂pathKernel P x
      ≤ ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => ε₀⁻¹ *
          ∫⁻ z, B.indicator 1 z ∂sampledKernel P w (ω k)) ω ∂pathKernel P x :=
        lintegral_mono fun ω => sumBefore_mono _ (fun k ω => hC1 (ω k)) ω
    _ = ε₀⁻¹ * ∫⁻ ω, sumBefore (firstReturn B) (fun k ω =>
          ∫⁻ z, B.indicator 1 z ∂sampledKernel P w (ω k)) ω ∂pathKernel P x := by
        simp_rw [sumBefore_const_mul]
        exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hε0.ne')
    _ = ε₀⁻¹ * ∑' i, w i * ∫⁻ ω, sumBefore (firstReturn B)
          (fun k ω => B.indicator 1 (ω (k + i))) ω ∂pathKernel P x := by
        rw [lemma_11_3_10 P x (proposition_3_4_4 hB).1 w (measurable_one.indicator hB)]
    _ ≤ c := by
        refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl ?_)
        calc ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => B.indicator 1 (ω (k + i))) ω
              ∂pathKernel P x ≤ ∫⁻ _, ((i : ℝ≥0∞) + 1) ∂pathKernel P x :=
              lintegral_mono fun ω => by exact_mod_cast sumBefore_firstReturn_shift_le B i ω
          _ = (i : ℝ≥0∞) + 1 := by rw [lintegral_const, measure_univ, mul_one]

/-! ### Theorem 14.2.3 (i) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.3 (i)** (MT p. 344): if (V3) holds for a petite set `C`, then for every
`B ∈ B⁺(X)` there is `c(B) < ∞` with `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ V(x) + c(B)` for every `x`. -/
theorem theorem_14_2_3_i [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f) {b : ℝ≥0∞} (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite P C) (h : DriftV3 P V f b C) {B : Set X} (hB : MeasurableSet B)
    (hψB : 0 < ψ B) : ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x, fSumReturn P B f x ≤ V x + c := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨c, hc, hocc⟩ := lintegral_sumBefore_indicator_le hψ hC hB hψB
  refine ⟨b * c, ENNReal.mul_ne_top hb hc, fun x => ?_⟩
  have hcmp := comparison_theorem_pathKernel P hV hf (measurable_const.indicator hCm) (D := univ)
    (fun y _ => h y) (proposition_3_4_4 hB).1 (fun _ _ _ => mem_univ _) x
  have hs : ∀ ω : ℕ → X, sumBefore (firstReturn B) (fun k ω => C.indicator (fun _ => b) (ω k)) ω
      = b * sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω := fun ω => by
    rw [← sumBefore_const_mul]
    refine sumBefore_congr _ fun k _ => ?_
    by_cases hk : ω k ∈ C <;> simp [hk]
  simp_rw [hs] at hcmp
  rw [lintegral_const_mul _ (measurable_sumBefore (measurableSet_lt_firstReturn hB)
    (F := fun k ω => C.indicator 1 (ω k))
    fun k => (measurable_one.indicator hCm).comp (measurable_pi_apply k))] at hcmp
  exact hcmp.trans (add_le_add le_rfl (mul_le_mul' le_rfl (hocc x)))

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.3 (i)**, `f`-regularity (MT p. 344): under (V3) with `C` petite, every
measurable set on which `V` is bounded is `f`-regular. -/
theorem theorem_14_2_3_i_fRegular [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV3 P V f b C) {A : Set X}
    (hA : MeasurableSet A) {M : ℝ≥0∞} (hM : M ≠ ∞) (hVA : ∀ x ∈ A, V x ≤ M) :
    IsFRegularSet P ψ f A := by
  refine ⟨hA, fun B hB hψB => ?_⟩
  obtain ⟨c, hc, hbound⟩ := theorem_14_2_3_i hψ hV hf hb hC h hB hψB
  exact ⟨M + c, ENNReal.add_ne_top.2 ⟨hM, hc⟩, fun x hx =>
    (hbound x).trans (add_le_add (hVA x hx) le_rfl)⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- Under (V3) with `C` petite, every state with `V(x) < ∞` is `f`-regular. -/
theorem isFRegularState_of_driftV3 [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV3 P V f b C) {x : X}
    (hx : V x ≠ ∞) : IsFRegularState P ψ f x := fun B hB hψB => by
  obtain ⟨c, hc, hbound⟩ := theorem_14_2_3_i hψ hV hf hb hC h hB hψB
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx, hc⟩) (hbound x)

variable [MeasurableSpace.CountablyGenerated X] in
/-- (MT p. 350) If (V3) holds for a petite set and `λ(V) < ∞` for a probability `λ`, then `λ` is
`f`-regular. -/
theorem isFRegularMeasure_of_driftV3 [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV3 P V f b C)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμV : ∫⁻ x, V x ∂μ ≠ ∞) :
    IsFRegularMeasure P ψ f μ := by
  intro B hB hψB
  obtain ⟨c, hc, hbound⟩ := theorem_14_2_3_i hψ hV hf hb hC h hB hψB
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμV, hc⟩) ?_
  calc ∫⁻ x, fSumReturn P B f x ∂μ ≤ ∫⁻ x, (V x + c) ∂μ := lintegral_mono hbound
    _ = ∫⁻ x, V x ∂μ + c := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-! ### The kernel `G_C(·, f)` as a solution of (V3) -/

omit [MeasurableSpace X] in
/-- `Σ_{k<τ_A} (f 1_A)(Φ_{k+1}) ≤ sup_A f`: only the visit at `τ_A` contributes. -/
theorem sumBefore_indicator_succ_le {A : Set X} {f : X → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : ∀ y ∈ A, f y ≤ M) (ω : ℕ → X) :
    sumBefore (firstReturn A) (fun k ω => A.indicator f (ω (k + 1))) ω ≤ M := by
  cases h : firstReturn A ω with
  | top =>
    refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun k => ?_) zero_le
    by_cases hk : (k : WithTop ℕ) < firstReturn A ω
    · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn A ω} from hk)]
      have hle : WithTop.some (k + 2) ≤ firstReturn A ω := by rw [h]; exact le_top
      exact indicator_of_notMem ((le_firstReturn_iff A ω (k + 2)).1 hle (k + 1) (by omega)
        (by omega)) _
    · exact indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstReturn A ω} from hk) _
  | coe t =>
    have ht1 : 1 ≤ t := by
      have := one_le_firstReturn A ω; rw [h] at this; exact WithTop.coe_le_coe.1 this
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [sumBefore_of_eq' h, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => ?_, zero_add]
    · exact (indicator_le_self A f _).trans (hM _ (mem_of_firstReturn_eq h))
    · have hle : WithTop.some (s + 1) ≤ firstReturn A ω := by rw [h]
      exact indicator_of_notMem ((le_firstReturn_iff A ω (s + 1)).1 hle (k + 1) (by omega)
        (by have := Finset.mem_range.1 hk; omega)) _

/-- `U_A(x, f 1_A) ≤ sup_A f`. -/
theorem tabooPotFn_indicator_le [IsMarkovKernel P] {A : Set X} {f : X → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : ∀ y ∈ A, f y ≤ M) (x : X) : tabooPotFn P A (A.indicator f) x ≤ M := by
  have := isMarkovKernel_pathKernel P
  calc tabooPotFn P A (A.indicator f) x ≤ ∫⁻ _, M ∂pathKernel P x :=
        lintegral_mono fun ω => sumBefore_indicator_succ_le hM ω
    _ = M := by rw [lintegral_const, measure_univ, mul_one]

/-- `U_A(x, f) ≤ E_x[Σ_{k<τ_A} f(Φ_k)] + sup_A f`. -/
theorem tabooPotFn_le [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) {f : X → ℝ≥0∞}
    (hf : Measurable f) {M : ℝ≥0∞} (hM : ∀ y ∈ A, f y ≤ M) (x : X) :
    tabooPotFn P A f x ≤ fSumReturn P A f x + M :=
  calc tabooPotFn P A f x ≤ f x + tabooPotFn P A f x := le_add_self
    _ = fSumReturn P A f x + tabooPotFn P A (A.indicator f) x :=
        (fSumReturn_add_tabooPotFn P hA hf x).symm
    _ ≤ fSumReturn P A f x + M := add_le_add le_rfl (tabooPotFn_indicator_le hM x)

/-- `G_A(x, f) ≤ f(x) + E_x[Σ_{k<τ_A} f(Φ_k)] + sup_A f`. -/
theorem gKernelFn_le [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) {f : X → ℝ≥0∞}
    (hf : Measurable f) {M : ℝ≥0∞} (hM : ∀ y ∈ A, f y ≤ M) (x : X) :
    gKernelFn P A f x ≤ f x + (fSumReturn P A f x + M) := by
  rw [gKernelFn_eq P hA hf x]
  exact add_le_add le_rfl ((indicator_le_self _ _ x).trans (tabooPotFn_le hA hf hM x))

/-- `G_A(x, f) ≤ 2 E_x[Σ_{k<τ_A} f(Φ_k)] + sup_A f`. -/
theorem gKernelFn_le_two_mul [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {f : X → ℝ≥0∞} (hf : Measurable f) {M : ℝ≥0∞} (hM : ∀ y ∈ A, f y ≤ M) (x : X) :
    gKernelFn P A f x ≤ 2 * fSumReturn P A f x + M := by
  refine (gKernelFn_le hA hf hM x).trans ?_
  rw [two_mul, ← add_assoc]
  exact add_le_add (add_le_add (le_fSumReturn P A hf x) le_rfl) le_rfl

/-- `G_A(·, f)` is measurable. -/
theorem measurable_gKernelFn [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {f : X → ℝ≥0∞} (hf : Measurable f) : Measurable (gKernelFn P A f) :=
  (measurable_sumBefore (measurableSet_lt_firstHit_add_one hA)
    fun k => hf.comp (measurable_pi_apply k)).lintegral_kernel

/-- `G_A(x, f) = f(x)` for `x ∈ A`. -/
theorem gKernelFn_of_mem [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) {f : X → ℝ≥0∞}
    (hf : Measurable f) {x : X} (hx : x ∈ A) : gKernelFn P A f x = f x := by
  rw [gKernelFn_eq P hA hf x, indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx), add_zero]

/-- **`G_C(·, f)` solves (V3)** (Theorem 11.3.5 (i)): if `U_C(x, f) ≤ b` for `x ∈ C`, then
`P G_C(·, f) + f ≤ G_C(·, f) + b 1_C`. -/
theorem driftV3_gKernelFn [IsMarkovKernel P] {C : Set X} (hC : MeasurableSet C) {f : X → ℝ≥0∞}
    (hf : Measurable f) {b : ℝ≥0∞} (hb : ∀ x ∈ C, tabooPotFn P C f x ≤ b) :
    DriftV3 P (gKernelFn P C f) f b C := fun x => by
  rw [theorem_11_3_5_i P hC hf x]
  refine add_le_add le_rfl ?_
  by_cases hx : x ∈ C
  · rw [indicator_of_mem hx, indicator_of_mem hx]; exact hb x hx
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-! ### Theorem 14.2.3 (ii) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.3 (ii)** (MT p. 344): for `f ≥ 1`, an `f`-regular set `C ∈ B⁺(X)` is petite,
`V = G_C(·, f)` solves (V3) for `C` with a finite `b`, and `V` is bounded on every `f`-regular
set. -/
theorem theorem_14_2_3_ii [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X}
    (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) :
    IsPetite P C ∧ ∃ b : ℝ≥0∞, b ≠ ∞ ∧ DriftV3 P (gKernelFn P C f) f b C ∧
      ∀ A, IsFRegularSet P ψ f A → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, gKernelFn P C f x ≤ M := by
  obtain ⟨M, hM, hbound⟩ := hC.2 C hC.1 hψC
  have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
  refine ⟨proposition_11_3_8 hψ (hC.isRegularSet hf1), M + M,
    ENNReal.add_ne_top.2 ⟨hM, hM⟩, driftV3_gKernelFn hC.1 hf fun x hx =>
      (tabooPotFn_le hC.1 hf hfC x).trans (add_le_add (hbound x hx) le_rfl), fun A hA => ?_⟩
  obtain ⟨M', hM', hA'⟩ := hA.2 C hC.1 hψC
  refine ⟨2 * M' + M, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hM', hM⟩,
    fun x hx => (gKernelFn_le_two_mul hC.1 hf hfC x).trans ?_⟩
  exact add_le_add (mul_le_mul' le_rfl (hA' x hx)) le_rfl

/-! ### Theorem 14.2.4 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.4** (MT p. 345), corrected: for `f ≥ 1` and a `ψ`-irreducible chain, a set `C`
is petite, non-empty and has `sup_{x ∈ C} E_x[Σ_{k<τ_C} f(Φ_k)] < ∞` (14.19) iff `C` is
`f`-regular and `C ∈ B⁺(X)`. -/
theorem theorem_14_2_4 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} :
    (IsPetite P C ∧ C.Nonempty ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, fSumReturn P C f x ≤ M) ↔
      (IsFRegularSet P ψ f C ∧ 0 < ψ C) := by
  constructor
  · rintro ⟨hpet, hne, M, hM, hbound⟩
    have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
    have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
    have hdrift : DriftV3 P (gKernelFn P C f) f (M + M) C := driftV3_gKernelFn hCm hf
      fun x hx => (tabooPotFn_le hCm hf hfC x).trans (add_le_add (hbound x hx) le_rfl)
    refine ⟨theorem_14_2_3_i_fRegular hψ (measurable_gKernelFn hCm hf) hf
      (ENNReal.add_ne_top.2 ⟨hM, hM⟩) hpet hdrift hCm hM fun x hx => ?_, ?_⟩
    · rw [gKernelFn_of_mem hCm hf hx]; exact hfC x hx
    · refine ((theorem_11_3_14 hψ).1 ⟨hpet, hne, M, hM, fun x hx => ?_⟩).2
      exact (meanReturnTime_le_fSumReturn P C hf1 x).trans (hbound x hx)
  · rintro ⟨hC, hψC⟩
    exact ⟨proposition_11_3_8 hψ (hC.isRegularSet hf1), nonempty_of_measure_ne_zero hψC.ne',
      hC.2 C hC.1 hψC⟩

/-- **The counterexample to Theorem 14.2.4 as stated** (`C = ∅`): `∅` is petite and satisfies
(14.19) vacuously, for every `f`, but `∅ ∉ B⁺(X)`. -/
theorem theorem_14_2_4_counterexample [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (x : X) :
    IsPetite P ∅ ∧ (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ y ∈ (∅ : Set X), fSumReturn P ∅ f y ≤ M) ∧
      ¬ 0 < ψ ∅ :=
  ⟨(theorem_11_3_14_counterexample (P := P) ψ x).1,
    ⟨0, ENNReal.zero_ne_top, fun y hy => absurd hy (notMem_empty y)⟩, by simp⟩

/-! ### Theorem 14.2.5 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.5** (MT p. 346): for `f ≥ 1`, if `C ∈ B⁺(X)` is `f`-regular, the sets
`S_f(n) = {G_C(·, f) ≤ n}` are `f`-regular and increasing, and their union
`S_f = {G_C(·, f) < ∞}` is full and absorbing; the chain is `f`-regular on `S_f`, and
`X = S_f ∪ N` with `N = S_fᶜ` a `ψ`-null set (14.20). -/
theorem theorem_14_2_5 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X}
    (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) :
    (∀ n : ℕ, IsFRegularSet P ψ f {x | gKernelFn P C f x ≤ n}) ∧
      Monotone (fun n : ℕ => {x | gKernelFn P C f x ≤ n}) ∧
      ⋃ n : ℕ, {x | gKernelFn P C f x ≤ n} = {x | gKernelFn P C f x ≠ ∞} ∧
      IsFull ψ {x | gKernelFn P C f x ≠ ∞} ∧ IsAbsorbing P {x | gKernelFn P C f x ≠ ∞} ∧
      IsFRegularOn P ψ f {x | gKernelFn P C f x ≠ ∞} := by
  obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_14_2_3_ii hψ hf hf1 hC hψC
  have hVm := measurable_gKernelFn hC.1 hf (P := P)
  obtain ⟨M, hM, hfC⟩ := hC.exists_le hf hψ.1
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have hc0 : gKernelFn P C f c ≠ ∞ := by
    rw [gKernelFn_of_mem hC.1 hf hc]; exact ne_top_of_le_ne_top hM (hfC c hc)
  have hsub : ∀ n : ℕ, IsFRegularSet P ψ f {x | gKernelFn P C f x ≤ n} := fun n =>
    theorem_14_2_3_i_fRegular hψ hVm hf hb hpet hdrift (measurableSet_le hVm measurable_const)
      (ENNReal.natCast_ne_top n) fun _ hx => hx
  have hU : ⋃ n : ℕ, {x | gKernelFn P C f x ≤ n} = {x | gKernelFn P C f x ≠ ∞} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hn, fun hx => ?_⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact ⟨n, hn.le⟩
  obtain ⟨habs, hfull⟩ := lemma_14_2_1 hψ.2.1 hVm hb hdrift hc0
  refine ⟨hsub, fun m n hmn x hx => ?_, hU, hfull, habs,
    fun n => {x | gKernelFn P C f x ≤ n}, hsub, hU⟩
  exact le_trans (show gKernelFn P C f x ≤ m from hx) (by exact_mod_cast hmn)

/-! ### Theorems 14.2.6 and 14.2.7 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.6**, sublevel sets (MT p. 346): under (V3) with a petite `C`, every sublevel
set `{V ≤ ℓ}`, `ℓ < ∞`, is `f`-regular. -/
theorem theorem_14_2_6_sublevel [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV3 P V f b C) {ℓ : ℝ≥0∞}
    (hℓ : ℓ ≠ ∞) : IsFRegularSet P ψ f {x | V x ≤ ℓ} :=
  theorem_14_2_3_i_fRegular hψ hV hf hb hC h (measurableSet_le hV measurable_const) hℓ
    fun _ hx => hx

/-- An `f`-regular chain (with `f ≥ 1`) has an `f`-regular set in `B⁺(X)`, and from it
`E_x[Σ_{k<τ_C} f(Φ_k)]` is finite for every `x`. -/
theorem IsFRegularChain.exists_pos [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hreg : IsFRegularChain P ψ f) :
    ∃ C : Set X, IsFRegularSet P ψ f C ∧ 0 < ψ C ∧ ∀ x, fSumReturn P C f x ≠ ∞ := by
  obtain ⟨Cs, hCs, hcov⟩ := hreg
  obtain ⟨n, hn⟩ := exists_pos_of_iUnion_eq_univ hψ.1 hcov
  refine ⟨Cs n, hCs n, hn, fun x => ?_⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
  obtain ⟨M, hM, hbound⟩ := (hCs m).2 (Cs n) (hCs n).1 hn
  exact ne_top_of_le_ne_top hM (hbound x hm)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.6** (MT p. 346): for `f ≥ 1` and a `ψ`-irreducible chain, the chain is
`f`-regular iff (V3) holds for a petite set `C`, a finite `b` and an everywhere finite `V`
(and then every sublevel set of `V` is `f`-regular, `theorem_14_2_6_sublevel`). -/
theorem theorem_14_2_6 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) :
    IsFRegularChain P ψ f ↔ ∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧
      Measurable V ∧ b ≠ ∞ ∧ (∀ x, V x ≠ ∞) ∧ DriftV3 P V f b C := by
  constructor
  · intro hreg
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    obtain ⟨n, hn⟩ := exists_pos_of_iUnion_eq_univ hψ.1 hcov
    obtain ⟨hpet, b, hb, hdrift, hbdd⟩ := theorem_14_2_3_ii hψ hf hf1 (hCs n) hn
    refine ⟨Cs n, gKernelFn P (Cs n) f, b, hpet, measurable_gKernelFn (hCs n).1 hf, hb,
      fun x => ?_, hdrift⟩
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
    obtain ⟨M, hM, hM'⟩ := hbdd (Cs m) (hCs m)
    exact ne_top_of_le_ne_top hM (hM' x hm)
  · rintro ⟨C, V, b, hC, hV, hb, hfin, h⟩
    refine ⟨fun n => {x | V x ≤ n}, fun n => theorem_14_2_6_sublevel hψ hV hf hb hC h
      (ENNReal.natCast_ne_top n), ?_⟩
    ext x
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hfin x)
    exact ⟨n, hn.le⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.7** (MT p. 346): for `f ≥ 1` and a `ψ`-irreducible chain, the chain is
`f`-regular iff there is a petite set `C` such that `E_x[Σ_{k<τ_C} f(Φ_k)]` is finite for every
`x` and uniformly bounded for `x ∈ C`. -/
theorem theorem_14_2_7 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) :
    IsFRegularChain P ψ f ↔ ∃ C : Set X, IsPetite P C ∧ (∀ x, fSumReturn P C f x ≠ ∞) ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, fSumReturn P C f x ≤ M := by
  constructor
  · intro hreg
    obtain ⟨C, hC, hψC, hfin⟩ := hreg.exists_pos hψ
    exact ⟨C, proposition_11_3_8 hψ (hC.isRegularSet hf1), hfin, hC.2 C hC.1 hψC⟩
  · rintro ⟨C, hC, hfin, M, hM, hbound⟩
    have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
    have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
    refine (theorem_14_2_6 hψ hf hf1).2 ⟨C, gKernelFn P C f, M + M, hC,
      measurable_gKernelFn hCm hf, ENNReal.add_ne_top.2 ⟨hM, hM⟩, fun x => ?_,
      driftV3_gKernelFn hCm hf fun x hx =>
        (tabooPotFn_le hCm hf hfC x).trans (add_le_add (hbound x hx) le_rfl)⟩
    refine ne_top_of_le_ne_top ?_ (gKernelFn_le_two_mul hCm hf hfC x)
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (hfin x), hM⟩

end MeynTweedie.VUniformErgodicity
