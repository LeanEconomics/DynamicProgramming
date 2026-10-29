/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.GeometricSums

/-!
# Kendall sets and `f`-geometrically regular sets (MT §15.2.1)

Meyn and Tweedie, §15.2.1, pp. 372–375. `τ_C(n)` is `returnTimeK C n`, the time of the `n`-th
visit to `C` after time `0`.

**Definitions** (p. 373).
* `IsKendall P A κ`: `A` is a **Kendall set of rate `κ > 1`**, `sup_{x ∈ A} E_x[κ^{τ_A}] < ∞`;
  `IsKendallSet P A`: for some `κ`.
* `IsFKendall P f A κ`: `A` is **`f`-Kendall of rate `κ`**, (15.22),
  `sup_{x ∈ A} E_x[Σ_{k<τ_A} f(Φ_k) κᵏ] < ∞`; `IsFKendallSet`: for some `κ`.
* `IsFGeomRegularSet P ψ f A`: `A` is **`f`-geometrically regular**: for every `B ∈ B⁺(X)` there
  is `r > 1` with `sup_{x ∈ A} E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] < ∞`.
* `IsFKendall.isKendall`, `IsFGeomRegularSet.isFRegularSet` (an `f`-geometrically regular set is
  `f`-regular, p. 373), `IsFGeomRegularSet.subset`, `IsFKendall.bounds` (on an `f`-Kendall set
  `f`, `E_x[κ^{τ_A}]` and `U_A^{(κ)}(x, f)` are bounded).

**The geometric trials argument** (the proof of Theorem 15.2.1, (15.24)–(15.27)).
* Pathwise: `returnTimeK_add_eq` (`τ_C(n + m) = τ_C(n) + τ_C(m) ∘ θ^{τ_C(n)}`),
  `firstReturn_eq_add_shift_of_lt` (`τ_B = t + τ_B ∘ θᵗ` on `{t < τ_B}`),
  `sumBefore_le_tsum_returnTimeK` (the sample-path bound of p. 374), and
  `natCast_le_sumBefore_indicator` (`m` visits to `C` before `τ_B` when `τ_C(m) < τ_B`).
* `lintegral_tpow_returnTimeK_le` ((15.24)), `measure_returnTimeK_lt_le` ((15.27)),
  `le_mul_sq_add_inv` (the bound `xy ≤ γⁿx² + γ⁻ⁿy²`).
* `geomTaboo_trials`: **the trials bound.** If `E_y[r₀^{τ_C}] ≤ M₀` and `U_C^{(r₀)}(y, f) ≤ M_f`
  on `C`, and `P_y(τ_C(m₀) < τ_B) ≤ q < 1` on `C`, then for some `r ∈ (1, r₀]` and `K < ∞`,
  `U_B^{(r)}(x, f) ≤ U_C^{(r₀)}(x, f) + K E_x[r₀^{τ_C}] + K` for every `x`. The book's choices
  `ρ < γ < 1` and `r ↓ 1` are made through the sequence `1 + 1/(n + 1)`.

**Results.**
* **Theorem 15.2.1** (`theorem_15_2_1`, p. 373), corrected: for `f ≥ 1`, `C` is petite, non-empty
  and `f`-Kendall iff `C` is `f`-geometrically regular and `C ∈ B⁺(X)`;
  `theorem_15_2_1_bound`: the bound behind it, `U_B^{(r)}(x, f) ≤ U_C^{(κ)}(x, f) + K E_x[κ^{τ_C}]
  + K` for every `x`.

**Correction.** Theorem 15.2.1 (i) ⇒ (ii) fails for `C = ∅`, which is petite and `f`-Kendall
vacuously but not in `B⁺(X)` (`theorem_15_2_1_counterexample`); the book's proof uses that a
Kendall set is Harris recurrent, which needs `C ≠ ∅`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Definitions -/

/-- `A` is a **Kendall set of rate `κ`** (MT p. 373): `κ > 1` and `sup_{x ∈ A} E_x[κ^{τ_A}] < ∞`. -/
def IsKendall (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (κ : ℝ≥0∞) : Prop :=
  MeasurableSet A ∧ 1 < κ ∧ κ ≠ ∞ ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, kendallMoment P A κ x ≤ M

/-- `A` is a **Kendall set** (MT p. 373): it is Kendall of some rate `κ > 1`. -/
def IsKendallSet (P : Kernel X X) [IsMarkovKernel P] (A : Set X) : Prop := ∃ κ, IsKendall P A κ

/-- `A` is **`f`-Kendall of rate `κ`** (MT (15.22), p. 373): `κ > 1` and
`sup_{x ∈ A} E_x[Σ_{k<τ_A} f(Φ_k) κᵏ] < ∞`. -/
def IsFKendall (P : Kernel X X) [IsMarkovKernel P] (f : X → ℝ≥0∞) (A : Set X) (κ : ℝ≥0∞) :
    Prop :=
  MeasurableSet A ∧ 1 < κ ∧ κ ≠ ∞ ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, geomSum P A κ f x ≤ M

/-- `A` is an **`f`-Kendall set** (MT p. 373): it is `f`-Kendall of some rate `κ > 1`. -/
def IsFKendallSet (P : Kernel X X) [IsMarkovKernel P] (f : X → ℝ≥0∞) (A : Set X) : Prop :=
  ∃ κ, IsFKendall P f A κ

/-- `A` is **`f`-geometrically regular** (MT p. 373): for every `B ∈ B⁺(X)` there is `r > 1` with
`sup_{x ∈ A} E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] < ∞`. -/
def IsFGeomRegularSet (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (A : Set X) : Prop :=
  MeasurableSet A ∧ ∀ B, MeasurableSet B → 0 < ψ B →
    ∃ r, 1 < r ∧ r ≠ ∞ ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, geomSum P B r f x ≤ M

/-- `f(x) ≤ E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]`: the term `k = 0`. -/
theorem le_geomSum (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞) {f : X → ℝ≥0∞}
    (hf : Measurable f) (x : X) : f x ≤ geomSum P B r f x := by
  rw [← lintegral_coord_zero P x hf]
  refine lintegral_mono fun ω => ?_
  have h := le_sumBefore_firstReturn B (fun k ω => r ^ k * f (ω k)) ω
  rwa [pow_zero, one_mul] at h

/-- `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` for `r ≥ 1`. -/
theorem fSumReturn_le_geomSum (P : Kernel X X) [IsMarkovKernel P] (B : Set X) {r : ℝ≥0∞}
    (hr : 1 ≤ r) (f : X → ℝ≥0∞) (x : X) : fSumReturn P B f x ≤ geomSum P B r f x := by
  rw [← geomSum_one]; exact geomSum_mono_r P B hr f x

/-- An `f`-geometrically regular set is `f`-regular (MT p. 373). -/
theorem IsFGeomRegularSet.isFRegularSet {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} {A : Set X} (h : IsFGeomRegularSet P ψ f A) : IsFRegularSet P ψ f A :=
  ⟨h.1, fun B hB hψB => by
    obtain ⟨r, hr, -, M, hM, hb⟩ := h.2 B hB hψB
    exact ⟨M, hM, fun x hx => (fSumReturn_le_geomSum P B hr.le f x).trans (hb x hx)⟩⟩

/-- A measurable subset of an `f`-geometrically regular set is `f`-geometrically regular. -/
theorem IsFGeomRegularSet.subset {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} {A D : Set X} (h : IsFGeomRegularSet P ψ f A) (hD : MeasurableSet D)
    (hDA : D ⊆ A) : IsFGeomRegularSet P ψ f D :=
  ⟨hD, fun B hB hψB => by
    obtain ⟨r, hr, hr', M, hM, hb⟩ := h.2 B hB hψB
    exact ⟨r, hr, hr', M, hM, fun x hx => hb x (hDA hx)⟩⟩

/-- An `f`-geometrically regular set is `g`-geometrically regular for `g ≤ f`. -/
theorem IsFGeomRegularSet.mono {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f g : X → ℝ≥0∞} {A : Set X} (h : IsFGeomRegularSet P ψ f A) (hgf : g ≤ f) :
    IsFGeomRegularSet P ψ g A :=
  ⟨h.1, fun B hB hψB => by
    obtain ⟨r, hr, hr', M, hM, hb⟩ := h.2 B hB hψB
    exact ⟨r, hr, hr', M, hM, fun x hx => (geomSum_mono_f P B r hgf x).trans (hb x hx)⟩⟩

/-- **The bounds on an `f`-Kendall set** (`f ≥ 1`): if `E_x[Σ_{k<τ_A} f(Φ_k) κᵏ] ≤ M` on `A`,
then on `A`, `f ≤ M`, `E_x[κ^{τ_A}] ≤ 1 + (κ − 1) M` and
`U_A^{(κ)}(x, f) ≤ M + M (1 + (κ − 1) M)`. -/
theorem fKendall_bounds (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {κ : ℝ≥0∞} (hκ : 1 < κ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {M : ℝ≥0∞} (hM : ∀ x ∈ A, geomSum P A κ f x ≤ M) :
    (∀ x ∈ A, f x ≤ M) ∧ (∀ x ∈ A, kendallMoment P A κ x ≤ 1 + (κ - 1) * M) ∧
      ∀ x ∈ A, geomTaboo P A κ f x ≤ M + M * (1 + (κ - 1) * M) := by
  have hfA : ∀ x ∈ A, f x ≤ M := fun x hx => (le_geomSum P A κ hf x).trans (hM x hx)
  have hK : ∀ x ∈ A, kendallMoment P A κ x ≤ 1 + (κ - 1) * M := fun x hx =>
    (kendallMoment_le_one_add P hA hκ hf1 x).trans (add_le_add le_rfl (mul_le_mul' le_rfl
      (hM x hx)))
  refine ⟨hfA, hK, fun x hx => ?_⟩
  exact (geomTaboo_le_geomSum_add P hA hκ hf hfA x).trans
    (add_le_add (hM x hx) (mul_le_mul' le_rfl (hK x hx)))

/-- An `f`-Kendall set (`f ≥ 1`) is Kendall of the same rate. -/
theorem IsFKendall.isKendall {P : Kernel X X} [IsMarkovKernel P] {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {A : Set X} {κ : ℝ≥0∞} (h : IsFKendall P f A κ) :
    IsKendall P A κ := by
  obtain ⟨hA, hκ, hκ', M, hM, hb⟩ := h
  exact ⟨hA, hκ, hκ', 1 + (κ - 1) * M, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hM⟩, (fKendall_bounds P hA hκ hf hf1 hb).2.1⟩

/-! ### Return times along the path -/

omit [MeasurableSpace X] in
/-- `k ≤ min{j ≥ n : Φⱼ ∈ A}` iff the path avoids `A` at the times `n ≤ j < k`. -/
theorem le_hittingAfter_iff' (A : Set X) (ω : ℕ → X) (n k : ℕ) :
    WithTop.some k ≤ hittingAfter (fun n (ω : ℕ → X) => ω n) A n ω ↔
      ∀ j, n ≤ j → j < k → ω j ∉ A := by
  rw [← not_lt, hittingAfter_lt_iff]
  simp only [Set.mem_Ico, not_exists, not_and]
  exact ⟨fun h j h1 h2 hj => h j ⟨h1, h2⟩ hj, fun h j hj => h j hj.1 hj.2⟩

omit [MeasurableSpace X] in
/-- `min{j ≥ t + 1 : Φⱼ ∈ A} = t + τ_A ∘ θᵗ`. -/
theorem hittingAfter_succ_eq_add (A : Set X) (t : ℕ) (ω : ℕ → X) :
    hittingAfter (fun n (ω : ℕ → X) => ω n) A (t + 1) ω =
      (t : WithTop ℕ) + firstReturn A (shift t ω) := by
  cases hs : firstReturn A (shift t ω) with
  | top => rw [WithTop.add_top]; exact (hittingAfter_succ_eq_top_iff A t ω).2 hs
  | coe s => rw [hittingAfter_succ_of_firstReturn_shift A hs]; rfl

omit [MeasurableSpace X] in
/-- `τ_A(k + 1) = τ_A(k) + τ_A ∘ θ^{τ_A(k)}` on `{τ_A(k) = t}`. -/
theorem returnTimeK_succ_eq' (A : Set X) {k t : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = (t : WithTop ℕ)) :
    returnTimeK A (k + 1) ω = (t : WithTop ℕ) + firstReturn A (shift t ω) := by
  rw [returnTimeK_succ_of_eq A h, hittingAfter_succ_eq_add]
  rfl

omit [MeasurableSpace X] in
/-- **`τ_A(k + m) = τ_A(k) + τ_A(m) ∘ θ^{τ_A(k)}`** on `{τ_A(k) = t}`. -/
theorem returnTimeK_add_eq (A : Set X) {k t : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = (t : WithTop ℕ)) (m : ℕ) :
    returnTimeK A (k + m) ω = (t : WithTop ℕ) + returnTimeK A m (shift t ω) := by
  induction m with
  | zero => rw [add_zero, h]; rfl
  | succ m ih =>
    rw [← add_assoc]
    cases hm : returnTimeK A (k + m) ω with
    | top =>
      rw [returnTimeK_succ_of_top A hm]
      rw [hm] at ih
      have h2 : returnTimeK A m (shift t ω) = ⊤ := by
        by_contra hne
        obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hne
        rw [← hs] at ih
        exact WithTop.top_ne_coe (ih.trans (by rfl : (t : WithTop ℕ) + WithTop.some s =
          WithTop.some (t + s)))
      rw [returnTimeK_succ_of_top A h2, WithTop.add_top]
    | coe s =>
      rw [hm] at ih
      cases hm' : returnTimeK A m (shift t ω) with
      | top => rw [hm', WithTop.add_top] at ih; exact absurd ih WithTop.coe_ne_top
      | coe u =>
        rw [hm'] at ih
        have hsu : s = t + u := WithTop.coe_inj.1 ih
        rw [returnTimeK_succ_eq' A hm, returnTimeK_succ_eq' A hm', shift_shift, ← add_assoc,
          ← Nat.cast_add, ← hsu]

omit [MeasurableSpace X] in
/-- `τ_A(k) ≤ τ_A(k + 1)`. -/
theorem returnTimeK_le_succ (A : Set X) (k : ℕ) (ω : ℕ → X) :
    returnTimeK A k ω ≤ returnTimeK A (k + 1) ω := by
  cases h : returnTimeK A k ω with
  | top => rw [returnTimeK_succ_of_top A h]
  | coe t => rw [returnTimeK_succ_eq' A h]; exact le_self_add

omit [MeasurableSpace X] in
/-- `k ↦ τ_A(k)` is monotone. -/
theorem returnTimeK_mono (A : Set X) (ω : ℕ → X) : Monotone fun k => returnTimeK A k ω :=
  monotone_nat_of_le_succ fun k => returnTimeK_le_succ A k ω

/-- `t < x` gives `t + 1 ≤ x` in `ℕ ∪ {∞}`. -/
theorem succ_le_of_lt_withTop {t : ℕ} {x : WithTop ℕ} (h : (t : WithTop ℕ) < x) :
    ((t + 1 : ℕ) : WithTop ℕ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe n => exact WithTop.coe_le_coe.2 (Nat.succ_le_of_lt (WithTop.coe_lt_coe.1 h))

omit [MeasurableSpace X] in
/-- **`τ_B = t + τ_B ∘ θᵗ` on `{t < τ_B}`.** -/
theorem firstReturn_eq_add_shift_of_lt (B : Set X) {ω : ℕ → X} {t : ℕ}
    (h : (t : WithTop ℕ) < firstReturn B ω) :
    firstReturn B ω = (t : WithTop ℕ) + firstReturn B (shift t ω) := by
  rw [← hittingAfter_succ_eq_add]
  refine withTop_eq_of_forall_le_iff fun k => ?_
  have hno : ∀ j, 1 ≤ j → j ≤ t → ω j ∉ B := fun j h1 h2 =>
    (le_firstReturn_iff B ω (t + 1)).1 (succ_le_of_lt_withTop h) j h1 (by omega)
  rw [le_firstReturn_iff, le_hittingAfter_iff']
  constructor
  · exact fun hk j hj1 hj2 => hk j (by omega) hj2
  · intro hk j hj1 hj2
    by_cases hjt : j ≤ t
    · exact hno j hj1 hjt
    · exact hk j (by omega) hj2

omit [MeasurableSpace X] in
/-- **`m` visits to `A` by time `τ_A(m)`**: if `τ_A(m) = t` then `Σ_{k ≤ t} 1_A(Φ_k) ≥ m`. -/
theorem natCast_le_sum_indicator_of_returnTimeK (A : Set X) {m t : ℕ} {ω : ℕ → X}
    (h : returnTimeK A m ω = (t : WithTop ℕ)) :
    (m : ℝ≥0∞) ≤ ∑ k ∈ range (t + 1), A.indicator 1 (ω k) := by
  induction m generalizing t with
  | zero => rw [Nat.cast_zero]; exact zero_le
  | succ m ih =>
    cases hm : returnTimeK A m ω with
    | top => rw [returnTimeK_succ_of_top A hm] at h; exact absurd h WithTop.top_ne_coe
    | coe s =>
      have hst := returnTimeK_succ_eq' A hm
      rw [h] at hst
      have hs1 : s + 1 ≤ t := by
        cases hu : firstReturn A (shift s ω) with
        | top => rw [hu, WithTop.add_top] at hst; exact absurd hst WithTop.coe_ne_top
        | coe u =>
          rw [hu] at hst
          have h1 := one_le_firstReturn A (shift s ω)
          rw [hu] at h1
          have h2 := WithTop.coe_le_coe.1 h1
          have h3 : (WithTop.some t : WithTop ℕ) = WithTop.some (s + u) := hst
          have h3 := WithTop.coe_inj.1 h3
          omega
      have hmem : ω t ∈ A := returnTimeK_mem A h
      calc ((m + 1 : ℕ) : ℝ≥0∞) = (m : ℝ≥0∞) + 1 := by push_cast; rfl
        _ ≤ ∑ k ∈ range (s + 1), A.indicator 1 (ω k) + A.indicator 1 (ω t) := by
            rw [indicator_of_mem hmem, Pi.one_apply]
            exact add_le_add (ih hm) le_rfl
        _ ≤ ∑ k ∈ range t, A.indicator 1 (ω k) + A.indicator 1 (ω t) :=
            add_le_add (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hs1)) le_rfl
        _ = ∑ k ∈ range (t + 1), A.indicator 1 (ω k) := (Finset.sum_range_succ _ _).symm

omit [MeasurableSpace X] in
/-- **Counting visits before `τ_B`**: `m 1{τ_C(m) < τ_B} ≤ Σ_{k<τ_B} 1_C(Φ_k)`. -/
theorem natCast_le_sumBefore_indicator (B C : Set X) (m : ℕ) {ω : ℕ → X}
    (h : returnTimeK C m ω < firstReturn B ω) :
    (m : ℝ≥0∞) ≤ sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h.ne_top
  have ht' : returnTimeK C m ω = (t : WithTop ℕ) := ht.symm
  refine (natCast_le_sum_indicator_of_returnTimeK C ht').trans ?_
  rw [ht'] at h
  rw [← sumBefore_of_eq' (ζ := fun _ : ℕ → X => ((t + 1 : ℕ) : WithTop ℕ)) (ω := ω)
    (F := fun k ω => C.indicator 1 (ω k)) rfl]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : ((k : ℕ) : WithTop ℕ) < ((t + 1 : ℕ) : WithTop ℕ)
  · rw [indicator_of_mem (show ω ∈ {ω : ℕ → X | ((k : ℕ) : WithTop ℕ) <
      (fun _ => ((t + 1 : ℕ) : WithTop ℕ)) ω} from hk), indicator_of_mem (show ω ∈
      {ω | ((k : ℕ) : WithTop ℕ) < firstReturn B ω} from lt_of_lt_of_le hk
        (succ_le_of_lt_withTop h))]
  · rw [indicator_of_notMem (show ω ∉ {ω : ℕ → X | ((k : ℕ) : WithTop ℕ) <
      (fun _ => ((t + 1 : ℕ) : WithTop ℕ)) ω} from hk)]
    exact zero_le

/-! ### The sample-path bound -/

omit [MeasurableSpace X] in
/-- `Σ_{k<τ} F_k ≤ Σ_{k<τ'} F_k` at a path where `τ ≤ τ'`. -/
theorem sumBefore_le_of_le_at {Ω : Type*} {τ τ' : Ω → WithTop ℕ} {ω : Ω} (h : τ ω ≤ τ' ω)
    (F : ℕ → Ω → ℝ≥0∞) : sumBefore τ F ω ≤ sumBefore τ' F ω := by
  unfold sumBefore
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : (k : WithTop ℕ) < τ ω
  · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ' ω} from lt_of_lt_of_le hk h)]
  · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk)]
    exact zero_le

omit [MeasurableSpace X] in
/-- `Σ_{k<t+s} G_k = Σ_{k<t} G_k + c Σ_{j<s} G_j ∘ θᵗ` when `G_{t+j} = c G_j ∘ θᵗ`. -/
theorem sumBefore_add_eq {G : ℕ → (ℕ → X) → ℝ≥0∞} {c : ℝ≥0∞} {ω : ℕ → X} {t : ℕ}
    {s : WithTop ℕ} (hG : ∀ j, G (t + j) ω = c * G j (shift t ω)) :
    sumBefore (fun _ => (t : WithTop ℕ) + s) G ω =
      ∑ k ∈ range t, G k ω + c * sumBefore (fun _ => s) G (shift t ω) := by
  rw [sumBefore_eq_tsum, tsum_indicator_lt_add, sumBefore_eq_tsum, ← ENNReal.tsum_mul_left]
  refine congrArg (_ + ·) (tsum_congr fun j => ?_)
  by_cases hj : (j : WithTop ℕ) < s
  · rw [indicator_of_mem (show j ∈ {j : ℕ | (j : WithTop ℕ) < s} from hj),
      indicator_of_mem (show j ∈ {j : ℕ | (j : WithTop ℕ) < s} from hj), hG]
  · rw [indicator_of_notMem (show j ∉ {j : ℕ | (j : WithTop ℕ) < s} from hj),
      indicator_of_notMem (show j ∉ {j : ℕ | (j : WithTop ℕ) < s} from hj), mul_zero]

omit [MeasurableSpace X] in
/-- The block bound up to `min(τ_B, τ_C(N))`. -/
theorem sumBefore_min_returnTimeK_le (B C : Set X) (r : ℝ≥0∞) (f : X → ℝ≥0∞) (N : ℕ)
    (ω : ℕ → X) :
    sumBefore (fun ω => min (firstReturn B ω) (returnTimeK C N ω))
        (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω ≤
      ∑ n ∈ range N, {ω | returnTimeK C n ω < firstReturn B ω}.indicator
        (fun ω => tpow r (returnTimeK C n ω) * sumBefore (firstReturn C)
          (fun k ω => r ^ (k + 1) * f (ω (k + 1))) (shiftAt (returnTimeK C n) ω)) ω := by
  set G : ℕ → (ℕ → X) → ℝ≥0∞ := fun k ω => r ^ (k + 1) * f (ω (k + 1)) with hGdef
  induction N with
  | zero =>
    rw [Finset.sum_range_zero, sumBefore_of_eq'
      (ζ := fun ω => min (firstReturn B ω) (returnTimeK C 0 ω)) (t := 0)
      (show min (firstReturn B ω) (returnTimeK C 0 ω) = ((0 : ℕ) : WithTop ℕ) from
        min_eq_right zero_le), Finset.sum_range_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hlt : returnTimeK C N ω < firstReturn B ω
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hlt.ne_top
      have ht' : returnTimeK C N ω = (t : WithTop ℕ) := ht.symm
      have hmin : min (firstReturn B ω) (returnTimeK C N ω) = (t : WithTop ℕ) := by
        rw [min_eq_right hlt.le, ht']
      have hle : min (firstReturn B ω) (returnTimeK C (N + 1) ω) ≤
          (t : WithTop ℕ) + firstReturn C (shift t ω) :=
        (min_le_right _ _).trans (le_of_eq (returnTimeK_succ_eq' C ht'))
      calc sumBefore (fun ω => min (firstReturn B ω) (returnTimeK C (N + 1) ω)) G ω
          ≤ sumBefore (fun _ => (t : WithTop ℕ) + firstReturn C (shift t ω)) G ω :=
            sumBefore_le_of_le_at (τ := fun ω => min (firstReturn B ω) (returnTimeK C (N + 1) ω))
              (τ' := fun _ => (t : WithTop ℕ) + firstReturn C (shift t ω)) hle G
        _ = ∑ k ∈ range t, G k ω + r ^ t * sumBefore (fun _ => firstReturn C (shift t ω)) G
              (shift t ω) := sumBefore_add_eq fun j => geomTaboo_shift_weight r f ω t j
        _ = sumBefore (fun ω => min (firstReturn B ω) (returnTimeK C N ω)) G ω +
              {ω | returnTimeK C N ω < firstReturn B ω}.indicator (fun ω =>
                tpow r (returnTimeK C N ω) * sumBefore (firstReturn C) G
                  (shiftAt (returnTimeK C N) ω)) ω := by
            rw [sumBefore_of_eq' (ζ := fun ω => min (firstReturn B ω) (returnTimeK C N ω)) hmin,
              indicator_of_mem (show ω ∈ {ω | returnTimeK C N ω <
              firstReturn B ω} from hlt), ht', tpow_coe, shiftAt_of_eq ht']
            rfl
        _ ≤ _ := add_le_add ih le_rfl
    · rw [indicator_of_notMem (show ω ∉ {ω | returnTimeK C N ω < firstReturn B ω} from hlt),
        add_zero]
      refine le_trans (sumBefore_le_of_le_at
        (τ := fun ω => min (firstReturn B ω) (returnTimeK C (N + 1) ω))
        (τ' := fun ω => min (firstReturn B ω) (returnTimeK C N ω)) ?_ G) ih
      have h1 : firstReturn B ω ≤ returnTimeK C N ω := not_lt.1 hlt
      rw [min_eq_left h1, min_eq_left (h1.trans (returnTimeK_le_succ C N ω))]

omit [MeasurableSpace X] in
/-- **The sample-path bound (p. 374)**: `Σ_{k=1}^{τ_B} f(Φ_k) rᵏ ≤ Σ_{n ≥ 0}
1{τ_C(n) < τ_B} r^{τ_C(n)} (Σ_{k=1}^{τ_C} f(Φ_k) rᵏ) ∘ θ^{τ_C(n)}`. -/
theorem sumBefore_le_tsum_returnTimeK (B C : Set X) (r : ℝ≥0∞) (f : X → ℝ≥0∞)
    (ω : ℕ → X) :
    sumBefore (firstReturn B) (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω ≤
      ∑' n, {ω | returnTimeK C n ω < firstReturn B ω}.indicator
        (fun ω => tpow r (returnTimeK C n ω) * sumBefore (firstReturn C)
          (fun k ω => r ^ (k + 1) * f (ω (k + 1))) (shiftAt (returnTimeK C n) ω)) ω := by
  rw [sumBefore_eq_tsum, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun K => ?_
  refine le_trans ?_ ((sumBefore_min_returnTimeK_le B C r f K ω).trans (ENNReal.sum_le_tsum _))
  rw [sumBefore_eq_tsum]
  refine (Finset.sum_le_sum fun k hk => ?_).trans (ENNReal.sum_le_tsum _)
  by_cases hkT : (k : WithTop ℕ) < firstReturn B ω
  · have hkK : (k : WithTop ℕ) < returnTimeK C K ω :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Finset.mem_range.1 hk)) (le_returnTimeK C K ω)
    rw [indicator_of_mem (show k ∈ {k : ℕ | (k : WithTop ℕ) < firstReturn B ω} from hkT),
      indicator_of_mem (show k ∈ {k : ℕ | (k : WithTop ℕ) < min (firstReturn B ω)
        (returnTimeK C K ω)} from lt_min hkT hkK)]
  · rw [indicator_of_notMem (show k ∉ {k : ℕ | (k : WithTop ℕ) < firstReturn B ω} from hkT)]
    exact zero_le

/-! ### Measurability and the strong Markov property at `τ_C(n)` -/

/-- `{ζ < T}` is an event, and `{ζ < T} ∩ {ζ = t} ∈ 𝓕ₜ`, for stopping times `ζ`, `T`. -/
theorem measurableSet_lt_inter_eq {ζ T : (ℕ → X) → WithTop ℕ}
    (hζ : IsStoppingTime (natFilt (X := X)) ζ) (hT : IsStoppingTime (natFilt (X := X)) T)
    (t : ℕ) : MeasurableSet[natFilt t] ({ω | ζ ω < T ω} ∩ {ω | ζ ω = t}) := by
  have h : {ω | ζ ω < T ω} ∩ {ω | ζ ω = t} = {ω | ζ ω = t} ∩ {ω | (t : WithTop ℕ) < T ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; rw [h2] at h1; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; rw [h1]; exact ⟨h2, rfl⟩
  rw [h]
  exact (hζ.measurableSet_eq_of_countable t).inter (measurableSet_lt_of_isStoppingTime hT t)

/-- `{ζ < T}` is an event. -/
theorem measurableSet_lt_stopping {ζ T : (ℕ → X) → WithTop ℕ}
    (hζ : IsStoppingTime (natFilt (X := X)) ζ) (hT : IsStoppingTime (natFilt (X := X)) T) :
    MeasurableSet {ω | ζ ω < T ω} := by
  have h : {ω | ζ ω < T ω} = ⋃ t : ℕ, ({ω | ζ ω < T ω} ∩ {ω | ζ ω = t}) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h.ne_top
      exact ⟨t, h, ht.symm⟩
    · rintro ⟨t, h, -⟩; exact h
  rw [h]
  exact MeasurableSet.iUnion fun t => (natFilt (X := X)).le t _ (measurableSet_lt_inter_eq hζ hT t)

/-- **The strong Markov property with the weight `r^ζ`**: for `A ∩ {ζ = n} ∈ 𝓕ₙ`,
`E_x[r^ζ H ∘ θ^ζ; A, ζ < ∞] = E_x[r^ζ E_{Φ_ζ}[H]; A, ζ < ∞]`. -/
theorem lintegral_tpow_shiftAt (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {τ : (ℕ → X) → WithTop ℕ} {A : Set (ℕ → X)}
    (hA : ∀ n : ℕ, MeasurableSet[natFilt n] (A ∩ {ω | τ ω = n})) (r : ℝ≥0∞)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, tpow r (τ ω) * H (shiftAt τ ω) ∂pathKernel P x =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, tpow r (τ ω) *
        ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) ∂pathKernel P x := by
  have hw : ∀ ω, τ ω ≠ ⊤ → tpow r (τ ω) = r ^ (τ ω).untopA := fun ω hω => by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [← ht]; rfl
  have hm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) := by
    rw [inter_ne_top_eq_iUnion]
    exact MeasurableSet.iUnion fun n => (natFilt (X := X)).le n _ (hA n)
  have h := lintegral_weight_shiftAt P (Measure.dirac x) hA (fun n => r ^ n) hH
  rw [pathMeasure_dirac] at h
  rw [setLIntegral_congr_fun hm fun ω hω => by rw [hw ω hω.2], h]
  exact setLIntegral_congr_fun hm fun ω hω => by rw [hw ω hω.2]

/-! ### The estimates (15.24)–(15.27) -/

/-- **(15.24)**: if `E_y[s^{τ_C}] ≤ M` on `C` (`M ≥ 1`), then
`E_x[s^{τ_C(n + 2)}] ≤ M E_x[s^{τ_C(n + 1)}]`. -/
theorem lintegral_tpow_returnTimeK_le (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {s : ℝ≥0∞} (hs : 1 < s) {M : ℝ≥0∞} (hM1 : 1 ≤ M)
    (hK : ∀ y ∈ C, kendallMoment P C s y ≤ M) (n : ℕ) (x : X) :
    ∫⁻ ω, tpow s (returnTimeK C (n + 2) ω) ∂pathKernel P x ≤
      M * ∫⁻ ω, tpow s (returnTimeK C (n + 1) ω) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  set ζ := returnTimeK C (n + 1) with hζdef
  have hζ : IsStoppingTime (natFilt (X := X)) ζ := isStoppingTime_returnTimeK hC (n + 1)
  have hζm : ∀ k : ℕ, MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < ζ ω} :=
    fun k => (natFilt (X := X)).le k _ (measurableSet_lt_of_isStoppingTime hζ k)
  have hS := measurableSet_ne_top hζ
  have hτC : Measurable fun ω : ℕ → X => tpow s (firstReturn C ω) :=
    measurable_tpow_comp (measurableSet_lt_firstReturn hC) hs
  have hpt : ∀ ω, tpow s (returnTimeK C (n + 2) ω) ≤
      {ω | ζ ω ≠ ⊤}.indicator (fun ω => tpow s (ζ ω) *
        tpow s (firstReturn C (shiftAt ζ ω))) ω + {ω | ζ ω ≠ ⊤}ᶜ.indicator (fun _ => ∞) ω :=
    fun ω => by
    cases h : ζ ω with
    | top =>
      rw [indicator_of_mem (show ω ∈ {ω | ζ ω ≠ ⊤}ᶜ from by simp [h])]
      exact le_top.trans le_add_self
    | coe t =>
      rw [indicator_of_mem (show ω ∈ {ω | ζ ω ≠ ⊤} from by simp [h]), shiftAt_of_eq h,
        show returnTimeK C (n + 2) ω = returnTimeK C (n + 1 + 1) ω from rfl,
        returnTimeK_succ_eq' C h, tpow_add hs.le, h]
      exact le_self_add
  have hA : ∀ k : ℕ, MeasurableSet[natFilt k] (Set.univ ∩ {ω : ℕ → X | ζ ω = k}) := fun k => by
    rw [Set.univ_inter]; exact hζ.measurableSet_eq_of_countable k
  have hSM := lintegral_tpow_shiftAt P x hA s hτC
  rw [Set.univ_inter] at hSM
  calc ∫⁻ ω, tpow s (returnTimeK C (n + 2) ω) ∂pathKernel P x
      ≤ ∫⁻ ω, ({ω | ζ ω ≠ ⊤}.indicator (fun ω => tpow s (ζ ω) *
          tpow s (firstReturn C (shiftAt ζ ω))) ω + {ω | ζ ω ≠ ⊤}ᶜ.indicator (fun _ => ∞) ω)
          ∂pathKernel P x := lintegral_mono hpt
    _ = ∫⁻ ω in {ω | ζ ω ≠ ⊤}, tpow s (ζ ω) * tpow s (firstReturn C (shiftAt ζ ω))
          ∂pathKernel P x + ∫⁻ ω in {ω | ζ ω ≠ ⊤}ᶜ, ∞ ∂pathKernel P x := by
        rw [lintegral_add_right _ (measurable_const.indicator hS.compl), lintegral_indicator hS,
          lintegral_indicator hS.compl]
    _ = ∫⁻ ω in {ω | ζ ω ≠ ⊤}, tpow s (ζ ω) * kendallMoment P C s (stoppedState ζ ω)
          ∂pathKernel P x + ∫⁻ ω in {ω | ζ ω ≠ ⊤}ᶜ, tpow s (ζ ω) ∂pathKernel P x := by
        rw [hSM]
        congr 1
        refine setLIntegral_congr_fun hS.compl fun ω hω => ?_
        have : ζ ω = ⊤ := by simpa using hω
        rw [this, tpow_top]
    _ ≤ ∫⁻ ω in {ω | ζ ω ≠ ⊤}, M * tpow s (ζ ω) ∂pathKernel P x +
          ∫⁻ ω in {ω | ζ ω ≠ ⊤}ᶜ, M * tpow s (ζ ω) ∂pathKernel P x := by
        refine add_le_add (setLIntegral_mono' hS fun ω hω => ?_)
          (setLIntegral_mono' hS.compl fun ω _ => le_mul_of_one_le_left' hM1)
        rw [mul_comm M]
        exact mul_le_mul' le_rfl (hK _ (stoppedState_returnTimeK_mem C n hω))
    _ = M * ∫⁻ ω, tpow s (ζ ω) ∂pathKernel P x := by
        rw [lintegral_add_compl _ hS, lintegral_const_mul _ (measurable_tpow_comp hζm hs)]

/-- **(15.24) iterated**: `E_x[s^{τ_C(n + 1)}] ≤ Mⁿ E_x[s^{τ_C}]`. -/
theorem lintegral_tpow_returnTimeK_le_pow (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {s : ℝ≥0∞} (hs : 1 < s) {M : ℝ≥0∞} (hM1 : 1 ≤ M)
    (hK : ∀ y ∈ C, kendallMoment P C s y ≤ M) (n : ℕ) (x : X) :
    ∫⁻ ω, tpow s (returnTimeK C (n + 1) ω) ∂pathKernel P x ≤ M ^ n * kendallMoment P C s x := by
  induction n with
  | zero => rw [pow_zero, one_mul]; rfl
  | succ n ih =>
    calc ∫⁻ ω, tpow s (returnTimeK C (n + 2) ω) ∂pathKernel P x
        ≤ M * ∫⁻ ω, tpow s (returnTimeK C (n + 1) ω) ∂pathKernel P x :=
          lintegral_tpow_returnTimeK_le P hC hs hM1 hK n x
      _ ≤ M * (M ^ n * kendallMoment P C s x) := mul_le_mul' le_rfl ih
      _ = M ^ (n + 1) * kendallMoment P C s x := by rw [pow_succ]; ring

/-- **(15.27), one block**: if `P_y(τ_C(m) < τ_B) ≤ q` on `C`, then
`P_x(τ_C(n + 1 + m) < τ_B) ≤ q P_x(τ_C(n + 1) < τ_B)`. -/
theorem measure_returnTimeK_lt_le (P : Kernel X X) [IsMarkovKernel P] {B C : Set X}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {m : ℕ} {q : ℝ≥0∞}
    (hq : ∀ y ∈ C, pathKernel P y {ω | returnTimeK C m ω < firstReturn B ω} ≤ q) (n : ℕ)
    (x : X) :
    pathKernel P x {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω} ≤
      q * pathKernel P x {ω | returnTimeK C (n + 1) ω < firstReturn B ω} := by
  have := isMarkovKernel_pathKernel P
  set ζ := returnTimeK C (n + 1) with hζdef
  have hζ : IsStoppingTime (natFilt (X := X)) ζ := isStoppingTime_returnTimeK hC (n + 1)
  have hT := (proposition_3_4_4 hB).1
  set A := {ω | ζ ω < firstReturn B ω} with hAdef
  have hAm : MeasurableSet A := measurableSet_lt_stopping hζ hT
  have hEm : MeasurableSet {ω | returnTimeK C m ω < firstReturn B ω} :=
    measurableSet_lt_stopping (isStoppingTime_returnTimeK hC m) hT
  have hAne : A ∩ {ω | ζ ω ≠ ⊤} = A :=
    inter_eq_left.2 fun ω hω => (show ζ ω < firstReturn B ω from hω).ne_top
  have hpt : ∀ ω, {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω}.indicator 1 ω ≤
      A.indicator (fun ω => {ω | returnTimeK C m ω < firstReturn B ω}.indicator 1
        (shiftAt ζ ω)) ω := fun ω => by
    by_cases hω : ω ∈ A
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (show ζ ω < firstReturn B ω from hω).ne_top
      have ht' : ζ ω = (t : WithTop ℕ) := ht.symm
      rw [indicator_of_mem hω (f := fun ω => {ω | returnTimeK C m ω < firstReturn B ω}.indicator
        (1 : (ℕ → X) → ℝ≥0∞) (shiftAt ζ ω)), shiftAt_of_eq ht']
      have h1 := returnTimeK_add_eq C ht' m
      have h2 := firstReturn_eq_add_shift_of_lt B
        (show (t : WithTop ℕ) < firstReturn B ω by rw [← ht']; exact hω)
      by_cases hlt : returnTimeK C (n + 1 + m) ω < firstReturn B ω
      · rw [indicator_of_mem (show ω ∈ {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω}
          from hlt)]
        rw [h1, h2] at hlt
        have hmem : shift t ω ∈ {ω | returnTimeK C m ω < firstReturn B ω} :=
          (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).1 hlt
        rw [indicator_of_mem hmem]
        exact le_of_eq rfl
      · rw [indicator_of_notMem (show ω ∉ {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω}
          from hlt)]
        exact zero_le
    · have hge : firstReturn B ω ≤ returnTimeK C (n + 1 + m) ω :=
        (not_lt.1 hω).trans (returnTimeK_mono C ω (by omega))
      rw [indicator_of_notMem (show ω ∉ {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω}
        from not_lt.2 hge)]
      exact zero_le
  have hA : ∀ k : ℕ, MeasurableSet[natFilt k] (A ∩ {ω : ℕ → X | ζ ω = k}) :=
    measurableSet_lt_inter_eq hζ hT
  have hSM := lintegral_weight_shiftAt P (Measure.dirac x) hA (fun _ => 1)
    (measurable_one.indicator hEm)
  simp only [one_mul, pathMeasure_dirac, hAne] at hSM
  calc pathKernel P x {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω}
      = ∫⁻ ω, {ω | returnTimeK C (n + 1 + m) ω < firstReturn B ω}.indicator 1 ω
          ∂pathKernel P x :=
        (lintegral_indicator_one (measurableSet_lt_stopping
          (isStoppingTime_returnTimeK hC (n + 1 + m)) hT)).symm
    _ ≤ ∫⁻ ω in A, {ω | returnTimeK C m ω < firstReturn B ω}.indicator 1 (shiftAt ζ ω)
          ∂pathKernel P x := by
        rw [← lintegral_indicator hAm]; exact lintegral_mono hpt
    _ = ∫⁻ ω in A, pathKernel P (stoppedState ζ ω)
          {ω | returnTimeK C m ω < firstReturn B ω} ∂pathKernel P x := by
        rw [hSM]
        exact setLIntegral_congr_fun hAm fun ω _ => lintegral_indicator_one hEm
    _ ≤ ∫⁻ _ in A, q ∂pathKernel P x := setLIntegral_mono' hAm fun ω hω =>
        hq _ (stoppedState_returnTimeK_mem C n (show ζ ω < firstReturn B ω from hω).ne_top)
    _ = q * pathKernel P x A := by rw [setLIntegral_const]

/-- **(15.27) iterated**: `P_x(τ_C(1 + m j) < τ_B) ≤ q^j`. -/
theorem measure_returnTimeK_lt_le_pow (P : Kernel X X) [IsMarkovKernel P] {B C : Set X}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {m : ℕ} {q : ℝ≥0∞}
    (hq : ∀ y ∈ C, pathKernel P y {ω | returnTimeK C m ω < firstReturn B ω} ≤ q) (j : ℕ)
    (x : X) : pathKernel P x {ω | returnTimeK C (1 + m * j) ω < firstReturn B ω} ≤ q ^ j := by
  have := isMarkovKernel_pathKernel P
  induction j with
  | zero => rw [pow_zero]; exact prob_le_one
  | succ j ih =>
    have h := measure_returnTimeK_lt_le P hB hC hq (m * j) x
    rw [show m * j + 1 + m = 1 + m * (j + 1) by ring, show m * j + 1 = 1 + m * j by ring] at h
    calc pathKernel P x {ω | returnTimeK C (1 + m * (j + 1)) ω < firstReturn B ω}
        ≤ q * pathKernel P x {ω | returnTimeK C (1 + m * j) ω < firstReturn B ω} := h
      _ ≤ q * q ^ j := mul_le_mul' le_rfl ih
      _ = q ^ (j + 1) := by rw [pow_succ, mul_comm]

/-- `n ↦ P_x(τ_C(n) < τ_B)` is antitone. -/
theorem measure_returnTimeK_lt_anti (P : Kernel X X) [IsMarkovKernel P] (B C : Set X) {n n' : ℕ}
    (h : n ≤ n') (x : X) :
    pathKernel P x {ω | returnTimeK C n' ω < firstReturn B ω} ≤
      pathKernel P x {ω | returnTimeK C n ω < firstReturn B ω} :=
  measure_mono fun ω hω => lt_of_le_of_lt (returnTimeK_mono C ω h) hω

/-- **The bound `xy ≤ γⁿx² + γ⁻ⁿy²`** for `y = 1`: `a ≤ c a² + c⁻¹` for `0 < c < ∞`. -/
theorem le_mul_sq_add_inv (a : ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞) :
    a ≤ c * a ^ 2 + c⁻¹ := by
  by_cases h : 1 ≤ c * a
  · calc a = 1 * a := (one_mul a).symm
      _ ≤ c * a * a := mul_le_mul' h le_rfl
      _ = c * a ^ 2 := by ring
      _ ≤ c * a ^ 2 + c⁻¹ := le_self_add
  · push Not at h
    calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc hc', one_mul]
      _ ≤ c⁻¹ * 1 := mul_le_mul' le_rfl h.le
      _ = c⁻¹ := mul_one _
      _ ≤ c * a ^ 2 + c⁻¹ := le_add_self

/-! ### Choosing the rates -/

/-- The sequence `1 + 1/(n + 1)`, decreasing to `1`. -/
noncomputable def seqOneLt (n : ℕ) : ℝ≥0∞ := 1 + ((n : ℝ≥0∞) + 1)⁻¹

/-- `1 < 1 + 1/(n + 1)`. -/
theorem one_lt_seqOneLt (n : ℕ) : 1 < seqOneLt n :=
  ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2 (ENNReal.add_ne_top.2
    ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))

/-- `1 + 1/(n + 1) < ∞`. -/
theorem seqOneLt_ne_top (n : ℕ) : seqOneLt n ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (by positivity)⟩

/-- `1 + 1/(n + 1) → 1`. -/
theorem tendsto_seqOneLt : Tendsto seqOneLt atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have := (tendsto_const_nhds (x := (1 : ℝ≥0∞))).add h
  rwa [add_zero] at this

/-- `rᵐ → 1` along `r = 1 + 1/(n + 1)`. -/
theorem tendsto_seqOneLt_pow (m : ℕ) : Tendsto (fun n => seqOneLt n ^ m) atTop (𝓝 1) := by
  have := ((ENNReal.continuous_pow m).tendsto 1).comp tendsto_seqOneLt
  rwa [one_pow] at this

/-- For `q < 1` and `m`, there is `g > 1`, `g < ∞`, with `gᵐ q < 1`. -/
theorem exists_pow_mul_lt_one {q : ℝ≥0∞} (hq : q < 1) (m : ℕ) :
    ∃ g, 1 < g ∧ g ≠ ∞ ∧ g ^ m * q < 1 := by
  have h := ENNReal.Tendsto.mul_const (tendsto_seqOneLt_pow m) (b := q)
    (Or.inr (hq.trans ENNReal.one_lt_top).ne)
  rw [one_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hq)).exists
  exact ⟨seqOneLt n, one_lt_seqOneLt n, seqOneLt_ne_top n, hn⟩

/-- For `r₀ > 1`, `M₀ < ∞` and `g > 1` there is `r > 1` with `r² ≤ r₀` and
`1 + (r² − 1)/(r₀ − 1) M₀ < g`. -/
theorem exists_rate {r₀ : ℝ≥0∞} (hr₀ : 1 < r₀) {M₀ : ℝ≥0∞} (hM₀ : M₀ ≠ ∞) {g : ℝ≥0∞}
    (hg : 1 < g) : ∃ r, 1 < r ∧ r ^ 2 ≤ r₀ ∧ 1 + (r ^ 2 - 1) / (r₀ - 1) * M₀ < g := by
  have h1 := tendsto_seqOneLt_pow 2
  have h2 : Tendsto (fun n => seqOneLt n ^ 2 - 1) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub h1 (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
      (Or.inl ENNReal.one_ne_top)
    rwa [tsub_self] at this
  have hc : (r₀ - 1)⁻¹ * M₀ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
    (tsub_pos_iff_lt.2 hr₀).ne') hM₀
  have h3 : Tendsto (fun n => 1 + (seqOneLt n ^ 2 - 1) / (r₀ - 1) * M₀) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.mul_const h2 (b := (r₀ - 1)⁻¹ * M₀) (Or.inr hc)
    rw [zero_mul] at this
    have h4 := (tendsto_const_nhds (x := (1 : ℝ≥0∞))).add this
    rw [add_zero] at h4
    refine h4.congr fun n => ?_
    rw [div_eq_mul_inv, mul_assoc]
  obtain ⟨n, hn1, hn2⟩ := ((h1.eventually (gt_mem_nhds hr₀)).and
    (h3.eventually (gt_mem_nhds hg))).exists
  exact ⟨seqOneLt n, one_lt_seqOneLt n, hn1.le, hn2⟩

/-! ### The trials bound -/

/-- **The geometric trials bound** (the proof of Theorem 15.2.1, (15.24)–(15.27)). Suppose that on
`C`, `E_y[r₀^{τ_C}] ≤ M₀` and `U_C^{(r₀)}(y, f) ≤ M_f`, and that `P_y(τ_C(m) < τ_B) ≤ q < 1` for
`y ∈ C`. Then for some `r ∈ (1, r₀]` and `K < ∞`, for every `x`,
`U_B^{(r)}(x, f) ≤ U_C^{(r₀)}(x, f) + K E_x[r₀^{τ_C}] + K`. -/
theorem geomTaboo_trials (P : Kernel X X) [IsMarkovKernel P] {B C : Set X} (hB : MeasurableSet B)
    (hC : MeasurableSet C) {f : X → ℝ≥0∞} (hf : Measurable f) {r₀ : ℝ≥0∞} (hr₀ : 1 < r₀)
    (hr₀' : r₀ ≠ ∞) {M₀ Mf : ℝ≥0∞} (hM₀ : M₀ ≠ ∞) (hMf : Mf ≠ ∞)
    (hK : ∀ y ∈ C, kendallMoment P C r₀ y ≤ M₀)
    (hU : ∀ y ∈ C, geomTaboo P C r₀ f y ≤ Mf) {m : ℕ} (hm : 1 ≤ m) {q : ℝ≥0∞} (hq : q < 1)
    (hT : ∀ y ∈ C, pathKernel P y {ω | returnTimeK C m ω < firstReturn B ω} ≤ q) :
    ∃ r, 1 < r ∧ r ≤ r₀ ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x,
      geomTaboo P B r f x ≤ geomTaboo P C r₀ f x + K * kendallMoment P C r₀ x + K := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨g, hg1, hgt, hgq⟩ := exists_pow_mul_lt_one hq m
  obtain ⟨r, hr1, hr2, hM2g⟩ := exists_rate hr₀ hM₀ hg1
  set M₂ := 1 + (r ^ 2 - 1) / (r₀ - 1) * M₀ with hM₂def
  have hr2' : 1 < r ^ 2 := one_lt_pow₀ hr1 two_ne_zero
  have hrr₀ : r ≤ r₀ := (le_self_pow₀ hr1.le two_ne_zero).trans hr2
  have hg0 : g ≠ 0 := (zero_lt_one.trans hg1).ne'
  set γ := g⁻¹ with hγ
  have hγ0 : γ ≠ 0 := ENNReal.inv_ne_zero.2 hgt
  have hγt : γ ≠ ∞ := ENNReal.inv_ne_top.2 hg0
  have hγM : γ * M₂ < 1 := by
    rw [hγ, mul_comm, ← div_eq_mul_inv]
    exact (ENNReal.div_lt_iff (Or.inl hg0) (Or.inl hgt)).2 (by rw [one_mul]; exact hM2g)
  have hM21 : 1 ≤ M₂ := le_self_add
  -- the Kendall bound for `r²`
  have hK2 : ∀ y, kendallMoment P C (r ^ 2) y ≤ 1 + (r ^ 2 - 1) / (r₀ - 1) *
      kendallMoment P C r₀ y := fun y => by
    have hm0 := measurable_tpow_comp (measurableSet_lt_firstReturn hC (X := X)) hr₀
    calc kendallMoment P C (r ^ 2) y ≤ ∫⁻ ω, (1 + (r ^ 2 - 1) / (r₀ - 1) *
          tpow r₀ (firstReturn C ω)) ∂pathKernel P y :=
          lintegral_mono fun ω => tpow_le_one_add hr2' hr2 hr₀' _
      _ = 1 + (r ^ 2 - 1) / (r₀ - 1) * kendallMoment P C r₀ y := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ hm0]; rfl
  have hK2C : ∀ y ∈ C, kendallMoment P C (r ^ 2) y ≤ M₂ := fun y hy =>
    (hK2 y).trans (add_le_add le_rfl (mul_le_mul' le_rfl (hK y hy)))
  have hTs := (proposition_3_4_4 hB).1
  have hζ : ∀ n, IsStoppingTime (natFilt (X := X)) (returnTimeK C n) := fun n =>
    isStoppingTime_returnTimeK hC n
  have hζm : ∀ n (k : ℕ), MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < returnTimeK C n ω} :=
    fun n k => (natFilt (X := X)).le k _ (measurableSet_lt_of_isStoppingTime (hζ n) k)
  have hAm : ∀ n, MeasurableSet {ω : ℕ → X | returnTimeK C n ω < firstReturn B ω} := fun n =>
    measurableSet_lt_stopping (hζ n) hTs
  have hUm := measurable_geomTaboo P hC r hf
  have hBlk := measurable_sumBefore_geomTaboo hC r hf
  set I : ℕ → (ℕ → X) → ℝ≥0∞ := fun n => {ω | returnTimeK C n ω < firstReturn B ω}.indicator
    (fun ω => tpow r (returnTimeK C n ω) * sumBefore (firstReturn C)
      (fun k ω => r ^ (k + 1) * f (ω (k + 1))) (shiftAt (returnTimeK C n) ω)) with hIdef
  have hIm : ∀ n, Measurable (I n) := fun n =>
    ((measurable_tpow_comp (hζm n) hr1).mul (hBlk.comp (measurable_shiftAt (hζ n)))).indicator
      (hAm n)
  -- the strong Markov property at `τ_C(n)`
  have hIeq : ∀ x n, ∫⁻ ω, I n ω ∂pathKernel P x =
      ∫⁻ ω in {ω | returnTimeK C n ω < firstReturn B ω}, tpow r (returnTimeK C n ω) *
        geomTaboo P C r f (stoppedState (returnTimeK C n) ω) ∂pathKernel P x := fun x n => by
    have hne : {ω | returnTimeK C n ω < firstReturn B ω} ∩ {ω | returnTimeK C n ω ≠ ⊤} =
        {ω | returnTimeK C n ω < firstReturn B ω} :=
      inter_eq_left.2 fun ω hω => (show returnTimeK C n ω < firstReturn B ω from hω).ne_top
    have h := lintegral_tpow_shiftAt P x (measurableSet_lt_inter_eq (hζ n) hTs) r hBlk
    rw [hne] at h
    rw [hIdef, lintegral_indicator (hAm n), h]
    rfl
  -- the sample-path bound, integrated
  have hA_ : ∀ x, geomTaboo P B r f x ≤ ∑' n, ∫⁻ ω, I n ω ∂pathKernel P x := fun x => by
    rw [← lintegral_tsum fun n => (hIm n).aemeasurable, geomTaboo]
    exact lintegral_mono fun ω => sumBefore_le_tsum_returnTimeK B C r f ω
  -- the term `n = 0`
  have h0 : ∀ x, ∫⁻ ω, I 0 ω ∂pathKernel P x ≤ geomTaboo P C r₀ f x := fun x => by
    rw [hIeq x 0]
    have hz : ∀ ω : ℕ → X, returnTimeK C 0 ω = ((0 : ℕ) : WithTop ℕ) := fun _ => rfl
    calc ∫⁻ ω in {ω | returnTimeK C 0 ω < firstReturn B ω}, tpow r (returnTimeK C 0 ω) *
          geomTaboo P C r f (stoppedState (returnTimeK C 0) ω) ∂pathKernel P x
        = ∫⁻ ω in {ω | returnTimeK C 0 ω < firstReturn B ω}, geomTaboo P C r f (ω 0)
            ∂pathKernel P x := setLIntegral_congr_fun (hAm 0) fun ω _ => by
          rw [stoppedState_of_eq (hz ω), hz ω, tpow_coe, pow_zero, one_mul]
      _ ≤ ∫⁻ ω, geomTaboo P C r f (ω 0) ∂pathKernel P x := setLIntegral_le_lintegral _ _
      _ = geomTaboo P C r f x := lintegral_coord_zero P x hUm
      _ ≤ geomTaboo P C r₀ f x := geomTaboo_mono_r P C hrr₀ f x
  -- the terms `n ≥ 1`, with the bound `xy ≤ γⁿx² + γ⁻ⁿy²`
  have hD : ∀ x (k : ℕ), ∫⁻ ω, I (k + 1) ω ∂pathKernel P x ≤ Mf * (γ ^ (k + 1) *
      (M₂ ^ k * kendallMoment P C (r ^ 2) x) + g ^ (k + 1) *
        pathKernel P x {ω | returnTimeK C (k + 1) ω < firstReturn B ω}) := fun x k => by
    have hc0 : γ ^ (k + 1) ≠ 0 := pow_ne_zero _ hγ0
    have hct : γ ^ (k + 1) ≠ ∞ := ENNReal.pow_ne_top hγt
    have hinv : (γ ^ (k + 1))⁻¹ = g ^ (k + 1) := by rw [ENNReal.inv_pow, hγ, inv_inv]
    have hm2 := measurable_tpow_comp (hζm (k + 1)) hr2'
    have hmeas : Measurable fun ω : ℕ → X =>
        γ ^ (k + 1) * tpow (r ^ 2) (returnTimeK C (k + 1) ω) + g ^ (k + 1) :=
      (measurable_const.mul hm2).add measurable_const
    rw [hIeq x (k + 1)]
    calc ∫⁻ ω in {ω | returnTimeK C (k + 1) ω < firstReturn B ω},
          tpow r (returnTimeK C (k + 1) ω) *
            geomTaboo P C r f (stoppedState (returnTimeK C (k + 1)) ω) ∂pathKernel P x
        ≤ ∫⁻ ω in {ω | returnTimeK C (k + 1) ω < firstReturn B ω}, Mf * (γ ^ (k + 1) *
            tpow (r ^ 2) (returnTimeK C (k + 1) ω) + g ^ (k + 1)) ∂pathKernel P x :=
          setLIntegral_mono' (hAm (k + 1)) fun ω hω => by
            rw [mul_comm Mf]
            refine mul_le_mul' ?_ ?_
            · rw [tpow_sq, ← hinv]; exact le_mul_sq_add_inv _ hc0 hct
            · exact (geomTaboo_mono_r P C hrr₀ f _).trans (hU _ (stoppedState_returnTimeK_mem C k
                (show returnTimeK C (k + 1) ω < firstReturn B ω from hω).ne_top))
      _ = Mf * (γ ^ (k + 1) * ∫⁻ ω in {ω | returnTimeK C (k + 1) ω < firstReturn B ω},
            tpow (r ^ 2) (returnTimeK C (k + 1) ω) ∂pathKernel P x + g ^ (k + 1) *
              pathKernel P x {ω | returnTimeK C (k + 1) ω < firstReturn B ω}) := by
          rw [lintegral_const_mul Mf hmeas,
            lintegral_add_right _ measurable_const, lintegral_const_mul _ hm2, setLIntegral_const]
      _ ≤ _ := mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl
          ((setLIntegral_le_lintegral _ _).trans
            (lintegral_tpow_returnTimeK_le_pow P hC hr2' hM21 hK2C k x))) le_rfl)
  -- the two series
  have hgeo1 : ∀ x, ∑' k, γ ^ (k + 1) * (M₂ ^ k * kendallMoment P C (r ^ 2) x) =
      γ * (1 - γ * M₂)⁻¹ * kendallMoment P C (r ^ 2) x := fun x => by
    have e : ∀ k, γ ^ (k + 1) * (M₂ ^ k * kendallMoment P C (r ^ 2) x) =
        (γ * kendallMoment P C (r ^ 2) x) * (γ * M₂) ^ k := fun k => by
      rw [mul_pow, pow_succ]; ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; ring
  have hgeo2 : ∀ x, ∑' k, g ^ (k + 1) *
      pathKernel P x {ω | returnTimeK C (k + 1) ω < firstReturn B ω} ≤
        m * g ^ m * (1 - g ^ m * q)⁻¹ := fun x => by
    rw [tsum_eq_tsum_sum_block (fun k => g ^ (k + 1) *
      pathKernel P x {ω | returnTimeK C (k + 1) ω < firstReturn B ω}) hm]
    calc ∑' j, ∑ i ∈ range m, g ^ (m * j + i + 1) *
          pathKernel P x {ω | returnTimeK C (m * j + i + 1) ω < firstReturn B ω}
        ≤ ∑' j, ∑ _i ∈ range m, g ^ m * (g ^ m * q) ^ j :=
          ENNReal.tsum_le_tsum fun j => Finset.sum_le_sum fun i hi => by
            have hi' := Finset.mem_range.1 hi
            have h1 : g ^ (m * j + i + 1) ≤ g ^ (m * (j + 1)) :=
              pow_le_pow_right₀ hg1.le (by rw [Nat.mul_succ]; omega)
            have h2 : pathKernel P x {ω | returnTimeK C (m * j + i + 1) ω < firstReturn B ω} ≤
                q ^ j := (measure_returnTimeK_lt_anti P B C (show 1 + m * j ≤ m * j + i + 1 by
                  omega) x).trans (measure_returnTimeK_lt_le_pow P hB hC hT j x)
            calc g ^ (m * j + i + 1) *
                  pathKernel P x {ω | returnTimeK C (m * j + i + 1) ω < firstReturn B ω}
                ≤ g ^ (m * (j + 1)) * q ^ j := mul_le_mul' h1 h2
              _ = g ^ m * (g ^ m * q) ^ j := by
                  rw [mul_pow, ← pow_mul, Nat.mul_succ, pow_add]; ring
      _ = m * g ^ m * (1 - g ^ m * q)⁻¹ := by
          simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; ring
  -- the conclusion
  have hfin1 : (1 - γ * M₂)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hγM).ne'
  have hfin2 : (1 - g ^ m * q)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hgq).ne'
  set K := Mf * (γ * (1 - γ * M₂)⁻¹) + Mf * (m * g ^ m * (1 - g ^ m * q)⁻¹) with hKdef
  refine ⟨r, hr1, hrr₀, K, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top hγt hfin1), ENNReal.mul_ne_top hMf (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (ENNReal.pow_ne_top hgt)) hfin2)⟩,
    fun x => ?_⟩
  calc geomTaboo P B r f x ≤ ∑' n, ∫⁻ ω, I n ω ∂pathKernel P x := hA_ x
    _ = ∫⁻ ω, I 0 ω ∂pathKernel P x + ∑' k, ∫⁻ ω, I (k + 1) ω ∂pathKernel P x :=
        tsum_eq_zero_add' ENNReal.summable
    _ ≤ geomTaboo P C r₀ f x + ∑' k, Mf * (γ ^ (k + 1) * (M₂ ^ k *
          kendallMoment P C (r ^ 2) x) + g ^ (k + 1) *
            pathKernel P x {ω | returnTimeK C (k + 1) ω < firstReturn B ω}) :=
        add_le_add (h0 x) (ENNReal.tsum_le_tsum fun k => hD x k)
    _ = geomTaboo P C r₀ f x + Mf * (γ * (1 - γ * M₂)⁻¹ * kendallMoment P C (r ^ 2) x +
          ∑' k, g ^ (k + 1) * pathKernel P x {ω | returnTimeK C (k + 1) ω < firstReturn B ω})
          := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, hgeo1]
    _ ≤ geomTaboo P C r₀ f x + Mf * (γ * (1 - γ * M₂)⁻¹ * kendallMoment P C r₀ x +
          m * g ^ m * (1 - g ^ m * q)⁻¹) :=
        add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl
          (kendallMoment_mono_r P C hr2 x)) (hgeo2 x)))
    _ ≤ geomTaboo P C r₀ f x + K * kendallMoment P C r₀ x + K := by
        rw [add_assoc]
        refine add_le_add le_rfl ?_
        rw [mul_add, ← mul_assoc]
        exact add_le_add (mul_le_mul' le_self_add le_rfl) le_add_self

/-! ### Theorem 15.2.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Petite sets are left geometrically often** (the step before (15.27)): for a petite `C` and
`B ∈ B⁺(X)` there is `m ≥ 1` with `P_y(τ_C(m) < τ_B) ≤ 1/2` for every `y`. The expected number of
visits to `C` before `τ_B` is bounded (Chapter 11), and Markov's inequality applies. -/
theorem exists_returnTimeK_lt_le_half {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) {B : Set X}
    (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ y, pathKernel P y {ω | returnTimeK C m ω < firstReturn B ω} ≤ 2⁻¹ := by
  have := isMarkovKernel_pathKernel P
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨c, hc, hbound⟩ := lintegral_sumBefore_indicator_le hψ hC hB hψB
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (show (2 : ℝ≥0∞) * c ≠ ∞ from
    ENNReal.mul_ne_top (by norm_num) hc)
  refine ⟨m + 1, by omega, fun y => ?_⟩
  set E := {ω : ℕ → X | returnTimeK C (m + 1) ω < firstReturn B ω} with hEdef
  have hEm : MeasurableSet E :=
    measurableSet_lt_stopping (isStoppingTime_returnTimeK hCm (m + 1)) (proposition_3_4_4 hB).1
  have hmark : ((m + 1 : ℕ) : ℝ≥0∞) * pathKernel P y E ≤ c := by
    calc ((m + 1 : ℕ) : ℝ≥0∞) * pathKernel P y E
        = ∫⁻ ω, E.indicator (fun _ => ((m + 1 : ℕ) : ℝ≥0∞)) ω ∂pathKernel P y := by
          rw [lintegral_indicator_const hEm]
      _ ≤ ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω ∂pathKernel P y :=
          lintegral_mono fun ω => by
            by_cases hω : ω ∈ E
            · rw [indicator_of_mem hω]; exact natCast_le_sumBefore_indicator B C (m + 1) hω
            · rw [indicator_of_notMem hω]; exact zero_le
      _ ≤ c := hbound y
  have hm0 : ((m + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hmt : ((m + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [ENNReal.le_inv_iff_mul_le, ← ENNReal.mul_le_mul_iff_right hm0 hmt, mul_one]
  calc ((m + 1 : ℕ) : ℝ≥0∞) * (pathKernel P y E * 2)
      = 2 * (((m + 1 : ℕ) : ℝ≥0∞) * pathKernel P y E) := by ring
    _ ≤ 2 * c := mul_le_mul' le_rfl hmark
    _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) := hm.le.trans (by exact_mod_cast Nat.le_succ m)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The bound behind Theorem 15.2.1**: for a petite `C` which is `f`-Kendall of rate `κ`
(`f ≥ 1`) and `B ∈ B⁺(X)`, there are `r ∈ (1, κ]` and `K < ∞` with
`U_B^{(r)}(x, f) ≤ U_C^{(κ)}(x, f) + K E_x[κ^{τ_C}] + K` for every `x`. -/
theorem theorem_15_2_1_bound {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} (hC : IsPetite P C) {κ : ℝ≥0∞} (hK : IsFKendall P f C κ) {B : Set X}
    (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    ∃ r, 1 < r ∧ r ≤ κ ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x,
      geomTaboo P B r f x ≤ geomTaboo P C κ f x + K * kendallMoment P C κ x + K := by
  obtain ⟨hCm, hκ, hκ', M, hM, hb⟩ := hK
  obtain ⟨-, hK0, hU0⟩ := fKendall_bounds P hCm hκ hf hf1 hb
  obtain ⟨m, hm, hT⟩ := exists_returnTimeK_lt_le_half hψ hC hB hψB
  have hM₀ : 1 + (κ - 1) * M ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hM⟩
  exact geomTaboo_trials P hB hCm hf hκ hκ' hM₀ (ENNReal.add_ne_top.2 ⟨hM,
    ENNReal.mul_ne_top hM hM₀⟩) hK0 hU0 hm (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2))
    (fun y _ => hT y)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.2.1** (MT p. 373), corrected: for a `ψ`-irreducible chain and `f ≥ 1`, a set `C`
is petite, non-empty and `f`-Kendall iff it is `f`-geometrically regular and `C ∈ B⁺(X)`. -/
theorem theorem_15_2_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} :
    (IsPetite P C ∧ C.Nonempty ∧ IsFKendallSet P f C) ↔
      (IsFGeomRegularSet P ψ f C ∧ 0 < ψ C) := by
  constructor
  · rintro ⟨hpet, hne, κ, hK⟩
    obtain ⟨hCm, hκ, hκ', M, hM, hb⟩ := hK
    obtain ⟨hfC, hK0, hU0⟩ := fKendall_bounds P hCm hκ hf hf1 hb
    refine ⟨⟨hCm, fun B hB hψB => ?_⟩, ?_⟩
    · obtain ⟨r, hr, hrκ, K, hK, hbd⟩ :=
        theorem_15_2_1_bound hψ hf hf1 hpet ⟨hCm, hκ, hκ', M, hM, hb⟩ hB hψB
      refine ⟨r, hr, ne_top_of_le_ne_top hκ' hrκ, M + (M + M * (1 + (κ - 1) * M) +
        K * (1 + (κ - 1) * M) + K), ?_, fun x hx => ?_⟩
      · have hM₀ : 1 + (κ - 1) * M ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
          ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hM⟩
        exact ENNReal.add_ne_top.2 ⟨hM, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
          ⟨ENNReal.add_ne_top.2 ⟨hM, ENNReal.mul_ne_top hM hM₀⟩, ENNReal.mul_ne_top hK hM₀⟩,
            hK⟩⟩
      · calc geomSum P B r f x ≤ f x + geomTaboo P B r f x := geomSum_le_add_geomTaboo P B r hf x
          _ ≤ M + (M + M * (1 + (κ - 1) * M) + K * (1 + (κ - 1) * M) + K) :=
            add_le_add (hfC x hx) ((hbd x).trans (add_le_add (add_le_add (hU0 x hx)
              (mul_le_mul' le_rfl (hK0 x hx))) le_rfl))
    · refine ((theorem_14_2_4 hψ hf hf1).1 ⟨hpet, hne, M, hM, fun x hx => ?_⟩).2
      exact (fSumReturn_le_geomSum P C hκ.le f x).trans (hb x hx)
  · rintro ⟨hC, hψC⟩
    obtain ⟨hpet, hne, -⟩ := (theorem_14_2_4 hψ hf hf1).2 ⟨hC.isFRegularSet, hψC⟩
    obtain ⟨r, hr, hr', M, hM, hb⟩ := hC.2 C hC.1 hψC
    exact ⟨hpet, hne, r, hC.1, hr, hr', M, hM, hb⟩

/-- **The counterexample to Theorem 15.2.1 as stated** (`C = ∅`): `∅` is petite and `f`-Kendall
(vacuously), but `∅ ∉ B⁺(X)`. -/
theorem theorem_15_2_1_counterexample {P : Kernel X X} [IsMarkovKernel P] (ψ : Measure X)
    (f : X → ℝ≥0∞) (x : X) : IsPetite P ∅ ∧ IsFKendallSet P f ∅ ∧ ¬ 0 < ψ ∅ :=
  ⟨(theorem_14_2_4_counterexample (P := P) ψ f x).1, ⟨2, MeasurableSet.empty, by norm_num,
    ENNReal.ofNat_ne_top, 0, ENNReal.zero_ne_top, fun y hy => absurd hy (notMem_empty y)⟩,
    by simp⟩

end MeynTweedie.Epilogue
