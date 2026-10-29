/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.TotalVariation
import Epilogue.AtomInvariant
import Epilogue.RenewalTheorem

/-!
# The regenerative decomposition for chains with atoms (MT §13.1.1, §13.2.3)

Meyn and Tweedie, pp. 316–318 and 324–326. `α` is an atom with a point `a ∈ α`, and
`_αPⁿ⁺¹(x, ·) = tabooKernel P hα n x` is the law of `Φₙ₊₁` on `{τ_α ≥ n + 1}`; for an initial
measure `λ`, `λ _αPⁿ⁺¹ = tabooSeq P hα λ n`.

**First-entrance and last-exit decompositions as identities of measures.**
* `pow_succ_eq_firstEntrance`: the measure form of (8.18) for any set `A`,
  `Pⁿ⁺¹(x, ·) = _APⁿ⁺¹(x, ·) + Σ_{j<n} ∫_A _APʲ⁺¹(x, dw) Pⁿ⁻ʲ(w, ·)`.
* `IsAtom.pow_succ_firstEntrance`, `IsAtom.comp_pow_succ_firstEntrance`: on an atom (13.40),
  `λPⁿ⁺¹ = λ _αPⁿ⁺¹ + Σ_{j<n} P_λ(τ_α = j + 1) Pⁿ⁻ʲ(a, ·)`.
* `IsAtom.pow_succ_lastExit`: `Pᵐ⁺¹(a, ·) = _αPᵐ⁺¹(a, ·) + Σ_{j<m} Pʲ⁺¹(a, α) _αPᵐ⁻ʲ(a, ·)`.
* `tabooSeq_univ_add_sum`: `P_λ(τ_α ≥ n + 1) + Σ_{j<n} P_λ(τ_α = j + 1) = λ(X)`;
  `tabooKernel_apply_le_one`, `tabooKernel_le_pow` (`_APⁿ⁺¹ ≤ Pⁿ⁺¹`), `tabooSeq_apply_le`.

**The three sequences** (13.10)–(13.12), (13.42)–(13.43), as real sequences on `ℤ₊`.
* `entryLaw P hα λ = a_λ`, `a_λ(n) = P_λ(τ_α = n)` (`a_λ(0) = 0`);
* `atomRenewal P α a = u`, `u(n) = Pⁿ(a, α)`;
* `lastExitSeq P hα a f = t_f`, `t_f(n) = ∫ _αPⁿ(a, dy) f(y) = E_a[f(Φₙ) 1{τ_α ≥ n}]` for
  measurable `f ≥ 0` (`t_f(0) = 0`).
* `hasSum_entryLaw`: `Σₙ a_λ(n) = ∫ λ(dx) L(x, α) = P_λ(τ_α < ∞)` ((13.21), (13.52));
  `tabooSeq_univ_toReal`: `P_λ(τ_α ≥ n + 1) = λ(X) − Σ_{k ≤ n} a_λ(k)`.

**The decompositions** (for bounded measurable `f ≥ 0`).
* (13.44) `comp_pow_succ_atom_toReal`: `λPⁿ(α) = a_λ ∗ u (n)`, `n ≥ 1`; (13.14) is `λ = δ_x`.
* (13.45) `lintegral_pow_succ_atom_toReal`: `Pⁿ(α, f) = u ∗ t_f (n)`, `n ≥ 1`; (13.15).
* (13.46) `lintegral_comp_pow_succ_atom_toReal`:
  `λPⁿ(f) = λ _αPⁿ(f) + a_λ ∗ u ∗ t_f (n)`, `n ≥ 1`; (13.16) is `λ = δ_x`.
* (13.50) `lintegral_eq_tsum_lastExitSeq`: if `π = π(α) μ°_α` then `π(f) = π(α) Σ_{j ≥ 1} t_f(j)`;
  (13.13) is `f = 1_{y}`.
* `atomRenewal_eq_realRenewalSeq`: `u` is the renewal sequence of the return-time law
  `p = a_{δ_a}` (MT p. 320).
* `incrMean_entryLaw`: `m_p = E_a[τ_α]` when `L(a, α) = 1` and `E_a[τ_α] < ∞`.

**Results.**
* **Theorem 13.2.5** (`theorem_13_2_5`, p. 325): the Regenerative Decompositions (13.47)
  and (13.48) for an accessible atom of a positive chain; the general forms
  `regenerative_decomposition_47`, `regenerative_decomposition_48` need only that
  `π = π(α) μ°_α`.
* `tvNorm_comp_pow_succ_le` (the proof of Theorem 13.3.1 (i), (13.54)–(13.56)): the bound
  (13.48) holds uniformly over `|f| ≤ 1`, so
  `‖λPⁿ⁺¹ − π‖ ≤ P_λ(τ_α ≥ n + 1) + Σ_{k ≤ n} |a_λ ∗ u (n − k) − π(α)| t₁(k + 1) +
  π(α) Σ_{j > n + 1} t₁(j)`.

**Hypotheses.** Theorem 13.2.5 is stated in the book for every `f ≥ 0`, with values in
`[0, ∞]`; the inequalities are between real numbers, so `f` is taken bounded (the identities
(13.44)–(13.46) themselves hold in `[0, ∞]` for every measurable `f ≥ 0`, as measure identities).

**Corrections.** None.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Decompositions as identities of measures -/

/-- The measure form of the first-entrance decomposition (8.18):
`Pⁿ⁺¹(x, ·) = _APⁿ⁺¹(x, ·) + Σ_{j<n} ∫_A _APʲ⁺¹(x, dw) Pⁿ⁻ʲ(w, ·)`. -/
theorem pow_succ_eq_firstEntrance (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    (P ^ (n + 1)) x = tabooKernel P hA n x +
      ∑ j ∈ range n, (P ^ (n - j) : Kernel X X) ∘ₘ (tabooKernel P hA j x).restrict A := by
  ext B hB
  rw [firstEntrance_decomposition P hA n x hB, tabooProb_eq_tabooKernel P hA n x hB,
    Measure.add_apply, Measure.finsetSum_apply]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (measure_kernel_apply _ _ hB).symm

/-- (13.40), first half: on an atom,
`Pⁿ⁺¹(x, ·) = _αPⁿ⁺¹(x, ·) + Σ_{j<n} _αPʲ⁺¹(x, α) Pⁿ⁻ʲ(a, ·)`. -/
theorem IsAtom.pow_succ_firstEntrance {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (n : ℕ) (x : X) :
    (P ^ (n + 1)) x = tabooKernel P hα.1 n x +
      ∑ j ∈ range n, (tabooKernel P hα.1 j x α) • (P ^ (n - j) : Kernel X X) a := by
  rw [pow_succ_eq_firstEntrance P hα.1 n x]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := Finset.mem_range.1 hj
  have h : ∀ w ∈ α, ∀ B, (P ^ (n - j) : Kernel X X) w B = (P ^ (n - j) : Kernel X X) a B :=
    fun w hw B => by
      rw [show n - j = (n - j - 1) + 1 by omega, hα.pow_succ_eq hw ha]
  ext B hB
  rw [measure_kernel_apply _ _ hB, Measure.smul_apply, smul_eq_mul,
    setLIntegral_congr_fun hα.1 (fun w hw => h w hw B), setLIntegral_const, mul_comm]

/-- (13.40) integrated against an initial measure `λ`:
`λPⁿ⁺¹ = λ _αPⁿ⁺¹ + Σ_{j<n} (λ _αPʲ⁺¹)(α) Pⁿ⁻ʲ(a, ·)`. -/
theorem IsAtom.comp_pow_succ_firstEntrance {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (n : ℕ) (μ : Measure X) :
    (P ^ (n + 1) : Kernel X X) ∘ₘ μ = tabooSeq P hα.1 μ n +
      ∑ j ∈ range n, (tabooSeq P hα.1 μ j α) • (P ^ (n - j) : Kernel X X) a := by
  ext B hB
  rw [measure_kernel_apply _ _ hB, Measure.add_apply, Measure.finsetSum_apply, tabooSeq,
    measure_kernel_apply _ _ hB]
  simp_rw [hα.pow_succ_firstEntrance ha n, Measure.add_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_left (Kernel.measurable_coe _ hB),
    lintegral_finsetSum _ (fun j _ => (Kernel.measurable_coe _ hα.1).mul_const _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_mul_const _ (Kernel.measurable_coe _ hα.1), tabooSeq,
    measure_kernel_apply _ _ hα.1]

/-- (13.40), second half (the last-exit decomposition at the atom):
`Pᵐ⁺¹(a, ·) = _αPᵐ⁺¹(a, ·) + Σ_{j<m} Pʲ⁺¹(a, α) _αPᵐ⁻ʲ(a, ·)`. -/
theorem IsAtom.pow_succ_lastExit {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (m : ℕ) :
    (P ^ (m + 1)) a = tabooKernel P hα.1 m a +
      ∑ j ∈ range m, ((P ^ (j + 1) : Kernel X X) a α) • tabooKernel P hα.1 (m - 1 - j) a := by
  ext B hB
  rw [lastExit_decomposition P hα.1 m a hB, tabooProb_eq_tabooKernel P hα.1 m a hB,
    Measure.add_apply, Measure.finsetSum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  have h : ∀ w ∈ α, tabooProb P α (m - j) w B = tabooKernel P hα.1 (m - 1 - j) a B :=
    fun w hw => by
      rw [show m - j = (m - 1 - j) + 1 by omega, tabooProb_eq_tabooKernel P hα.1 _ w hB,
        hα.tabooKernel_eq hw ha]
  rw [setLIntegral_congr_fun hα.1 h, setLIntegral_const, Measure.smul_apply, smul_eq_mul,
    mul_comm]

/-- `_APⁿ⁺¹(x, X) ≤ 1`. -/
theorem tabooKernel_apply_le_one (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) (B : Set X) : tabooKernel P hA n x B ≤ 1 := by
  have := isMarkovKernel_pathKernel P
  refine (measure_mono (subset_univ B)).trans ?_
  rw [← tabooProb_eq_tabooKernel P hA n x MeasurableSet.univ]
  exact prob_le_one

/-- `_APⁿ⁺¹(x, B) ≤ Pⁿ⁺¹(x, B)`. -/
theorem tabooKernel_le_pow (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooKernel P hA n x B ≤ (P ^ (n + 1) : Kernel X X) x B := by
  have := isMarkovKernel_pathKernel P
  rw [← tabooProb_eq_tabooKernel P hA n x hB, tabooProb, ← pathKernel_coord_mem P x (n + 1) hB]
  exact measure_mono inter_subset_left

/-- `λ _APⁿ⁺¹(X) ≤ λ(X)`. -/
theorem tabooSeq_apply_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) (n : ℕ) (B : Set X) :
    tabooSeq P hA μ n B ≤ μ univ := by
  refine (measure_mono (subset_univ B)).trans ?_
  rw [tabooSeq, measure_kernel_apply _ _ MeasurableSet.univ]
  calc ∫⁻ x, tabooKernel P hA n x univ ∂μ ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono fun x => tabooKernel_apply_le_one P hA n x univ
    _ = μ univ := by rw [lintegral_one]

/-- The masses: `P_λ(τ_A ≥ n + 1) + Σ_{j<n} P_λ(τ_A = j + 1) = λ(X)`. -/
theorem tabooSeq_univ_add_sum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) (n : ℕ) :
    tabooSeq P hA μ n univ + ∑ j ∈ range n, tabooSeq P hA μ j A = μ univ := by
  induction n with
  | zero => rw [range_zero, Finset.sum_empty, add_zero, tabooSeq_zero, Measure.comp_apply_univ]
  | succ n ih =>
    rw [Finset.sum_range_succ, tabooSeq_succ, Measure.comp_apply_univ,
      Measure.restrict_apply_univ, ← ih, add_comm (∑ j ∈ range n, _) _, ← add_assoc,
      add_comm _ (tabooSeq P hA μ n A), measure_add_measure_compl hA]

/-- `L(x, α)` integrated: `∫ λ(dx) L(x, A) = Σₙ P_λ(τ_A = n + 1)`. -/
theorem lintegral_hitProb_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) :
    ∫⁻ x, hitProb P A x ∂μ = ∑' n, tabooSeq P hA μ n A := by
  simp_rw [hitProb_eq_tsum P hA]
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ hA).aemeasurable]
  exact tsum_congr fun n => by rw [tabooSeq, measure_kernel_apply _ _ hA]

/-! ### The sequences `a_λ`, `u`, `t_f` -/

/-- `a_λ(n) = P_λ(τ_α = n)` (13.10), (13.42), as a real sequence with `a_λ(0) = 0`. -/
noncomputable def entryLaw (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (μ : Measure X) :
    ℕ → ℝ
  | 0 => 0
  | k + 1 => (tabooSeq P hα μ k α).toReal

/-- `u(n) = Pⁿ(a, α)` (13.11), the renewal sequence of returns to the atom. -/
noncomputable def atomRenewal (P : Kernel X X) (α : Set X) (a : X) (n : ℕ) : ℝ :=
  ((P ^ n : Kernel X X) a α).toReal

/-- `t_f(n) = ∫ _αPⁿ(a, dy) f(y)` (13.12), (13.43), with `t_f(0) = 0`. -/
noncomputable def lastExitSeq (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    (f : X → ℝ≥0∞) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (∫⁻ y, f y ∂tabooKernel P hα m a).toReal

/-- `a_λ(0) = 0`. -/
@[simp] theorem entryLaw_zero (P : Kernel X X) {α : Set X} (hα : MeasurableSet α)
    (μ : Measure X) : entryLaw P hα μ 0 = 0 := rfl

/-- `a_λ(k + 1) = P_λ(τ_α = k + 1)`. -/
theorem entryLaw_succ (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (μ : Measure X)
    (k : ℕ) : entryLaw P hα μ (k + 1) = (tabooSeq P hα μ k α).toReal := rfl

/-- `a_λ ≥ 0`. -/
theorem entryLaw_nonneg (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (μ : Measure X)
    (k : ℕ) : 0 ≤ entryLaw P hα μ k := by
  cases k
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

/-- For `δ_a`, `a(k + 1) = _αPᵏ⁺¹(a, α) = P_a(τ_α = k + 1)`. -/
theorem entryLaw_dirac_succ (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    (k : ℕ) : entryLaw P hα (Measure.dirac a) (k + 1) = (tabooKernel P hα k a α).toReal := by
  rw [entryLaw_succ, tabooSeq, dirac_kernel]

/-- `t_f(0) = 0`. -/
@[simp] theorem lastExitSeq_zero (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    (f : X → ℝ≥0∞) : lastExitSeq P hα a f 0 = 0 := rfl

/-- `t_f(m + 1) = ∫ _αPᵐ⁺¹(a, dy) f(y)`. -/
theorem lastExitSeq_succ (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    (f : X → ℝ≥0∞) (m : ℕ) :
    lastExitSeq P hα a f (m + 1) = (∫⁻ y, f y ∂tabooKernel P hα m a).toReal := rfl

/-- `t_f ≥ 0`. -/
theorem lastExitSeq_nonneg (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    (f : X → ℝ≥0∞) (m : ℕ) : 0 ≤ lastExitSeq P hα a f m := by
  cases m
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

/-- For an indicator, `t_{1_B}(m + 1) = _αPᵐ⁺¹(a, B)`. -/
theorem lastExitSeq_indicator_succ (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    {B : Set X} (hB : MeasurableSet B) (m : ℕ) :
    lastExitSeq P hα a (B.indicator 1) (m + 1) = (tabooKernel P hα m a B).toReal := by
  rw [lastExitSeq_succ, lintegral_indicator_one hB]

/-- `u(0) = 1`. -/
theorem atomRenewal_zero (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) {a : X}
    (ha : a ∈ α) : atomRenewal P α a 0 = 1 := by
  rw [atomRenewal, pow_zero_apply, Measure.dirac_apply' _ hα, indicator_of_mem ha, Pi.one_apply,
    ENNReal.toReal_one]

/-- `u ≥ 0`. -/
theorem atomRenewal_nonneg (P : Kernel X X) (α : Set X) (a : X) (n : ℕ) :
    0 ≤ atomRenewal P α a n := ENNReal.toReal_nonneg

/-- `u ≤ 1`. -/
theorem atomRenewal_le_one (P : Kernel X X) [IsMarkovKernel P] (α : Set X) (a : X) (n : ℕ) :
    atomRenewal P α a n ≤ 1 := by
  have := isMarkovKernel_pow P n
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- `∫ f d(_αPᵐ⁺¹(a, ·))` is finite for bounded `f`. -/
theorem lintegral_tabooKernel_ne_top (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (x : X) {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ y, f y ≤ C) (m : ℕ) : ∫⁻ y, f y ∂tabooKernel P hα m x ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (ENNReal.one_ne_top)) ?_
  calc ∫⁻ y, f y ∂tabooKernel P hα m x ≤ ∫⁻ _, C ∂tabooKernel P hα m x := lintegral_mono hfC
    _ = C * tabooKernel P hα m x univ := lintegral_const C
    _ ≤ C * 1 := by gcongr; exact tabooKernel_apply_le_one P hα m x univ

/-- `t_f ≤ C t₁` for `f ≤ C`, with `t₁(m + 1) = _αPᵐ⁺¹(a, X)`. -/
theorem lastExitSeq_le (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : MeasurableSet α)
    (a : X) {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (m : ℕ) :
    lastExitSeq P hα a f (m + 1) ≤ C.toReal * (tabooKernel P hα m a univ).toReal := by
  rw [lastExitSeq_succ, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hC
    (ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hα m a univ))) ?_
  calc ∫⁻ y, f y ∂tabooKernel P hα m a ≤ ∫⁻ _, C ∂tabooKernel P hα m a := lintegral_mono hfC
    _ = C * tabooKernel P hα m a univ := lintegral_const C

/-! ### The real decompositions (13.44)–(13.46), (13.50) -/

/-- `∫ f d(λ _αPⁿ⁺¹)` is finite for bounded `f` and finite `λ`. -/
theorem lintegral_tabooSeq_ne_top (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ≥0∞} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (n : ℕ) : ∫⁻ y, f y ∂tabooSeq P hα μ n ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top μ univ)) ?_
  calc ∫⁻ y, f y ∂tabooSeq P hα μ n ≤ ∫⁻ _, C ∂tabooSeq P hα μ n := lintegral_mono hfC
    _ = C * tabooSeq P hα μ n univ := lintegral_const C
    _ ≤ C * μ univ := mul_le_mul_right (tabooSeq_apply_le P hα μ n univ) C

/-- `∫ f dPᵐ(a, ·)` is finite for bounded `f`. -/
theorem lintegral_pow_ne_top (P : Kernel X X) [IsMarkovKernel P] (x : X) {f : X → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (m : ℕ) :
    ∫⁻ y, f y ∂(P ^ m : Kernel X X) x ≠ ∞ := by
  have := isMarkovKernel_pow P m
  refine ne_top_of_le_ne_top hC ?_
  calc ∫⁻ y, f y ∂(P ^ m : Kernel X X) x ≤ ∫⁻ _, C ∂(P ^ m : Kernel X X) x := lintegral_mono hfC
    _ = C := by rw [lintegral_const, measure_univ, mul_one]

/-- **(13.45)**, (13.15): for `n ≥ 1`, `Pⁿ(a, f) = u ∗ t_f (n)`, for bounded measurable
`f ≥ 0`. -/
theorem lintegral_pow_succ_atom_toReal {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ y, f y ≤ C) (m : ℕ) :
    (∫⁻ y, f y ∂(P ^ (m + 1) : Kernel X X) a).toReal =
      realConv (atomRenewal P α a) (lastExitSeq P hα.1 a f) (m + 1) := by
  have hfin := lintegral_tabooKernel_ne_top P hα.1 a hC hfC
  have hu : ∀ j, (P ^ (j + 1) : Kernel X X) a α ≠ ∞ := fun j => by
    have := isMarkovKernel_pow P (j + 1); exact measure_ne_top _ _
  rw [hα.pow_succ_lastExit ha m, lintegral_add_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [ENNReal.toReal_add (hfin m)
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (hu j) (hfin _)),
    ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top (hu j) (hfin _)]
  simp_rw [ENNReal.toReal_mul]
  rw [realConv_eq_sum_range, Finset.sum_range_succ', Finset.sum_range_succ,
    atomRenewal_zero P hα.1 ha, one_mul, Nat.sub_zero, lastExitSeq_succ]
  simp only [Nat.sub_self, lastExitSeq_zero, mul_zero, add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  rw [show m + 1 - (j + 1) = (m - 1 - j) + 1 by omega, lastExitSeq_succ]
  rfl

/-- **(13.44)**, (13.14): for `n ≥ 1`, `λPⁿ(α) = a_λ ∗ u (n)`. -/
theorem comp_pow_succ_atom_toReal {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    (((P ^ (n + 1) : Kernel X X) ∘ₘ μ) α).toReal =
      realConv (entryLaw P hα.1 μ) (atomRenewal P α a) (n + 1) := by
  have hE : ∀ j, tabooSeq P hα.1 μ j α ≠ ∞ := fun j =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα.1 μ j α)
  have hu : ∀ j, (P ^ j : Kernel X X) a α ≠ ∞ := fun j => by
    have := isMarkovKernel_pow P j; exact measure_ne_top _ _
  rw [hα.comp_pow_succ_firstEntrance ha n μ, Measure.add_apply, Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (hE n)
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (hE j) (hu _)),
    ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top (hE j) (hu _)]
  simp_rw [ENNReal.toReal_mul]
  rw [realConv_eq_sum_range, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [entryLaw_zero, zero_mul, add_zero, Nat.sub_self, atomRenewal_zero P hα.1 ha,
    mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [entryLaw_succ, Nat.add_sub_add_right]
  rfl

/-- **(13.46)**, (13.16): for `n ≥ 1` and bounded measurable `f ≥ 0`,
`λPⁿ(f) = λ _αPⁿ(f) + a_λ ∗ u ∗ t_f (n)`. -/
theorem lintegral_comp_pow_succ_atom_toReal {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (n : ℕ) :
    (∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ μ)).toReal =
      (∫⁻ y, f y ∂tabooSeq P hα.1 μ n).toReal +
        realConv (realConv (entryLaw P hα.1 μ) (atomRenewal P α a)) (lastExitSeq P hα.1 a f)
          (n + 1) := by
  have hE : ∀ j, tabooSeq P hα.1 μ j α ≠ ∞ := fun j =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα.1 μ j α)
  have hP := lintegral_pow_ne_top P a hC hfC
  rw [realConv_assoc, hα.comp_pow_succ_firstEntrance ha n μ, lintegral_add_measure,
    lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [ENNReal.toReal_add (lintegral_tabooSeq_ne_top P hα.1 μ hC hfC n)
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (hE j) (hP _)),
    ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top (hE j) (hP _)]
  simp_rw [ENNReal.toReal_mul]
  congr 1
  have h0 : realConv (atomRenewal P α a) (lastExitSeq P hα.1 a f) 0 = 0 := by
    simp [realConv_eq_sum_range]
  rw [realConv_eq_sum_range, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [entryLaw_zero, zero_mul, add_zero, Nat.sub_self, h0, mul_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := Finset.mem_range.1 hj
  rw [entryLaw_succ, show n + 1 - (j + 1) = (n - j - 1) + 1 by omega,
    ← lintegral_pow_succ_atom_toReal hα ha hC hfC, show n - j - 1 + 1 = n - j by omega]

/-- **(13.50)**, (13.13): if `π = π(α) μ°_α`, then `π(f) = π(α) Σ_{j ≥ 1} t_f(j)` for bounded
measurable `f ≥ 0`. -/
theorem lintegral_eq_tsum_lastExitSeq (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} (hπ : π = π α • atomMeasure P hα a)
    {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) :
    (∫⁻ y, f y ∂π).toReal = (π α).toReal * ∑' m, lastExitSeq P hα a f (m + 1) := by
  have h1 : ∫⁻ y, f y ∂π = π α * ∑' m, ∫⁻ y, f y ∂tabooKernel P hα m a := by
    conv_lhs => rw [hπ]
    rw [lintegral_smul_measure, smul_eq_mul, atomMeasure, tabooPotKernel, Kernel.sum_apply,
      lintegral_sum_measure]
  rw [h1, ENNReal.toReal_mul,
    ENNReal.tsum_toReal_eq fun m => lintegral_tabooKernel_ne_top P hα a hC hfC m]
  rfl

/-! ### The entry law and the renewal sequence -/

/-- (13.21), (13.52): `Σₙ a_λ(n) = ∫ λ(dx) L(x, α) = P_λ(τ_α < ∞)`. -/
theorem hasSum_entryLaw (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : MeasurableSet α)
    (μ : Measure X) [IsFiniteMeasure μ] :
    HasSum (entryLaw P hα μ) (∫⁻ x, hitProb P α x ∂μ).toReal := by
  have hfin : ∫⁻ x, hitProb P α x ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_ne_top μ univ) ?_
    calc ∫⁻ x, hitProb P α x ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun x => hitProb_le_one P α x
      _ = μ univ := lintegral_one
  have hE : ∀ j, tabooSeq P hα μ j α ≠ ∞ := fun j =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα μ j α)
  have h := ENNReal.hasSum_toReal (f := fun n => tabooSeq P hα μ n α)
    (by rw [← lintegral_hitProb_eq_tsum P hα μ]; exact hfin)
  rw [← ENNReal.tsum_toReal_eq hE, ← lintegral_hitProb_eq_tsum P hα μ] at h
  have h2 := (hasSum_nat_add_iff' (f := entryLaw P hα μ) 1).1 (by simpa [entryLaw_succ] using h)
  simpa using h2

/-- `P_λ(τ_α ≥ n + 1) = λ(X) − Σ_{k ≤ n} a_λ(k)`. -/
theorem tabooSeq_univ_toReal (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    (tabooSeq P hα μ n univ).toReal = μ.real univ - ∑ k ∈ range (n + 1), entryLaw P hα μ k := by
  have hE : ∀ j, tabooSeq P hα μ j α ≠ ∞ := fun j =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα μ j α)
  have h := congrArg ENNReal.toReal (tabooSeq_univ_add_sum P hα μ n)
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top (measure_ne_top μ univ)
      (tabooSeq_apply_le P hα μ n univ)) (ENNReal.sum_ne_top.2 fun j _ => hE j),
    ENNReal.toReal_sum fun j _ => hE j] at h
  rw [Finset.sum_range_succ', entryLaw_zero, add_zero, measureReal_def, ← h]
  simp [entryLaw_succ]

/-- `u` is the renewal sequence of the return-time law `p(n) = P_a(τ_α = n)` (MT p. 320). -/
theorem atomRenewal_eq_realRenewalSeq {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) :
    atomRenewal P α a = realRenewalSeq (entryLaw P hα.1 (Measure.dirac a)) := by
  set p := entryLaw P hα.1 (Measure.dirac a)
  have hp0 : p 0 = 0 := rfl
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [atomRenewal_zero P hα.1 ha, realRenewalSeq_zero hp0]
    · have h := comp_pow_succ_atom_toReal hα ha (Measure.dirac a) n
      rw [dirac_kernel] at h
      rw [atomRenewal, h, realRenewalSeq_eq_realConv_of_pos hp0 (Nat.succ_pos n),
        realConv_eq_sum_range, realConv_eq_sum_range]
      refine Finset.sum_congr rfl fun k hk => ?_
      rcases k with _ | k
      · simp only [p, entryLaw_zero, zero_mul]
      · rw [ih (n + 1 - (k + 1)) (by omega)]

/-- The return-time law `p(n) = P_a(τ_α = n)` is an increment law when `L(a, α) = 1`. -/
theorem isIncrementLaw_entryLaw (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) {a : X} (hL : hitProb P α a = 1) :
    IsIncrementLaw (entryLaw P hα (Measure.dirac a)) := by
  refine ⟨entryLaw_nonneg P hα _, rfl, ?_⟩
  have h := hasSum_entryLaw P hα (Measure.dirac a)
  rwa [lintegral_dirac' _ (measurable_hitProb P hα), hL, ENNReal.toReal_one] at h

/-- The tails of the return-time law: `Σ_{j > n} p(j) = P_a(τ_α ≥ n + 1)`. -/
theorem renewalTail_entryLaw (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) (n : ℕ) :
    renewalTail (entryLaw P hα (Measure.dirac a)) n = (tabooKernel P hα n a univ).toReal := by
  have h := tabooSeq_univ_toReal P hα (Measure.dirac a) n
  rw [tabooSeq, dirac_kernel, measureReal_def, Measure.dirac_apply_of_mem (mem_univ a),
    ENNReal.toReal_one] at h
  rw [h]
  rfl

/-- `E_a[τ_α] = Σₙ P_a(τ_α ≥ n + 1)`, the real form of (10.12). -/
theorem hasSum_tabooKernel_univ (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) (hm : meanReturnTime P α a ≠ ∞) :
    HasSum (fun n => (tabooKernel P hα n a univ).toReal) (meanReturnTime P α a).toReal := by
  have h : meanReturnTime P α a = ∑' n, tabooKernel P hα n a univ := by
    rw [meanReturnTime_eq_tabooPotKernel P hα, tabooPotKernel, Kernel.sum_apply,
      Measure.sum_apply _ MeasurableSet.univ]
  rw [h] at hm ⊢
  rw [ENNReal.tsum_toReal_eq fun n => ne_top_of_le_ne_top ENNReal.one_ne_top
    (tabooKernel_apply_le_one P hα n a univ)]
  exact ENNReal.hasSum_toReal hm

/-- The mean of the return-time law is the mean return time: `m_p = E_a[τ_α]`, when
`L(a, α) = 1` and `E_a[τ_α] < ∞`. -/
theorem incrMean_entryLaw (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) {a : X} (hL : hitProb P α a = 1) (hm : meanReturnTime P α a ≠ ∞) :
    incrMean (entryLaw P hα (Measure.dirac a)) = (meanReturnTime P α a).toReal := by
  have hp := isIncrementLaw_entryLaw P hα hL
  have h1 : HasSum (renewalTail (entryLaw P hα (Measure.dirac a)))
      (meanReturnTime P α a).toReal := by
    rw [show renewalTail (entryLaw P hα (Measure.dirac a)) =
      fun n => (tabooKernel P hα n a univ).toReal from funext (renewalTail_entryLaw P hα a)]
    exact hasSum_tabooKernel_univ P hα a hm
  exact (hasSum_renewalTail hp ((summable_renewalTail_iff hp).1 h1.summable)).unique h1

/-! ### Consequences of the representation `π = π(α) μ°_α` -/

/-- If `π = π(α) μ°_α` is a probability, then `π(α) E_a[τ_α] = 1`. -/
theorem measure_atom_mul_meanReturnTime (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα a) : π α * meanReturnTime P α a = 1 := by
  have h := congrArg (fun m : Measure X => m univ) hπ
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ] at h
  rw [← atomMeasure_univ P hα a, ← h]

/-- If `π = π(α) μ°_α` is a probability, then `E_a[τ_α] < ∞`. -/
theorem meanReturnTime_ne_top_of_rep (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα a) : meanReturnTime P α a ≠ ∞ := by
  intro htop
  have h := measure_atom_mul_meanReturnTime P hα a hπ
  rw [htop] at h
  rcases eq_or_ne (π α) 0 with h0 | h0
  · rw [h0, zero_mul] at h; exact zero_ne_one h
  · rw [ENNReal.mul_top h0] at h; exact ENNReal.top_ne_one h

/-- If `π = π(α) μ°_α` is a probability, then `π(α) ≠ 0`. -/
theorem measure_atom_ne_zero_of_rep (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα a) : π α ≠ 0 := by
  intro h0
  have h := measure_atom_mul_meanReturnTime P hα a hπ
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- If `π = π(α) μ°_α` is a probability, then `π(α) = E_a[τ_α]⁻¹`, the real form of (10.14). -/
theorem measure_atom_toReal_of_rep (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα a) : (π α).toReal = ((meanReturnTime P α a).toReal)⁻¹ := by
  have h := congrArg ENNReal.toReal (measure_atom_mul_meanReturnTime P hα a hπ)
  rw [ENNReal.toReal_mul, ENNReal.toReal_one] at h
  exact eq_inv_of_mul_eq_one_left h

/-- `t₁(m + 1) = P_a(τ_α ≥ m + 1)` is summable when `E_a[τ_α] < ∞`. -/
theorem summable_tabooKernel_univ (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) (hm : meanReturnTime P α a ≠ ∞) :
    Summable fun m => (tabooKernel P hα m a univ).toReal :=
  (hasSum_tabooKernel_univ P hα a hm).summable

/-- `t_f(m + 1)` is summable for bounded `f` when `E_a[τ_α] < ∞`. -/
theorem summable_lastExitSeq (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) (hm : meanReturnTime P α a ≠ ∞) {f : X → ℝ≥0∞} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) : Summable fun m => lastExitSeq P hα a f (m + 1) :=
  Summable.of_nonneg_of_le (fun m => lastExitSeq_nonneg P hα a f (m + 1))
    (fun m => lastExitSeq_le P hα a hC hfC m)
    ((summable_tabooKernel_univ P hα a hm).mul_left C.toReal)

/-- `|g ∗ t (n)| ≤ |g| ∗ t (n)` for `t ≥ 0`. -/
theorem abs_realConv_le_of_nonneg {g t : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n) (n : ℕ) :
    |realConv g t n| ≤ realConv (fun k => |g k|) t n := by
  rw [realConv, realConv]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (ht _)]

/-- `c ∗ t (n) = c Σ_{j ≤ n} t(j)` for a constant sequence `c`. -/
theorem realConv_const_left (c : ℝ) (t : ℕ → ℝ) (n : ℕ) :
    realConv (fun _ => c) t n = c * ∑ j ∈ range (n + 1), t j := by
  rw [realConv_comm, realConv_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### Theorem 13.2.5 -/

/-- **(13.47)**, the first Regenerative Decomposition: for `n ≥ 1` and bounded measurable
`f ≥ 0`, `|E_λ[f(Φₙ)] − E_α[f(Φₙ)]| ≤ E_λ[f(Φₙ); τ_α ≥ n] + |a_λ ∗ u − u| ∗ t_f (n)`. -/
theorem regenerative_decomposition_47 {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (n : ℕ) :
    |(∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ μ)).toReal -
        (∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a).toReal| ≤
      (∫⁻ y, f y ∂tabooSeq P hα.1 μ n).toReal +
        realConv (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k -
          atomRenewal P α a k|) (lastExitSeq P hα.1 a f) (n + 1) := by
  rw [lintegral_comp_pow_succ_atom_toReal hα ha μ hC hfC,
    lintegral_pow_succ_atom_toReal hα ha hC hfC, add_sub_assoc, ← Pi.sub_apply (realConv _ _),
    ← realConv_sub_left]
  refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_of_nonneg ENNReal.toReal_nonneg)) ?_)
  exact abs_realConv_le_of_nonneg (lastExitSeq_nonneg P hα.1 a f) (n + 1)

/-- The identity behind (13.48): for `n ≥ 1`, bounded measurable `f ≥ 0` and `π = π(α) μ°_α`,
`λPⁿ(f) − π(f) = λ _αPⁿ(f) + (a_λ ∗ u − π(α)) ∗ t_f (n) − π(α) Σ_{j > n} t_f(j)`. -/
theorem regenerative_identity_48 {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a) (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (n : ℕ) :
    (∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ μ)).toReal - (∫⁻ y, f y ∂π).toReal =
      (∫⁻ y, f y ∂tabooSeq P hα.1 μ n).toReal +
        realConv (fun k => realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - (π α).toReal)
          (lastExitSeq P hα.1 a f) (n + 1) -
        (π α).toReal * ∑' i, lastExitSeq P hα.1 a f (i + n + 2) := by
  have hm := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  have hs := summable_lastExitSeq P hα.1 a hm hC hfC
  have hsplit := hs.sum_add_tsum_nat_add (n + 1)
  rw [lintegral_comp_pow_succ_atom_toReal hα ha μ hC hfC,
    lintegral_eq_tsum_lastExitSeq P hα.1 a hπ hC hfC, ← hsplit,
    show (fun k => realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - (π α).toReal) =
      realConv (entryLaw P hα.1 μ) (atomRenewal P α a) - fun _ => (π α).toReal from rfl,
    realConv_sub_left, Pi.sub_apply, realConv_const_left,
    Finset.sum_range_succ' (lastExitSeq P hα.1 a f) (n + 1), lastExitSeq_zero, add_zero]
  have hidx : ∀ i, lastExitSeq P hα.1 a f (i + (n + 1) + 1) = lastExitSeq P hα.1 a f (i + n + 2) :=
    fun i => by rw [show i + (n + 1) + 1 = i + n + 2 by ring]
  simp_rw [hidx]
  ring

/-- **(13.48)**, the second Regenerative Decomposition: for `n ≥ 1`, bounded measurable `f ≥ 0`
and `π = π(α) μ°_α`, `|E_λ[f(Φₙ)] − π(f)| ≤ E_λ[f(Φₙ); τ_α ≥ n] + |a_λ ∗ u − π(α)| ∗ t_f (n) +
π(α) Σ_{j > n} t_f(j)`. -/
theorem regenerative_decomposition_48 {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a) (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ y, f y ≤ C) (n : ℕ) :
    |(∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ μ)).toReal - (∫⁻ y, f y ∂π).toReal| ≤
      (∫⁻ y, f y ∂tabooSeq P hα.1 μ n).toReal +
        realConv (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - (π α).toReal|)
          (lastExitSeq P hα.1 a f) (n + 1) +
        (π α).toReal * ∑' i, lastExitSeq P hα.1 a f (i + n + 2) := by
  rw [regenerative_identity_48 hα ha hπ μ hC hfC n]
  have h1 := abs_realConv_le_of_nonneg
    (g := fun k => realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - (π α).toReal)
    (lastExitSeq_nonneg P hα.1 a f) (n + 1)
  have h2 : 0 ≤ (π α).toReal * ∑' i, lastExitSeq P hα.1 a f (i + n + 2) :=
    mul_nonneg ENNReal.toReal_nonneg (tsum_nonneg fun i => lastExitSeq_nonneg P hα.1 a f _)
  have h3 : 0 ≤ (∫⁻ y, f y ∂tabooSeq P hα.1 μ n).toReal := ENNReal.toReal_nonneg
  have hB := abs_le.1 h1
  rw [abs_le]
  constructor <;> linarith

/-- An accessible atom of a recurrent chain represents every invariant probability:
`π = π(α) μ°_α` (Theorem 10.2.1 (ii)). -/
theorem eq_smul_atomMeasure_of_accessible {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) (hrec : IsRecurrentChain P ψ) {a : X} (ha : a ∈ α)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    π = π α • atomMeasure P h.1.1 a :=
  theorem_10_2_1_ii_smul h hrec ha hπ.isSubinvariant
    (hπ.isSubinvariant.pos_of_pos h.2.1.2.1 (IsProbabilityMeasure.ne_zero π) h.1.1 h.2.2).ne'
    (measure_ne_top π α)

/-- **Theorem 13.2.5** (MT p. 325), the Regenerative Decompositions. If `α` is an accessible atom
of a positive chain with invariant probability `π`, then for every probability `λ`, every bounded
measurable `f ≥ 0` and every `n ≥ 1` (here `n + 1`), (13.47) and (13.48) hold, with
`E_π[f(Φₙ)] = π(f)`. -/
theorem theorem_13_2_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) (hpos : IsPositive P ψ) {a : X} (ha : a ∈ α)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ y, f y ≤ C) (n : ℕ) :
    |(∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ μ)).toReal -
        (∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a).toReal| ≤
      (∫⁻ y, f y ∂tabooSeq P h.1.1 μ n).toReal +
        realConv (fun k => |realConv (entryLaw P h.1.1 μ) (atomRenewal P α a) k -
          atomRenewal P α a k|) (lastExitSeq P h.1.1 a f) (n + 1) ∧
    |(∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ μ)).toReal -
        (∫⁻ y, f y ∂((P ^ (n + 1) : Kernel X X) ∘ₘ π)).toReal| ≤
      (∫⁻ y, f y ∂tabooSeq P h.1.1 μ n).toReal +
        realConv (fun k => |realConv (entryLaw P h.1.1 μ) (atomRenewal P α a) k - (π α).toReal|)
          (lastExitSeq P h.1.1 a f) (n + 1) +
        (π α).toReal * ∑' i, lastExitSeq P h.1.1 a f (i + n + 2) := by
  refine ⟨regenerative_decomposition_47 h.1 ha μ hC hfC n, ?_⟩
  rw [(hπ.pow (n + 1) :)]
  exact regenerative_decomposition_48 h.1 ha
    (eq_smul_atomMeasure_of_accessible h (proposition_10_1_1 hpos) ha hπ) μ hC hfC n

/-! ### The total variation bound -/

/-- `(ofReal x).toReal − (ofReal (−x)).toReal = x`. -/
theorem toReal_ofReal_sub_ofReal_neg (x : ℝ) :
    (ENNReal.ofReal x).toReal - (ENNReal.ofReal (-x)).toReal = x := by
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.2 hx)]; ring
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.2 hx)]; ring

/-- `(ofReal x).toReal + (ofReal (−x)).toReal = |x|`. -/
theorem toReal_ofReal_add_ofReal_neg (x : ℝ) :
    (ENNReal.ofReal x).toReal + (ENNReal.ofReal (-x)).toReal = |x| := by
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.2 hx), abs_of_nonpos hx]; ring
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.2 hx), abs_of_nonneg hx]; ring

/-- `g ∗ t_f (n + 1) = Σ_{k ≤ n} g(k) ∫ f d(_αPⁿ⁻ᵏ⁺¹(a, ·))`. -/
theorem realConv_lastExitSeq_succ (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X)
    (f : X → ℝ≥0∞) (g : ℕ → ℝ) (n : ℕ) :
    realConv g (lastExitSeq P hα a f) (n + 1) =
      ∑ k ∈ range (n + 1), g k * (∫⁻ y, f y ∂tabooKernel P hα (n - k) a).toReal := by
  rw [realConv_eq_sum_range, Finset.sum_range_succ, Nat.sub_self, lastExitSeq_zero, mul_zero,
    add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show n + 1 - k = (n - k) + 1 by have := Finset.mem_range.1 hk; omega, lastExitSeq_succ]

/-- **The total variation form of (13.48)** (the proof of Theorem 13.3.1 (i), (13.54)–(13.56)):
if `π = π(α) μ°_α`, then for every finite `λ` and `n ≥ 0`,
`‖λPⁿ⁺¹ − π‖ ≤ P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − π(α)| ∗ t₁ (n + 1) + π(α) Σ_{j > n + 1} t₁(j)`,
where `t₁(j) = P_a(τ_α ≥ j)`. The bound does not depend on the test function. -/
theorem tvNorm_comp_pow_succ_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π ≤ (tabooSeq P hα.1 μ n univ).toReal +
      realConv (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - (π α).toReal|)
        (lastExitSeq P hα.1 a 1) (n + 1) +
      (π α).toReal * ∑' i, lastExitSeq P hα.1 a 1 (i + n + 2) := by
  have := isMarkovKernel_pow P (n + 1)
  have hm := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  set c := (π α).toReal with hc
  set au := realConv (entryLaw P hα.1 μ) (atomRenewal P α a) with hau
  set T : ℕ → Measure X := fun k => tabooKernel P hα.1 k a with hT
  have hTfin : ∀ k B, T k B ≠ ∞ := fun k B =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hα.1 k a B)
  have hSfin : ∀ B, ∑' i, T (i + n + 1) B ≠ ∞ := fun B => by
    refine ne_top_of_le_ne_top (b := meanReturnTime P α a) hm ?_
    rw [meanReturnTime_eq_tabooPotKernel P hα.1, tabooPotKernel, Kernel.sum_apply,
      Measure.sum_apply _ MeasurableSet.univ]
    calc ∑' i, T (i + n + 1) B ≤ ∑' i, T (i + n + 1) univ :=
          ENNReal.tsum_le_tsum fun i => measure_mono (subset_univ B)
      _ ≤ ∑' k, T k univ := ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun i => i + n + 1) (fun i j hij => by simpa using hij) (fun k => T k univ)
  have hE : ∀ B, tabooSeq P hα.1 μ n B ≠ ∞ := fun B =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα.1 μ n B)
  set σ₁ : Measure X := tabooSeq P hα.1 μ n +
    ∑ k ∈ range (n + 1), ENNReal.ofReal (au k - c) • T (n - k) with hσ₁
  set σ₂ : Measure X := ∑ k ∈ range (n + 1), ENNReal.ofReal (c - au k) • T (n - k) +
    π α • Measure.sum (fun i => T (i + n + 1)) with hσ₂
  have hσ₁B : ∀ B, σ₁ B = tabooSeq P hα.1 μ n B +
      ∑ k ∈ range (n + 1), ENNReal.ofReal (au k - c) * T (n - k) B := fun B => by
    rw [hσ₁, Measure.add_apply, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
  have hσ₂B : ∀ B, MeasurableSet B → σ₂ B =
      ∑ k ∈ range (n + 1), ENNReal.ofReal (c - au k) * T (n - k) B +
        π α * ∑' i, T (i + n + 1) B := fun B hB => by
    rw [hσ₂, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.sum_apply _ hB]
    simp only [Measure.smul_apply, smul_eq_mul]
  have hσ₁fin : ∀ B, σ₁ B ≠ ∞ := fun B => by
    rw [hσ₁B]
    exact ENNReal.add_ne_top.2 ⟨hE B, ENNReal.sum_ne_top.2 fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)⟩
  have hσ₂fin : ∀ B, MeasurableSet B → σ₂ B ≠ ∞ := fun B hB => by
    rw [hσ₂B B hB]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _),
      ENNReal.mul_ne_top (measure_ne_top π α) (hSfin B)⟩
  have : IsFiniteMeasure σ₁ := ⟨lt_top_iff_ne_top.2 (hσ₁fin univ)⟩
  have : IsFiniteMeasure σ₂ := ⟨lt_top_iff_ne_top.2 (hσ₂fin univ MeasurableSet.univ)⟩
  have hσ₁R : ∀ B, σ₁.real B = (tabooSeq P hα.1 μ n B).toReal +
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (au k - c)).toReal * (T (n - k) B).toReal :=
    fun B => by
      rw [measureReal_def, hσ₁B, ENNReal.toReal_add (hE B) (ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)), ENNReal.toReal_sum fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)]
      simp_rw [ENNReal.toReal_mul]
  have hσ₂R : ∀ B, MeasurableSet B → σ₂.real B =
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (c - au k)).toReal * (T (n - k) B).toReal +
        c * ∑' i, (T (i + n + 1) B).toReal := fun B hB => by
    rw [measureReal_def, hσ₂B B hB, ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _))
        (ENNReal.mul_ne_top (measure_ne_top π α) (hSfin B)), ENNReal.toReal_sum fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _), ENNReal.toReal_mul,
      ENNReal.tsum_toReal_eq fun i => hTfin _ _]
    simp_rw [ENNReal.toReal_mul]
    rfl
  have hind : ∀ B, MeasurableSet B → ∀ y, B.indicator (1 : X → ℝ≥0∞) y ≤ 1 := fun B _ y => by
    by_cases hy : y ∈ B <;> simp [hy]
  refine (tvNorm_le_of_sub_eq (σ₁ := σ₁) (σ₂ := σ₂) fun B hB => ?_).trans (le_of_eq ?_)
  · have hid := regenerative_identity_48 hα ha hπ μ ENNReal.one_ne_top (hind B hB) n
    simp only [lintegral_indicator_one hB] at hid
    rw [measureReal_def, measureReal_def, hid, hσ₁R, hσ₂R B hB,
      realConv_lastExitSeq_succ]
    simp only [lintegral_indicator_one hB]
    have htail : ∀ i, lastExitSeq P hα.1 a (B.indicator 1) (i + n + 2) = (T (i + n + 1) B).toReal :=
      fun i => by rw [show i + n + 2 = (i + n + 1) + 1 by ring, lastExitSeq_indicator_succ _ _ _ hB]
    simp_rw [htail]
    have hk : ∀ k ∈ range (n + 1), (au k - c) * (T (n - k) B).toReal =
        (ENNReal.ofReal (au k - c)).toReal * (T (n - k) B).toReal -
          (ENNReal.ofReal (c - au k)).toReal * (T (n - k) B).toReal := fun k _ => by
      rw [← sub_mul, show c - au k = -(au k - c) by ring, toReal_ofReal_sub_ofReal_neg]
    rw [Finset.sum_congr rfl hk, Finset.sum_sub_distrib]
    ring
  · rw [hσ₁R, hσ₂R univ MeasurableSet.univ, realConv_lastExitSeq_succ]
    have htail : ∀ i, lastExitSeq P hα.1 a 1 (i + n + 2) = (T (i + n + 1) univ).toReal :=
      fun i => by
        rw [show i + n + 2 = (i + n + 1) + 1 by ring, lastExitSeq_succ]
        simp [T]
    simp_rw [htail]
    have hk : ∀ k ∈ range (n + 1), |au k - c| * (∫⁻ y, (1 : X → ℝ≥0∞) y ∂T (n - k)).toReal =
        (ENNReal.ofReal (au k - c)).toReal * (T (n - k) univ).toReal +
          (ENNReal.ofReal (c - au k)).toReal * (T (n - k) univ).toReal := fun k _ => by
      rw [← add_mul, show c - au k = -(au k - c) by ring, toReal_ofReal_add_ofReal_neg]
      simp [T]
    rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib]
    ring

end MeynTweedie.Epilogue
