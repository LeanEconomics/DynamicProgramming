/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.GeometricErgodicTheorem

/-!
# `f`-geometric ergodicity implies `f`-geometric regularity (MT Theorem 15.4.2)

Meyn and Tweedie, Theorem 15.4.2, pp. 386–387, for chains with an accessible atom `α ∋ a`.
`t_j = ∫ f d(_αP^{j+1}(a, ·))`, `u(k) = Pᵏ(a, α)` and `c = π(α)`.

**The argument** (15.44)–(15.46), done in `[0, ∞]` with truncated sums.
* `lintegral_le_add_fNorm`: `ν(f) ≤ μ(f) + ‖μ − ν‖_f` (the test function `f` itself).
* `atom_tail_le`: `c Σ_{j > n} t_j ≤ ‖Pⁿ⁺¹(a, ·) − π‖_f + Σ_{k ≤ n} |u(k) − c| t_{n−k}`, from the
  last-exit decomposition `Pⁿ⁺¹(a, f) = Σ_{k ≤ n} u(k) t_{n−k}` and `π(f) = c Σ_j t_j`.
* `tsum_pow_mul_eq_add`: `Σ sʲ g_j = Σ g_j + (s − 1) Σₙ sⁿ Σ_{j > n} g_j` (Fubini, (15.46)).
* `theorem_15_4_2_atom`: with `t` cut off at `N` (`g_j = t_j 1_{j<N}`, `Y_N = Σ_{j<N} sʲ t_j`),
  multiplying the tail bound by `sⁿ` and summing gives
  `c Y_N ≤ c Σ t_j + (s − 1) E + (s − 1) D Y_N`, with `E = Σ sⁿ ‖Pⁿ⁺¹(a, ·) − π‖_f` and
  `D = Σ sᵏ |u(k) − c|`, both at most `R = Σ rⁿ ‖Pⁿ(a, ·) − π‖_f` (as
  `|u(k) − c| ≤ ‖Pᵏ(a, ·) − π‖_f` for `f ≥ 1`). Choosing `s ≤ r` with `(s − 1) R ≤ c/2`
  bounds `Y_N` uniformly in `N`, so `Σ sʲ t_j < ∞` and `U_α^{(s)}(a, f) = s Σ sʲ t_j < ∞`.

**Results.**
* **Theorem 15.4.2** for chains with an accessible atom (`theorem_15_4_2_atom`, p. 386): if
  `π(f) < ∞` and `Σₙ rⁿ ‖Pⁿ(a, ·) − π‖_f < ∞` for some `r > 1`, then `U_α^{(s)}(a, f) < ∞` for
  some `s > 1` and the set `{U_α^{(s)}(·, f) < ∞}` is full and absorbing. If also `f` is bounded
  on `α`, then `α` is `f`-Kendall and the chain is `f`-geometrically regular on a full absorbing
  set (`theorem_15_4_2_atom_regular`). Boundedness on `α` is an added hypothesis: `IsFKendall`
  bounds `G_α^{(s)}(x, f)` uniformly over `x ∈ α`, and that includes the term `f(x)`.

**Correction.** (15.44) is printed as
`Pⁿ(α, f) − π(f) ≥ (u − π(α)) ∗ t_f(n) + π(α) Σ_{j > n} t_f(j)`; the regenerative
decomposition gives equality with `− π(α) Σ_{j > n} t_f(j)`, so the printed inequality fails
whenever the tail is positive (`eq_15_44_counterexample`, the flip chain at `n = 1`). The
argument goes through with `π(f) − Pⁿ(α, f)` in place of `Pⁿ(α, f) − π(f)` (`atom_tail_le`).

**The general case.** The book's reduction of the general case to the atom (p. 387) needs a
`ν`-average of `x ↦ Σ rⁿ ‖Pⁿ(x, ·) − π‖_f` that need not be finite. `GeometricConverseGeneral`
proves the theorem without an atom by another route (`theorem_15_4_2`).
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- **The test function `f`**: `ν(f) ≤ μ(f) + ‖μ − ν‖_f` when `μ(f), ν(f) < ∞`. -/
theorem lintegral_le_add_fNorm {f : X → ℝ≥0∞} (hf : Measurable f) {μ ν : Measure X}
    (hμ : ∫⁻ x, f x ∂μ ≠ ∞) (hν : ∫⁻ x, f x ∂ν ≠ ∞) :
    ∫⁻ x, f x ∂ν ≤ ∫⁻ x, f x ∂μ + fNorm f μ ν := by
  set g : X → ℝ := fun x => (f x).toReal with hg
  have hgt : IsFTest f μ ν g := ⟨hf.ennreal_toReal, fun x => by
      rw [hg, abs_of_nonneg ENNReal.toReal_nonneg]; exact ENNReal.ofReal_toReal_le,
    integrable_toReal_of_lintegral_ne_top hf.aemeasurable hμ,
    integrable_toReal_of_lintegral_ne_top hf.aemeasurable hν⟩
  have h := ofReal_abs_integral_sub_le_fNorm hgt
  rw [integral_toReal hf.aemeasurable (ae_lt_top hf hμ),
    integral_toReal hf.aemeasurable (ae_lt_top hf hν)] at h
  set a := (∫⁻ x, f x ∂μ).toReal
  set b := (∫⁻ x, f x ∂ν).toReal
  calc ∫⁻ x, f x ∂ν = ENNReal.ofReal b := (ENNReal.ofReal_toReal hν).symm
    _ ≤ ENNReal.ofReal (a + |a - b|) := ENNReal.ofReal_le_ofReal (by
        have := le_abs_self (b - a); rw [abs_sub_comm]; linarith)
    _ = ENNReal.ofReal a + ENNReal.ofReal |a - b| :=
        ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _)
    _ ≤ ∫⁻ x, f x ∂μ + fNorm f μ ν := add_le_add (le_of_eq (ENNReal.ofReal_toReal hμ)) h

/-- The last-exit decomposition integrated: `Pⁿ⁺¹(a, f) = Σ_{k ≤ n} u(k) t_{n−k}` in `[0, ∞]`. -/
theorem IsAtom.lintegral_pow_succ_eq {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (f : X → ℝ≥0∞) (n : ℕ) :
    ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a = ∑ k ∈ range (n + 1),
      (P ^ k : Kernel X X) a α * ∫⁻ y, f y ∂tabooKernel P hα.1 (n - k) a := by
  rw [hα.pow_succ_lastExit ha n, lintegral_add_measure, lintegral_finsetSum_measure,
    Finset.sum_range_succ']
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [pow_zero_apply, Measure.dirac_apply' a hα.1, indicator_of_mem ha, Pi.one_apply, one_mul,
    Nat.sub_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show n - (j + 1) = n - 1 - j by omega]

/-- **The tail bound behind (15.44)**, corrected: for an atom with `π = π(α) μ°_α`, `π(f) < ∞`,
`c Σ_{j > n} t_j ≤ ‖Pⁿ⁺¹(a, ·) − π‖_f + Σ_{k ≤ n} |u(k) − c| t_{n−k}`. -/
theorem atom_tail_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α) {a : X}
    (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π] (hπ : π = π α • atomMeasure P hα.1 a)
    (hinv : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞)
    (n : ℕ) :
    π α * ∑' i, ∫⁻ y, f y ∂tabooKernel P hα.1 (i + n + 1) a ≤
      fNorm f ((P ^ (n + 1) : Kernel X X) a) π + ∑ k ∈ range (n + 1),
        ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - (π α).toReal| *
          ∫⁻ y, f y ∂tabooKernel P hα.1 (n - k) a := by
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with ht
  set c := π α with hc
  have hct : c ≠ ∞ := measure_ne_top π α
  have hU : ∑' j, t j = tabooPotFn P α f a := tsum_lintegral_tabooKernel P hα.1 hf a
  have hUt : tabooPotFn P α f a ≠ ∞ := tabooPotFn_ne_top_of_rep P hα.1 a hπ hf hπf
  have htt : ∀ j, t j ≠ ∞ := fun j => ne_top_of_le_ne_top (hU ▸ hUt) (ENNReal.le_tsum j)
  have hπfeq : ∫⁻ y, f y ∂π = c * ∑' j, t j := by rw [hU]; exact lintegral_eq_atom P hα.1 a hπ hf
  have hPf := hα.lintegral_pow_succ_eq ha f n
  have hPft : ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a ≠ ∞ := by
    have h1 := hα.mul_lintegral_pow_le ha hinv hf n
    intro htop
    rw [htop, ENNReal.mul_top (measure_atom_ne_zero_of_rep P hα.1 a hπ)] at h1
    exact hπf (top_le_iff.1 h1)
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - c.toReal|
    with hw
  have hu : ∀ k, (P ^ k : Kernel X X) a α ≤ c + w k := fun k => by
    have := isMarkovKernel_pow P k
    have hk : (P ^ k : Kernel X X) a α ≠ ∞ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hk, ← ENNReal.ofReal_toReal hct, hw, ← ENNReal.ofReal_add
      ENNReal.toReal_nonneg (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [le_abs_self (((P ^ k : Kernel X X) a α).toReal - c.toReal)]
  -- `c Σ_{j ≤ n} t_j + c Σ_{j > n} t_j = π(f) ≤ Pⁿ⁺¹(a, f) + ‖·‖ ≤ c Σ_{j ≤ n} t_j + E + ‖·‖`
  have hsplit : c * ∑ j ∈ range (n + 1), t j + c * ∑' i, t (i + n + 1) = ∫⁻ y, f y ∂π := by
    have h := Summable.sum_add_tsum_nat_add' (f := t) (k := n + 1) ENNReal.summable
    rw [hπfeq, ← mul_add, ← h]
    rfl
  have hreflect : ∑ j ∈ range (n + 1), t j = ∑ k ∈ range (n + 1), t (n - k) :=
    (Finset.sum_range_reflect t (n + 1)).symm
  have hupper : ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a ≤
      c * ∑ j ∈ range (n + 1), t j + ∑ k ∈ range (n + 1), w k * t (n - k) := by
    rw [hPf, hreflect, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => by rw [← add_mul]; exact mul_le_mul' (hu k) le_rfl
  have hlow := lintegral_le_add_fNorm hf hPft hπf (μ := (P ^ (n + 1) : Kernel X X) a)
  have hfin : c * ∑ j ∈ range (n + 1), t j ≠ ∞ :=
    ENNReal.mul_ne_top hct (ENNReal.sum_ne_top.2 fun j _ => htt j)
  have key : c * ∑ j ∈ range (n + 1), t j + c * ∑' i, t (i + n + 1) ≤
      c * ∑ j ∈ range (n + 1), t j + (fNorm f ((P ^ (n + 1) : Kernel X X) a) π +
        ∑ k ∈ range (n + 1), w k * t (n - k)) := by
    rw [hsplit]
    calc ∫⁻ y, f y ∂π ≤ ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a +
          fNorm f ((P ^ (n + 1) : Kernel X X) a) π := hlow
      _ ≤ c * ∑ j ∈ range (n + 1), t j + ∑ k ∈ range (n + 1), w k * t (n - k) +
          fNorm f ((P ^ (n + 1) : Kernel X X) a) π := add_le_add hupper le_rfl
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_left hfin).1 key

/-- `Σⱼ sʲ g_j = Σⱼ g_j + (s − 1) Σₙ sⁿ Σ_{j > n} g_j` in `[0, ∞]`, for `s ≥ 1`. -/
theorem tsum_pow_mul_eq_add {s : ℝ≥0∞} (hs : 1 ≤ s) (g : ℕ → ℝ≥0∞) :
    ∑' j, s ^ j * g j = ∑' j, g j + (s - 1) * ∑' n, s ^ n * ∑' i, g (i + n + 1) := by
  have htail : ∀ n, ∑' i, g (i + n + 1) = ∑' j, {j : ℕ | n < j}.indicator g j := fun n => by
    have h := Summable.sum_add_tsum_nat_add' (f := fun j => {j : ℕ | n < j}.indicator g j)
      (k := n + 1) ENNReal.summable
    rw [← h, Finset.sum_eq_zero fun j hj => indicator_of_notMem (by
      change ¬ n < j; have := Finset.mem_range.1 hj; omega) g, zero_add]
    exact tsum_congr fun i => (indicator_of_mem (show n < i + (n + 1) by omega) g).symm
  have hswap : ∑' n, s ^ n * ∑' i, g (i + n + 1) = ∑' j, (∑ n ∈ range j, s ^ n) * g j := by
    simp_rw [htail, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun j => ?_
    rw [Finset.sum_mul, tsum_eq_sum (s := range j) fun n hn => by
      rw [indicator_of_notMem (show j ∉ {j : ℕ | n < j} from fun h => hn (Finset.mem_range.2 h)),
        mul_zero]]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [indicator_of_mem (show j ∈ {j : ℕ | n < j} from Finset.mem_range.1 hn)]
  rw [hswap, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun j => ?_
  rw [pow_eq_one_add_sum hs j, add_mul, one_mul, mul_assoc]

/-- **Theorem 15.4.2** (MT p. 386), for a chain with an accessible atom `α ∋ a`: if `f ≥ 1`,
`π(f) < ∞` and `Σₙ rⁿ ‖Pⁿ(a, ·) − π‖_f < ∞` for some `r > 1`, then `U_α^{(s)}(a, f) < ∞` for some
`s > 1`, and `{U_α^{(s)}(·, f) < ∞}` is full and absorbing. -/
theorem theorem_15_4_2_atom {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ y, f y ∂π ≠ ∞) {r : ℝ≥0∞} (hr : 1 < r)
    (hR : ∑' n, r ^ n * fNorm f ((P ^ n : Kernel X X) a) π ≠ ∞) :
    ∃ s : ℝ≥0∞, 1 < s ∧ s ≠ ∞ ∧ geomTaboo P α s f a ≠ ∞ ∧
      IsFull ψ {x | geomTaboo P α s f x ≠ ∞} ∧ IsAbsorbing P {x | geomTaboo P α s f x ≠ ∞} := by
  have hα := h.1
  obtain ⟨hπ, -⟩ := atom_rep_of_invariant h ha hinv
  have hc0 : π α ≠ 0 := measure_atom_ne_zero_of_rep P hα.1 a hπ
  have hct : π α ≠ ∞ := measure_ne_top π α
  have hU : ∑' j, ∫⁻ y, f y ∂tabooKernel P hα.1 j a ≠ ∞ := by
    rw [tsum_lintegral_tabooKernel P hα.1 hf a]
    exact tabooPotFn_ne_top_of_rep P hα.1 a hπ hf hπf
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with ht
  set e : ℕ → ℝ≥0∞ := fun n => fNorm f ((P ^ n : Kernel X X) a) π with he
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - (π α).toReal|
    with hw
  set R := ∑' n, r ^ n * e n with hRdef
  set c := π α with hc
  have htt : ∀ j, t j ≠ ∞ := fun j => ne_top_of_le_ne_top hU (ENNReal.le_tsum j)
  have hwe : ∀ k, w k ≤ e k := fun k => by
    have := isMarkovKernel_pow P k
    have h1 := ofReal_abs_measureReal_sub_le_fNorm hf1 (μ := (P ^ k : Kernel X X) a) (ν := π) hα.1
    rw [measureReal_def, measureReal_def] at h1
    exact h1
  -- the choice of `s`: `1 < s ≤ r` and `(s − 1) R ≤ c / 2`
  have hR1 : R + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hR, ENNReal.one_ne_top⟩
  have hR10 : R + 1 ≠ 0 := by simp
  have hc2 : c / 2 ≠ 0 := (ENNReal.div_pos hc0 ENNReal.ofNat_ne_top).ne'
  have hc2t : c / 2 ≠ ∞ := ENNReal.div_ne_top hct two_ne_zero
  set ε := c / 2 / (R + 1) with hε
  have hε0 : 0 < ε := ENNReal.div_pos hc2 hR1
  have hεt : ε ≠ ∞ := ENNReal.div_ne_top hc2t hR10
  have hεR : ε * R ≤ c / 2 := calc ε * R ≤ ε * (R + 1) := mul_le_mul' le_rfl le_self_add
      _ = c / 2 := ENNReal.div_mul_cancel hR10 hR1
  set s := min r (1 + ε) with hs
  have hs1 : 1 < s := lt_min hr (ENNReal.lt_add_right ENNReal.one_ne_top hε0.ne')
  have hsr : s ≤ r := min_le_left _ _
  have hst : s ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hεt⟩) (min_le_right _ _)
  have hs1ε : s - 1 ≤ ε := tsub_le_iff_left.2 (min_le_right _ _)
  have hsn : ∀ n, s ^ n ≤ r ^ n := fun n => pow_le_pow_left₀ bot_le hsr n
  have hD : ∑' k, s ^ k * w k ≤ R := ENNReal.tsum_le_tsum fun k => mul_le_mul' (hsn k) (hwe k)
  have hE : ∑' n, s ^ n * e (n + 1) ≤ R := by
    calc ∑' n, s ^ n * e (n + 1) ≤ ∑' n, r ^ (n + 1) * e (n + 1) := ENNReal.tsum_le_tsum fun n =>
          mul_le_mul' ((hsn n).trans (pow_le_pow_right₀ hr.le n.le_succ)) le_rfl
      _ ≤ R := by
        rw [hRdef, ← Summable.sum_add_tsum_nat_add' (f := fun n => r ^ n * e n) (k := 1)
          ENNReal.summable]
        exact le_add_self
  -- the truncated sums are bounded uniformly
  have hY : ∀ N, ∑ j ∈ range N, s ^ j * t j ≤ (c * ∑' j, t j + (s - 1) * R) / (c / 2) := by
    intro N
    set g : ℕ → ℝ≥0∞ := fun j => if j < N then t j else 0 with hg
    have hgt : ∀ j, g j ≤ t j := fun j => by
      simp only [hg]; split_ifs
      · exact le_rfl
      · exact bot_le
    have hYg : ∑' j, s ^ j * g j = ∑ j ∈ range N, s ^ j * t j := by
      rw [tsum_eq_sum (s := range N) fun j hj => by
        simp only [hg]; split_ifs with h
        · exact absurd (Finset.mem_range.2 h) hj
        · exact mul_zero _]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hg]; split_ifs with h
      · rfl
      · exact absurd (Finset.mem_range.1 hj) h
    have hYt : ∑ j ∈ range N, s ^ j * t j ≠ ∞ := ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.mul_ne_top (ENNReal.pow_ne_top hst) (htt j)
    have htail : ∀ n, c * ∑' i, g (i + n + 1) ≤
        e (n + 1) + ∑ k ∈ range (n + 1), w k * g (n - k) := by
      intro n
      by_cases hn : n < N
      · have hgk : ∀ k ∈ range (n + 1), w k * g (n - k) = w k * t (n - k) := fun k _ => by
          simp only [hg]; split_ifs with h
          · rfl
          · exact absurd (lt_of_le_of_lt (Nat.sub_le n k) hn) h
        rw [Finset.sum_congr rfl hgk]
        calc c * ∑' i, g (i + n + 1) ≤ c * ∑' i, t (i + n + 1) :=
              mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => hgt _)
          _ ≤ _ := atom_tail_le hα ha hπ hinv hf hπf n
      · have h0 : ∀ i, g (i + n + 1) = 0 := fun i => by
          simp only [hg]; split_ifs with h
          · exact absurd h (by omega)
          · rfl
        simp only [h0, tsum_zero, mul_zero]
        exact bot_le
    have hmain : c * ∑' j, s ^ j * g j ≤
        c * ∑' j, t j + (s - 1) * R + c / 2 * ∑' j, s ^ j * g j := by
      calc c * ∑' j, s ^ j * g j
          = c * ∑' j, g j + (s - 1) * ∑' n, s ^ n * (c * ∑' i, g (i + n + 1)) := by
            rw [tsum_pow_mul_eq_add hs1.le g, mul_add]
            congr 1
            simp_rw [mul_left_comm (s ^ _) c, ENNReal.tsum_mul_left]
            ring
        _ ≤ c * ∑' j, t j + (s - 1) * ∑' n, s ^ n *
            (e (n + 1) + ∑ k ∈ range (n + 1), w k * g (n - k)) :=
            add_le_add (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hgt))
              (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl (htail n)))
        _ = c * ∑' j, t j + (s - 1) * (∑' n, s ^ n * e (n + 1) +
            (∑' k, s ^ k * w k) * ∑' j, s ^ j * g j) := by
            congr 2
            rw [← tsum_sum_range_mul, ← ENNReal.tsum_add]
            refine tsum_congr fun n => ?_
            rw [mul_add, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
            calc s ^ n * (w k * g (n - k)) = s ^ (k + (n - k)) * (w k * g (n - k)) := by
                  rw [Nat.add_sub_cancel' hkn]
              _ = _ := by rw [pow_add]; ring
        _ ≤ c * ∑' j, t j + (s - 1) * R + c / 2 * ∑' j, s ^ j * g j := by
            rw [mul_add, ← mul_assoc, ← add_assoc]
            refine add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hE)) (mul_le_mul' ?_ le_rfl)
            exact (mul_le_mul' hs1ε hD).trans hεR
    rw [hYg] at hmain
    have hfin : c / 2 * ∑ j ∈ range N, s ^ j * t j ≠ ∞ := ENNReal.mul_ne_top hc2t hYt
    have h2 : c / 2 * ∑ j ∈ range N, s ^ j * t j + c / 2 * ∑ j ∈ range N, s ^ j * t j ≤
        c * ∑' j, t j + (s - 1) * R + c / 2 * ∑ j ∈ range N, s ^ j * t j := by
      rw [← add_mul, ENNReal.add_halves]; exact hmain
    have h3 := (ENNReal.add_le_add_iff_right hfin).1 h2
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc2) (Or.inl hc2t), mul_comm]
    exact h3
  have hK : (c * ∑' j, t j + (s - 1) * R) / (c / 2) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hct hU,
      ENNReal.mul_ne_top (ENNReal.sub_ne_top hst) hR⟩) hc2
  have hsum : ∑' j, s ^ j * t j ≠ ∞ := by
    rw [ENNReal.tsum_eq_iSup_nat]
    exact ne_top_of_le_ne_top hK (iSup_le hY)
  have hUa : geomTaboo P α s f a ≠ ∞ := by
    rw [← tsum_pow_lintegral_tabooKernel P hα.1 s hf a]
    simp_rw [pow_succ', mul_assoc]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hst hsum
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs1).ne'
  have habs := isAbsorbing_geomTaboo_finite hα ha hs0 hst hf hUa
  exact ⟨s, hs1, hst, hUa, proposition_4_2_3_i h.2.1.2.1 ((measurableSet_singleton ∞).compl.preimage
    (measurable_geomTaboo P hα.1 s hf)) ⟨a, hUa⟩ habs, habs⟩

/-- **Theorem 15.4.2**, the regularity conclusion (MT p. 386): under `theorem_15_4_2_atom`, if `f`
is bounded on the atom then `α` is `f`-Kendall and the chain is `f`-geometrically regular on a full
absorbing set. -/
theorem theorem_15_4_2_atom_regular {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {π : Measure X}
    [IsProbabilityMeasure π] (hinv : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ y, f y ∂π ≠ ∞) {r : ℝ≥0∞} (hr : 1 < r)
    (hR : ∑' n, r ^ n * fNorm f ((P ^ n : Kernel X X) a) π ≠ ∞) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hfB : ∀ x ∈ α, f x ≤ B) :
    ∃ s : ℝ≥0∞, IsFKendall P f α s ∧ ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧
      IsAbsorbing P S ∧ IsFGeomRegularOn P f S := by
  obtain ⟨s, hs1, hst, hUa, -, -⟩ := theorem_15_4_2_atom h ha hinv hf hf1 hπf hr hR
  have hK : IsFKendall P f α s := ⟨h.1.1, hs1, hst, B + geomTaboo P α s f a,
    ENNReal.add_ne_top.2 ⟨hB, hUa⟩, fun x hx => (geomSum_le_add_geomTaboo P α s hf x).trans
      (add_le_add (hfB x hx) (le_of_eq (h.1.geomTaboo_const s hf hx ha)))⟩
  obtain ⟨S, hSm, hSf, hSa, -, hS⟩ :=
    proposition_15_3_2 h.2.1 hf hf1 (h.1.isPetite ⟨a, ha⟩) ⟨a, ha⟩ hK
  exact ⟨s, hK, S, hSm, hSf, hSa, hS⟩

/-- **The counterexample to (15.44) as printed** (MT p. 386). For the flip chain on `Bool`, the
atom `{true}`, `f = 1` and `n = 1`: `P¹(true, f) − π(f) = 0`, while the printed right-hand side
`(u(0) − π(α)) t_f(1) + π(α) Σ_{j > 1} t_f(j)` is at least `1/2`. -/
theorem eq_15_44_counterexample :
    haveI := isMarkovKernel_flipKernel
    ((flipKernel ^ 1 : Kernel Bool Bool) true univ).toReal - (flipPi univ).toReal <
      (((flipKernel ^ 0 : Kernel Bool Bool) true {true}).toReal - (flipPi {true}).toReal) *
        (tabooKernel flipKernel (measurableSet_singleton true) 0 true univ).toReal +
      (flipPi {true}).toReal *
        (∑' i, tabooKernel flipKernel (measurableSet_singleton true) (i + 1) true univ).toReal := by
  have := isMarkovKernel_flipKernel
  have := isProbabilityMeasure_flipPi
  have h1 : ((flipKernel ^ 1 : Kernel Bool Bool) true univ) = 1 := by
    have := isMarkovKernel_pow flipKernel 1; exact measure_univ
  have h0 : ((flipKernel ^ 0 : Kernel Bool Bool) true {true}) = 1 := by
    rw [pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton true)]
  have ht0 : tabooKernel flipKernel (measurableSet_singleton true) 0 true univ = 1 := by
    rw [tabooKernel_zero]; exact measure_univ
  have hπ : (flipPi {true}).toReal = 2⁻¹ := by
    rw [flipPi, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem
      (mem_singleton true), Measure.dirac_apply' _ (measurableSet_singleton true),
      indicator_of_notMem (show false ∉ ({true} : Set Bool) by simp), add_zero, smul_eq_mul,
      mul_one, ENNReal.toReal_inv]
    norm_num
  rw [h1, h0, ht0, hπ, measure_univ, ENNReal.toReal_one, sub_self]
  have hX := ENNReal.toReal_nonneg (a := ∑' i, tabooKernel flipKernel
    (measurableSet_singleton true) (i + 1) true univ)
  nlinarith

end MeynTweedie.GeometricErgodicity
