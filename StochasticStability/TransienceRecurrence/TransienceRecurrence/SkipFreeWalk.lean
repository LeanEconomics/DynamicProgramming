/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransienceRecurrence.RandomWalkIntegers
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Transience of the skip-free random walk on `ℤ₊` (MT §8.5.3)

Meyn and Tweedie, Proposition 8.5.5, pp. 195–197. The walk is `matKernel (rwhlMatrix Γ)` on `ℤ₊`
with increments skip-free to the right, `Γ(w) = 0` for `w > 1` (the GI/M/1 queue), but with no
bound on the downward jumps. Write `aⱼ = Γ(1 − j)`, `j ≥ 0`.

The book's construction: a bounded non-constant solution of `PV = V` off `{0}` (8.62) is
`V(x) ∝ Σ_{m<x} bₘ`, where `Σ bₘ zᵐ = B(z)⁻¹`, `B(z) = 1 − Σⱼ zʲ Σ_{n>j} aₙ` (8.69). Here `b` is
the renewal sequence (`renewalSeq`) of the defective sequence `cⱼ = Σ_{n>j} aₙ`, whose total mass is
`Σ n aₙ = 1 − β < 1`; the equation (8.63) is proved by comparing power series coefficients
(Mathlib's `PowerSeries`) instead of by Abel's theorem.

* `skipFree_tsum_a`: `Σⱼ aⱼ = 1`; `skipFreeTail`, `skipFreeTail_add`: `cⱼ + Σ_{l ≤ j} aₗ = 1`;
  `tsum_skipFreeTail`: `Σⱼ cⱼ = Σₙ n aₙ`.
* `tsum_renewalSeq_skipFree` (8.68): `Σₘ bₘ = (1 − Σₙ n aₙ)⁻¹ < ∞`.
* `skipFree_harmonic` (8.63): `V(x) = Σ_{m<x} bₘ` has `Σⱼ aⱼ V((x + 1 − j)⁺) = V(x)` for `x ≥ 1`,
  that is `PV(x) = V(x)` (`lintegral_skipFreeV`).
* **Proposition 8.5.5** (`proposition_8_5_5`): if `Σₙ n aₙ < 1` (equivalently `β > 0`,
  `skipFree_mean_lt_one`) and `Γ(−∞, 0) > 0`, the walk is transient; `proposition_8_5_5_mean`
  is the statement with `β = Σ_w w Γ(w) > 0`.

**Corrections.** The book assumes "without loss of generality" `Γ(−∞, 0) > 0`; without it the
walk is irreducible for no nonzero measure (`rwhl_not_irreducible_of_nonneg`), so it is neither
transient nor recurrent in the sense of §8.2.3 (`rwhl_not_transient_of_nonneg`), and the
hypothesis is kept.
-/

namespace MeynTweedie.TransienceRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {Γ : ℤ → ℝ≥0∞}

/-- `Σⱼ Γ(1 − j) f(j) = Σ_w Γ(w) f(1 − w)` for a law skip-free to the right. -/
theorem skipFree_tsum_reindex (hskip : ∀ w : ℤ, 1 < w → Γ w = 0) (F : ℤ → ℝ≥0∞) :
    ∑' j : ℕ, Γ (1 - j) * F (1 - j) = ∑' w, Γ w * F w := by
  refine (Function.Injective.tsum_eq (g := fun j : ℕ => 1 - (j : ℤ)) (f := fun w => Γ w * F w)
    (fun i j h => by
      have h' : (1 : ℤ) - i = 1 - j := h
      exact_mod_cast (show (i : ℤ) = j by omega)) fun w hw => ?_)
  have : w ≤ 1 := by
    by_contra h
    push Not at h
    exact hw (by simp only; rw [hskip w h, zero_mul])
  exact ⟨(1 - w).toNat, by simp only; omega⟩

/-- `Σⱼ aⱼ = 1`. -/
theorem skipFree_tsum_a (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0) :
    ∑' j : ℕ, Γ (1 - j) = 1 := by
  have := skipFree_tsum_reindex hskip (fun _ => 1)
  simp only [mul_one] at this
  rw [this, hΓ]

/-- The tails `cⱼ = Σ_{n > j} aₙ`. -/
noncomputable def skipFreeTail (Γ : ℤ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ∑' i : ℕ, Γ (1 - ((i + j + 1 : ℕ) : ℤ))

/-- `cⱼ + Σ_{l ≤ j} aₗ = 1`. -/
theorem skipFreeTail_add (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0) (j : ℕ) :
    skipFreeTail Γ j + ∑ l ∈ Finset.range (j + 1), Γ (1 - l) = 1 := by
  rw [add_comm, skipFreeTail, ← skipFree_tsum_a hΓ hskip]
  have := (ENNReal.summable (f := fun i : ℕ => Γ (1 - ((i + (j + 1) : ℕ) : ℤ)))
    ).sum_add_tsum_nat_add' (f := fun n : ℕ => Γ (1 - (n : ℤ))) (k := j + 1)
  rw [← this]
  congr 1

/-- `Σⱼ cⱼ = Σₙ n aₙ`. -/
theorem tsum_skipFreeTail (Γ : ℤ → ℝ≥0∞) :
    ∑' j, skipFreeTail Γ j = ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) := by
  unfold skipFreeTail
  rw [ENNReal.tsum_comm, ← tsum_sum_antidiagonal (fun p => Γ (1 - ((p.1 + p.2 + 1 : ℕ) : ℤ)))]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  refine tsum_congr fun n => ?_
  rw [Finset.sum_congr rfl fun p hp => by rw [Finset.mem_antidiagonal.1 hp], Finset.sum_const,
    Finset.Nat.card_antidiagonal, nsmul_eq_mul]

/-- (8.68): `Σₘ bₘ = (1 − Σₙ n aₙ)⁻¹` for the renewal sequence `b` of `c`. -/
theorem tsum_renewalSeq_skipFree (Γ : ℤ → ℝ≥0∞) :
    ∑' m, renewalSeq (skipFreeTail Γ) m = (1 - ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n))⁻¹ := by
  have := genFun_renewalSeq (skipFreeTail Γ) 1
  simp only [genFun, one_pow, mul_one] at this
  rw [this, tsum_skipFreeTail]

/-- The bounded harmonic function `V(x) = Σ_{m<x} bₘ` of Proposition 8.5.5. -/
noncomputable def skipFreeV (Γ : ℤ → ℝ≥0∞) (x : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.range x, renewalSeq (skipFreeTail Γ) m

/-- **(8.63)**, the harmonic equation (MT p. 196): if `Σₙ n aₙ < 1`, then for `x ≥ 1`,
`Σ_{j ≤ x} aⱼ V(x + 1 − j) = V(x)`, where `V(x) = Σ_{m<x} bₘ`. -/
theorem skipFree_harmonic (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0)
    (hmean : ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) < 1) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2), Γ (1 - j) * skipFreeV Γ (n + 2 - j) = skipFreeV Γ (n + 1) := by
  set a : ℕ → ℝ≥0∞ := fun j => Γ (1 - j) with ha
  set c := skipFreeTail Γ
  set b := renewalSeq c
  have hbfin : ∀ m, b m ≠ ∞ := fun m => ne_top_of_le_ne_top (by
    rw [tsum_renewalSeq_skipFree]; exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hmean).ne')
    (ENNReal.le_tsum (f := b) m)
  -- the power series identity
  set O : PowerSeries ℝ≥0∞ := PowerSeries.mk fun _ => 1 with hOdef
  have hO : ∀ k, PowerSeries.coeff k O = 1 := fun k => by rw [hOdef, PowerSeries.coeff_mk]
  have hren : PowerSeries.mk b = 1 + PowerSeries.mk b * PowerSeries.mk c := by
    ext m
    rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, PowerSeries.coeff_mul]
    simp_rw [PowerSeries.coeff_mk]
    exact renewal_equation c m
  have hcA : PowerSeries.mk c + PowerSeries.mk a * O = O := by
    ext m
    rw [map_add, PowerSeries.coeff_mul]
    simp_rw [hO, PowerSeries.coeff_mk, mul_one]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact skipFreeTail_add hΓ hskip m
  have key : PowerSeries.mk b * O + 1 =
      PowerSeries.mk b + PowerSeries.mk a * (PowerSeries.mk b * O) :=
    calc PowerSeries.mk b * O + 1 =
          PowerSeries.mk b * (PowerSeries.mk c + PowerSeries.mk a * O) + 1 := by rw [hcA]
      _ = (1 + PowerSeries.mk b * PowerSeries.mk c) +
          PowerSeries.mk a * (PowerSeries.mk b * O) := by ring
      _ = _ := by rw [← hren]
  have hB : ∀ m, PowerSeries.coeff m (PowerSeries.mk b * O) = skipFreeV Γ (m + 1) := fun m => by
    rw [PowerSeries.coeff_mul]
    simp_rw [hO, PowerSeries.coeff_mk, mul_one]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rfl
  have hk := congrArg (PowerSeries.coeff (n + 1)) key
  have hone : PowerSeries.coeff (n + 1) (1 : PowerSeries ℝ≥0∞) = 0 := by
    rw [PowerSeries.coeff_one]; simp
  rw [map_add, map_add, hone, add_zero, hB, PowerSeries.coeff_mk, PowerSeries.coeff_mul] at hk
  simp_rw [hB, PowerSeries.coeff_mk] at hk
  -- `V(n + 2) = V(n + 1) + b(n + 1)`
  have hsplit : skipFreeV Γ (n + 1 + 1) = skipFreeV Γ (n + 1) + b (n + 1) := by
    unfold skipFreeV; rw [Finset.sum_range_succ]
  rw [hsplit, add_comm] at hk
  have hcancel := (ENNReal.add_right_inj (hbfin (n + 1))).1 hk
  rw [hcancel, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  congr 2
  omega

/-- `V` is bounded by `(1 − Σ n aₙ)⁻¹`. -/
theorem skipFreeV_le (Γ : ℤ → ℝ≥0∞) (x : ℕ) :
    skipFreeV Γ x ≤ (1 - ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n))⁻¹ := by
  rw [← tsum_renewalSeq_skipFree]
  exact ENNReal.sum_le_tsum _

/-- `V(0) = 0` and `V(x) ≥ b₀ ≥ 1` for `x ≥ 1`. -/
theorem one_le_skipFreeV (Γ : ℤ → ℝ≥0∞) {x : ℕ} (hx : 1 ≤ x) : 1 ≤ skipFreeV Γ x := by
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 1 := ⟨x - 1, by omega⟩
  unfold skipFreeV
  rw [Finset.sum_range_succ']
  refine le_add_left ?_
  rw [renewal_equation]
  exact le_add_right (by simp [diracDist])

/-- `PV(x) = V(x)` for `x ≥ 1` (8.62). -/
theorem lintegral_skipFreeV (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0)
    (hmean : ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) < 1) (n : ℕ) :
    ∫⁻ y, skipFreeV Γ y ∂matKernel (rwhlMatrix Γ) (n + 1) = skipFreeV Γ (n + 1) := by
  rw [lintegral_rwhl, ← skipFree_tsum_reindex hskip
    (fun w => skipFreeV Γ (((n + 1 : ℕ) : ℤ) + w).toNat)]
  rw [tsum_eq_sum (s := Finset.range (n + 2)) fun j hj => by
    have : ((((n + 1 : ℕ) : ℤ) + (1 - (j : ℤ))).toNat) = 0 := by
      simp only [Finset.mem_range, not_lt] at hj; omega
    rw [this]; simp [skipFreeV]]
  rw [← skipFree_harmonic hΓ hskip hmean n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  congr 2
  omega

/-- `Σₙ n aₙ < 1` forces `Γ(1) > 0`. -/
theorem skipFree_one_pos (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0)
    (hmean : ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) < 1) : Γ 1 ≠ 0 := by
  intro h1
  refine absurd hmean (not_lt.2 ?_)
  calc (1 : ℝ≥0∞) = ∑' j : ℕ, Γ (1 - j) := (skipFree_tsum_a hΓ hskip).symm
    _ = ∑' j : ℕ, Γ (1 - ((j + 1 : ℕ) : ℤ)) := by
        rw [tsum_eq_zero_add' ENNReal.summable]; simp [h1]
    _ ≤ ∑' j : ℕ, ((j + 1 : ℕ) : ℝ≥0∞) * Γ (1 - ((j + 1 : ℕ) : ℤ)) :=
        ENNReal.tsum_le_tsum fun j => le_mul_of_one_le_left zero_le (by simp)
    _ = ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) := by
        rw [tsum_eq_zero_add' ENNReal.summable (f := fun n : ℕ => (n : ℝ≥0∞) * Γ (1 - n))]
        simp

/-- **Proposition 8.5.5** (MT p. 195): the random walk on `ℤ₊` skip-free to the right
(`Γ(w) = 0` for `w > 1`), with `Γ(−∞, 0) > 0` and `Σₙ n Γ(1 − n) < 1` (that is, `β > 0`), is
transient: `V(x) = Σ_{m<x} bₘ` is bounded, non-constant and harmonic off `{0}`, and Theorem 8.4.2
applies. -/
theorem proposition_8_5_5 (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0)
    (hmean : ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) < 1) {wn : ℤ} (hwn : wn < 0) (hΓn : Γ wn ≠ 0)
    {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
      IsMaximalIrreducibility (matKernel (rwhlMatrix Γ)) ψ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
    IsTransientChain (matKernel (rwhlMatrix Γ)) ψ := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  set P := matKernel (rwhlMatrix Γ)
  set K := (1 - ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n))⁻¹ with hK
  have hKfin : K ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hmean).ne'
  have hVfin : ∀ x, skipFreeV Γ x ≠ ∞ := fun x => ne_top_of_le_ne_top hKfin (skipFreeV_le Γ x)
  set V : ℕ → ℝ := fun x => (skipFreeV Γ x).toReal with hV
  have h1 := skipFree_one_pos hΓ hskip hmean
  -- every state reaches `{x ≥ 1}`
  have hreach : 0 < ψ {x | 0 < V x} := by
    rw [hψ.pos_iff_hitProb_pos (measurableSet_of_countable _)]
    intro y
    have hy0 : 0 < (P ^ y) y {0} :=
      (ENNReal.pow_pos (pos_iff_ne_zero.2 hΓn) _).trans_le (rwhl_pow_zero_ge Γ hwn y y
        (by nlinarith))
    have h01 : 0 < (P ^ 1) 0 {1} := by
      rw [matKernel_pow_one_singleton]
      simp only [rwhlMatrix, one_ne_zero, ite_false, Nat.cast_one, Nat.cast_zero, sub_zero]
      exact pos_iff_ne_zero.2 h1
    refine (hitProb_pos_iff P (measurableSet_of_countable _) y).2 ⟨y, ?_⟩
    refine (ENNReal.mul_pos hy0.ne' h01.ne').trans_le
      ((pow_add_singleton_ge P y 1 y 0 1).trans (measure_mono ?_))
    intro z hz
    rw [mem_singleton_iff.1 hz]
    simp only [mem_ofPred_eq, hV]
    exact ENNReal.toReal_pos (by
      have := one_le_skipFreeV Γ (le_refl 1); exact (zero_lt_one.trans_le this).ne') (hVfin 1)
  refine isTransientChain_of_drift P hψ (C := {0}) (measurableSet_singleton 0)
    (rwhl_pos_zero hΓ hwn hΓn hψ) (V := V) (measurable_of_countable _)
    (fun x => ENNReal.toReal_nonneg) (M := K.toReal)
    (fun x => ENNReal.toReal_mono hKfin (skipFreeV_le Γ x)) (r := 0)
    (fun y hy => by rw [mem_singleton_iff.1 hy]; simp [hV, skipFreeV]) (fun x hx => ?_) hreach
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by have : x ≠ 0 := hx; omega⟩
  rw [driftR, hV, integral_toReal (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun y => (hVfin y).lt_top), lintegral_skipFreeV hΓ hskip hmean n,
    sub_self]

/-- `β > 0` gives `Σₙ n Γ(1 − n) < 1` for a law skip-free to the right with finite mean:
`β = Σ_w w Γ(w) = 1 − Σₙ n Γ(1 − n)`. -/
theorem skipFree_mean_lt_one (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0)
    (hsum : Summable fun w : ℤ => (Γ w).toReal * w) (hβ : 0 < ∑' w : ℤ, (Γ w).toReal * w) :
    ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) < 1 := by
  have hfin : ∀ w, Γ w ≠ ∞ := ne_top_of_tsum_eq_one hΓ
  set a : ℕ → ℝ := fun n => (Γ (1 - n)).toReal with ha
  -- reindex the mean over `ℕ`
  have hreal : ∑' n : ℕ, (Γ (1 - (n : ℤ))).toReal * ((1 - (n : ℤ) : ℤ) : ℝ) =
      ∑' w : ℤ, (Γ w).toReal * w := by
    refine Function.Injective.tsum_eq (g := fun j : ℕ => 1 - (j : ℤ))
      (f := fun w : ℤ => (Γ w).toReal * w) (fun i j h => by
        have h' : (1 : ℤ) - i = 1 - j := h
        exact_mod_cast (show (i : ℤ) = j by omega)) fun w hw => ?_
    have : w ≤ 1 := by
      by_contra h
      push Not at h
      exact hw (by simp [hskip w h])
    exact ⟨(1 - w).toNat, by simp only; omega⟩
  have hsumN : Summable fun n : ℕ => (Γ (1 - (n : ℤ))).toReal * ((1 - (n : ℤ) : ℤ) : ℝ) :=
    hsum.comp_injective (fun i j h => by
      have h' : (1 : ℤ) - i = 1 - j := h
      exact_mod_cast (show (i : ℤ) = j by omega))
  have hsuma : Summable a := ENNReal.summable_toReal (by
    rw [skipFree_tsum_a hΓ hskip]; exact ENNReal.one_ne_top)
  have hsa : ∑' n, a n = 1 := by
    rw [ha, ← ENNReal.tsum_toReal_eq (fun n => hfin _), skipFree_tsum_a hΓ hskip,
      ENNReal.toReal_one]
  have hsumna : Summable fun n : ℕ => (n : ℝ) * a n := by
    have : (fun n : ℕ => (n : ℝ) * a n) = fun n => a n - a n * ((1 - (n : ℤ) : ℤ) : ℝ) := by
      ext n; push_cast; ring
    rw [this]
    exact hsuma.sub hsumN
  have hkey : ∑' n : ℕ, (n : ℝ) * a n = 1 - ∑' w : ℤ, (Γ w).toReal * w := by
    rw [← hreal, ← hsa, ← hsuma.tsum_sub hsumN]
    exact tsum_congr fun n => by push_cast; ring
  have hlt : ∑' n : ℕ, (n : ℝ) * a n < 1 := by rw [hkey]; linarith
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * a n := fun n => mul_nonneg (Nat.cast_nonneg n)
    ENNReal.toReal_nonneg
  have hE : ∑' n : ℕ, (n : ℝ≥0∞) * Γ (1 - n) = ENNReal.ofReal (∑' n : ℕ, (n : ℝ) * a n) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsumna]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, ha,
      ENNReal.ofReal_toReal (hfin _)]
  rw [hE, ENNReal.ofReal_lt_one]
  exact hlt

/-- **Proposition 8.5.5** (MT p. 195), with the mean: a random walk on `ℤ₊` skip-free to the
right with `Γ(−∞, 0) > 0` and positive mean `β = Σ_w w Γ(w) > 0` is transient. -/
theorem proposition_8_5_5_mean (hΓ : ∑' w, Γ w = 1) (hskip : ∀ w : ℤ, 1 < w → Γ w = 0)
    (hsum : Summable fun w : ℤ => (Γ w).toReal * w) (hβ : 0 < ∑' w : ℤ, (Γ w).toReal * w)
    {wn : ℤ} (hwn : wn < 0) (hΓn : Γ wn ≠ 0) {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
      IsMaximalIrreducibility (matKernel (rwhlMatrix Γ)) ψ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
    IsTransientChain (matKernel (rwhlMatrix Γ)) ψ :=
  proposition_8_5_5 hΓ hskip (skipFree_mean_lt_one hΓ hskip hsum hβ) hwn hΓn hψ

/-- MT p. 196: if `Γ[0, ∞) = 1` the walk on `ℤ₊` only moves up, so it is irreducible for no
nonzero measure: each `{n}` is unreachable from `n + 1`. Hence the hypothesis `Γ(−∞, 0) > 0` in
Proposition 8.5.5 cannot be dropped: such a walk is not transient in the sense of §8.2.3. -/
theorem rwhl_not_irreducible_of_nonneg (hΓ : ∑' w, Γ w = 1) (hnn : ∀ w : ℤ, w < 0 → Γ w = 0)
    {φ : Measure ℕ}
    (hφ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
      IsPhiIrreducible (matKernel (rwhlMatrix Γ)) φ) : φ = 0 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  have hpt : ∀ n : ℕ, φ {n} = 0 := fun n => by
    by_contra h0
    have habs : IsAbsorbing (matKernel (rwhlMatrix Γ)) {y : ℕ | n + 1 ≤ y} :=
      (isAbsorbing_matKernel_iff _).2 fun y hy w hw => by
        simp only [mem_ofPred_eq, not_le] at hy hw
        unfold rwhlMatrix
        split_ifs with hw0
        · refine ENNReal.tsum_eq_zero.2 fun k => ?_
          split_ifs with hk
          · exact hnn k (by omega)
          · rfl
        · exact hnn _ (by omega)
    have h1 := habs.hitProb_compl (measurableSet_of_countable _)
      (show n + 1 ∈ {y : ℕ | n + 1 ≤ y} from Nat.le_refl (n + 1))
    have h2 := hφ {n} (measurableSet_singleton n) (pos_iff_ne_zero.2 h0) (n + 1)
    exact absurd h1 ((h2.trans_le (hitProb_mono _ (by simp) _)).ne')
  rw [← Measure.measure_univ_eq_zero, show (univ : Set ℕ) = ⋃ n : ℕ, {n} by ext; simp]
  exact measure_iUnion_null fun n => hpt n

/-- With `Γ[0, ∞) = 1` the walk on `ℤ₊` is neither transient nor recurrent in the sense of
§8.2.3, for every measure `ψ`. -/
theorem rwhl_not_transient_of_nonneg (hΓ : ∑' w, Γ w = 1) (hnn : ∀ w : ℤ, w < 0 → Γ w = 0)
    (ψ : Measure ℕ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
    ¬ IsTransientChain (matKernel (rwhlMatrix Γ)) ψ ∧
      ¬ IsRecurrentChain (matKernel (rwhlMatrix Γ)) ψ := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  exact ⟨fun h => h.1.1 (rwhl_not_irreducible_of_nonneg hΓ hnn h.1.2.1),
    fun h => h.1.1 (rwhl_not_irreducible_of_nonneg hΓ hnn h.1.2.1)⟩

end MeynTweedie.TransienceRecurrence
