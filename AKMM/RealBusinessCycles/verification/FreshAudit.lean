import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import AKMMUncertainty.LinearSDE
import Mathlib.LinearAlgebra.Matrix.Block
import AKMMLaborSupply.Dynamic
import NeoclassicalGrowth.RBModel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import NeoclassicalGrowth.RXCopied
import NeoclassicalGrowth.RBEquilibrium
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import AKMMLaborSupply.BalancedGrowth
import NeoclassicalGrowth.RXHayashi
import NeoclassicalGrowth.RXTrend
import NeoclassicalGrowth.RXCapacity
import NeoclassicalGrowth.RBUtility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ContinuousMapDense
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Hodrick–Prescott filter

AKMM, §14.3.1, (14.1), pp. 410–412.

Observations are indexed `0, …, T − 1` (the book's `t = 1, …, T`). The second-difference matrix
`D` (`hpD`) has row `k` equal to `τ_{k−1} − 2τ_k + τ_{k+1}` for the interior rows
`1 ≤ k ≤ T − 2` and zero otherwise, so `‖Dτ‖²` is the book's
`Σ_{t=2}^{T−1}[(τ_{t+1} − τ_t) − (τ_t − τ_{t−1})]²` (`hp_D_apply`). Let `A = DᵀD` (`hpA`).

* `I + λA` is positive definite for `λ ≥ 0` (`hp_posDef`), hence invertible.
* **(14.1), Lagrangian form**: `τ` minimises `Σ(Y_t − τ_t)² + λ‖Dτ‖²` iff `(I + λA)τ = Y`
  (`eq_14_1`); the minimiser is unique (`hp_unique`) and equals `(I + λA)⁻¹Y` (`hp_trend_eq`,
  `hp_trend_exists`).
* The rows of `A` are the printed pentadiagonal matrix: interior rows
  `(1, −4, 6, −4, 1)` (`hp_A_interior`), first rows `(1, −2, 1)` and `(−2, 5, −4, 1)`
  (`hp_A_row0`, `hp_A_row1`), last rows symmetrically (`hp_A_rowLast`, `hp_A_rowLast1`).
* The printed first-order condition `τ_t − λ(…) = Y_t` has the wrong sign: the bracket is
  `τ_{t−2} − 4τ_{t−1} + 6τ_t − 4τ_{t+1} + τ_{t+2}` (`hp_bracket_eq`), the correct condition is
  `τ_t + λ(…) = Y_t` (`hp_foc_interior`), and the printed one fails (`hp_foc_printed_false`).
  The interior rows are `3 ≤ t ≤ T − 2` in the book's indexing, not `2 ≤ t ≤ T − 2`.
* **Constrained and Lagrangian forms** (p. 411): the Lagrangian trend `τ_λ` (`λ > 0`) is the
  unique solution of the constrained problem with `µ = ‖Dτ_λ‖²` (`hp_constrained_of_lagrangian`,
  `hp_constrained_unique`).
* `µ = 0` imposes a linear trend: `‖Dτ‖² ≤ 0` iff `τ_t = τ₀ + t(τ₁ − τ₀)` (`hp_pen_zero_iff`).
* Ravn–Uhlig: `1600·(1/4)⁴ = 6.25` (`hp_ravn_uhlig`).

The limit `λ → ∞` (the OLS linear trend) is in `HPLimit`.
-/

namespace AKMM.RealBusinessCycles

open Matrix

/-- The second-difference matrix of the HP filter: row `k` is `τ_{k−1} − 2τ_k + τ_{k+1}` for
`1 ≤ k` and `k + 1 < T`, and zero otherwise. -/
def hpD (T : ℕ) : Matrix (Fin T) (Fin T) ℝ := fun k j =>
  if 1 ≤ k.val ∧ k.val + 1 < T then
    (if j.val + 1 = k.val then 1 else 0) + (if j.val = k.val then -2 else 0) +
      (if j.val = k.val + 1 then 1 else 0)
  else 0

/-- AKMM, p. 412: the matrix `A = DᵀD` of the first-order system `(I + λA)τ = Y`. -/
def hpA (T : ℕ) : Matrix (Fin T) (Fin T) ℝ := (hpD T)ᵀ * hpD T

/-- The fit `Σ_t (Y_t − τ_t)²`. -/
def hpFit {T : ℕ} (Y τ : Fin T → ℝ) : ℝ := ∑ t, (Y t - τ t) ^ 2

/-- The smoothness penalty `Σ_k ((Dτ)_k)²`. -/
def hpPen (T : ℕ) (τ : Fin T → ℝ) : ℝ := ∑ k, (hpD T *ᵥ τ) k ^ 2

/-- AKMM, (14.1), Lagrangian form: `Σ(Y_t − τ_t)² + λΣ[(τ_{t+1} − τ_t) − (τ_t − τ_{t−1})]²`. -/
def hpObj (T : ℕ) (lam : ℝ) (Y τ : Fin T → ℝ) : ℝ := hpFit Y τ + lam * hpPen T τ

/-- The padding of a vector by zero outside `0, …, T − 1`. -/
noncomputable def hpExt {T : ℕ} (τ : Fin T → ℝ) (m : ℕ) : ℝ :=
  if h : m < T then τ ⟨m, h⟩ else 0

theorem hp_sum_ite_val {T : ℕ} (f : Fin T → ℝ) (m : ℕ) :
    ∑ j : Fin T, (if j.val = m then f j else 0) = if h : m < T then f ⟨m, h⟩ else 0 := by
  by_cases h : m < T
  · simp only [h, ↓reduceDIte]
    rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro j _ hj
      have : j.val ≠ m := fun e => hj (Fin.ext e)
      simp [this]
    · simp
  · simp only [h, ↓reduceDIte]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : j.val ≠ m := fun e => h (e ▸ j.isLt)
    simp [this]

theorem hp_pen_nonneg (T : ℕ) (τ : Fin T → ℝ) : 0 ≤ hpPen T τ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem hp_fit_nonneg {T : ℕ} (Y τ : Fin T → ℝ) : 0 ≤ hpFit Y τ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- AKMM, p. 411: the rows of `Dτ` are the second differences of the constraint
(`τ_{k+1} − 2τ_k + τ_{k−1}` for `1 ≤ k ≤ T − 2`, in the padded notation) and vanish otherwise. -/
theorem hp_D_apply {T : ℕ} (τ : Fin T → ℝ) (k : Fin T) :
    (hpD T *ᵥ τ) k = if 1 ≤ k.val ∧ k.val + 1 < T then
      hpExt τ (k.val - 1) - 2 * hpExt τ k.val + hpExt τ (k.val + 1) else 0 := by
  unfold hpD
  simp only [mulVec, dotProduct]
  split_ifs with hk
  · have e : ∀ j : Fin T, ((if j.val + 1 = k.val then (1 : ℝ) else 0) +
        (if j.val = k.val then -2 else 0) + (if j.val = k.val + 1 then 1 else 0)) * τ j =
        (if j.val = k.val - 1 then τ j else 0) + (-2) * (if j.val = k.val then τ j else 0) +
          (if j.val = k.val + 1 then τ j else 0) := fun j => by
      split_ifs <;> first | (exfalso; omega) | ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hp_sum_ite_val, hpExt]
    ring
  · simp

/-- The padded second difference `τ_{m−1} − 2τ_m + τ_{m+1}`. -/
noncomputable def hpSec {T : ℕ} (τ : Fin T → ℝ) (m : ℕ) : ℝ :=
  hpExt τ (m - 1) - 2 * hpExt τ m + hpExt τ (m + 1)

theorem hp_ext_fin {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) : hpExt τ t.val = τ t := by
  simp [hpExt, t.isLt]

/-- The rows of `A = DᵀD`: `(Aτ)_t = [t+1 interior](Dτ)_{t+1} − 2[t interior](Dτ)_t +
[t−1 interior](Dτ)_{t−1}`. -/
theorem hp_A_apply {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) :
    (hpA T *ᵥ τ) t = (if t.val + 2 < T then hpSec τ (t.val + 1) else 0) -
      2 * (if 1 ≤ t.val ∧ t.val + 1 < T then hpSec τ t.val else 0) +
      (if 2 ≤ t.val then hpSec τ (t.val - 1) else 0) := by
  unfold hpA
  rw [← mulVec_mulVec]
  set w := hpD T *ᵥ τ with hw
  have hwk : ∀ k : Fin T, w k = if 1 ≤ k.val ∧ k.val + 1 < T then hpSec τ k.val else 0 :=
    fun k => by rw [hw, hp_D_apply]; rfl
  simp only [mulVec, dotProduct, transpose_apply]
  have e : ∀ k : Fin T, hpD T k t * w k =
      (if k.val = t.val + 1 then (if 1 ≤ k.val ∧ k.val + 1 < T then w k else 0) else 0) +
      (-2) * (if k.val = t.val then (if 1 ≤ k.val ∧ k.val + 1 < T then w k else 0) else 0) +
      (if k.val = t.val - 1 then (if 1 ≤ k.val ∧ k.val + 1 < T ∧ 1 ≤ t.val then w k else 0)
        else 0) := fun k => by
    unfold hpD
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hp_sum_ite_val]
  have ht := t.isLt
  congr 1
  · congr 1
    · by_cases h : t.val + 2 < T
      · simp only [show t.val + 1 < T by omega, ↓reduceDIte, h, ↓reduceIte,
          show 1 ≤ t.val + 1 ∧ t.val + 1 + 1 < T from ⟨by omega, by omega⟩, hwk, and_self]
      · simp only [h, ↓reduceIte]
        split_ifs with h1 h2 <;> first | rfl | (exfalso; tauto)
    · simp only [ht, ↓reduceDIte, Fin.eta, hwk]
      split_ifs <;> ring
  · by_cases h : 2 ≤ t.val
    · simp only [show t.val - 1 < T by omega, ↓reduceDIte, h, ↓reduceIte,
        show 1 ≤ t.val - 1 ∧ t.val - 1 + 1 < T ∧ 1 ≤ t.val from ⟨by omega, by omega, by omega⟩,
        hwk, and_self]
    · simp only [h, ↓reduceIte]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

/-- **AKMM, p. 412: the interior rows of `A`** are `(1, −4, 6, −4, 1)`:
`(Aτ)_t = τ_{t−2} − 4τ_{t−1} + 6τ_t − 4τ_{t+1} + τ_{t+2}` for `2 ≤ t ≤ T − 3` (the book's
`3 ≤ t ≤ T − 2`). -/
theorem hp_A_interior {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) (h2 : 2 ≤ t.val)
    (h3 : t.val + 3 ≤ T) :
    (hpA T *ᵥ τ) t = hpExt τ (t.val - 2) - 4 * hpExt τ (t.val - 1) + 6 * τ t -
      4 * hpExt τ (t.val + 1) + hpExt τ (t.val + 2) := by
  rw [hp_A_apply, ite_eq_left (by omega : t.val + 2 < T),
    ite_eq_left (⟨by omega, by omega⟩ : 1 ≤ t.val ∧ t.val + 1 < T),
    ite_eq_left (by omega : 2 ≤ t.val)]
  simp only [hpSec, show t.val + 1 - 1 = t.val by omega, show t.val + 1 + 1 = t.val + 2 by omega,
    show t.val - 1 - 1 = t.val - 2 by omega, show t.val - 1 + 1 = t.val by omega, hp_ext_fin]
  ring

/-- AKMM, p. 412: the first row of `A` is `(1, −2, 1, 0, …)` (`T ≥ 3`). -/
theorem hp_A_row0 {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) (h0 : t.val = 0) (hT : 3 ≤ T) :
    (hpA T *ᵥ τ) t = hpExt τ 0 - 2 * hpExt τ 1 + hpExt τ 2 := by
  rw [hp_A_apply, ite_eq_left (by omega : t.val + 2 < T),
    ite_eq_right (by omega : ¬(1 ≤ t.val ∧ t.val + 1 < T)),
    ite_eq_right (by omega : ¬(2 ≤ t.val))]
  simp only [hpSec, h0]
  ring

/-- AKMM, p. 412: the second row of `A` is `(−2, 5, −4, 1, 0, …)` (`T ≥ 4`). -/
theorem hp_A_row1 {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) (h1 : t.val = 1) (hT : 4 ≤ T) :
    (hpA T *ᵥ τ) t = -2 * hpExt τ 0 + 5 * hpExt τ 1 - 4 * hpExt τ 2 + hpExt τ 3 := by
  rw [hp_A_apply, ite_eq_left (by omega : t.val + 2 < T),
    ite_eq_left (⟨by omega, by omega⟩ : 1 ≤ t.val ∧ t.val + 1 < T),
    ite_eq_right (by omega : ¬(2 ≤ t.val))]
  simp only [hpSec, h1]
  ring

/-- AKMM, p. 412: the last row of `A` is `(…, 0, 1, −2, 1)` (`T ≥ 3`). -/
theorem hp_A_rowLast {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) (h : t.val + 1 = T) (hT : 3 ≤ T) :
    (hpA T *ᵥ τ) t = hpExt τ (T - 3) - 2 * hpExt τ (T - 2) + hpExt τ (T - 1) := by
  rw [hp_A_apply, ite_eq_right (by omega : ¬(t.val + 2 < T)),
    ite_eq_right (by omega : ¬(1 ≤ t.val ∧ t.val + 1 < T)),
    ite_eq_left (by omega : 2 ≤ t.val)]
  simp only [hpSec, show t.val - 1 = T - 2 by omega,
    show T - 2 + 1 = T - 1 by omega, show T - 2 - 1 = T - 3 by omega]
  ring

/-- AKMM, p. 412: the second-to-last row of `A` is `(…, 0, 1, −4, 5, −2)` (`T ≥ 4`). -/
theorem hp_A_rowLast1 {T : ℕ} (τ : Fin T → ℝ) (t : Fin T) (h : t.val + 2 = T) (hT : 4 ≤ T) :
    (hpA T *ᵥ τ) t =
      hpExt τ (T - 4) - 4 * hpExt τ (T - 3) + 5 * hpExt τ (T - 2) - 2 * hpExt τ (T - 1) := by
  rw [hp_A_apply, ite_eq_right (by omega : ¬(t.val + 2 < T)),
    ite_eq_left (⟨by omega, by omega⟩ : 1 ≤ t.val ∧ t.val + 1 < T),
    ite_eq_left (by omega : 2 ≤ t.val)]
  simp only [hpSec,
    show t.val = T - 2 by omega, show T - 3 + 1 = T - 2 by omega, show T - 2 - 1 = T - 3 by omega,
    show T - 2 + 1 = T - 1 by omega, show T - 3 - 1 = T - 4 by omega]
  ring

/-- `‖Dτ‖² = τ·Aτ`. -/
theorem hp_pen_eq {T : ℕ} (τ : Fin T → ℝ) : hpPen T τ = τ ⬝ᵥ (hpA T *ᵥ τ) := by
  unfold hpPen hpA
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp [dotProduct, sq]

/-- The cross term: `(Dh)·(Dτ) = h·Aτ`. -/
theorem hp_cross {T : ℕ} (h τ : Fin T → ℝ) :
    ∑ k, (hpD T *ᵥ h) k * (hpD T *ᵥ τ) k = h ⬝ᵥ (hpA T *ᵥ τ) := by
  unfold hpA
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rfl

/-- `(I + λA)` applied to `τ`. -/
theorem hp_M_apply {T : ℕ} (lam : ℝ) (τ : Fin T → ℝ) (t : Fin T) :
    ((1 + lam • hpA T) *ᵥ τ) t = τ t + lam * (hpA T *ᵥ τ) t := by
  rw [add_mulVec, one_mulVec, smul_mulVec]
  simp

/-- The exact expansion of the objective around `τ`:
`J(τ + h) = J(τ) + 2h·((I + λA)τ − Y) + ‖h‖² + λ‖Dh‖²`. -/
theorem hp_obj_expand {T : ℕ} (lam : ℝ) (Y τ h : Fin T → ℝ) :
    hpObj T lam Y (τ + h) = hpObj T lam Y τ +
      2 * (h ⬝ᵥ ((1 + lam • hpA T) *ᵥ τ - Y)) + (h ⬝ᵥ h + lam * hpPen T h) := by
  have hpen : hpPen T (τ + h) = hpPen T τ + 2 * (h ⬝ᵥ (hpA T *ᵥ τ)) + hpPen T h := by
    rw [← hp_cross]
    unfold hpPen
    rw [mulVec_add]
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hfit : hpFit Y (τ + h) = hpFit Y τ - 2 * (h ⬝ᵥ (Y - τ)) + h ⬝ᵥ h := by
    unfold hpFit
    simp only [dotProduct, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hlin : h ⬝ᵥ ((1 + lam • hpA T) *ᵥ τ - Y) =
      -(h ⬝ᵥ (Y - τ)) + lam * (h ⬝ᵥ (hpA T *ᵥ τ)) := by
    simp only [dotProduct, Pi.sub_apply, hp_M_apply, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  unfold hpObj
  rw [hpen, hfit, hlin]
  ring

/-- `‖h‖² + λ‖Dh‖² > 0` for `h ≠ 0` and `λ ≥ 0`. -/
theorem hp_quad_pos {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) {h : Fin T → ℝ} (hh : h ≠ 0) :
    0 < h ⬝ᵥ h + lam * hpPen T h := by
  have h1 : 0 < h ⬝ᵥ h := by
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hh
    have : 0 < h t * h t := mul_self_pos.2 ht
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun s => h s * h s)
      (fun s _ => mul_self_nonneg (h s)) (Finset.mem_univ t))
  have := mul_nonneg hlam (hp_pen_nonneg T h)
  linarith

/-- AKMM, p. 412: `I + λA` (`A = DᵀD`) is positive definite for `λ ≥ 0`. -/
theorem hp_posDef (T : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) : (1 + lam • hpA T).PosDef := by
  refine PosDef.one.add_posSemidef ?_
  have h := posSemidef_conjTranspose_mul_self (hpD T)
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.smul hlam

/-- **AKMM, (14.1), p. 412: the first-order system.** For `λ ≥ 0`, `τ` minimises the HP
objective `Σ(Y_t − τ_t)² + λ‖Dτ‖²` iff `(I + λA)τ = Y`. -/
theorem eq_14_1 {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y τ : Fin T → ℝ) :
    (∀ τ', hpObj T lam Y τ ≤ hpObj T lam Y τ') ↔ (1 + lam • hpA T) *ᵥ τ = Y := by
  constructor
  · intro hmin
    set r := (1 + lam • hpA T) *ᵥ τ - Y with hr
    by_contra hne
    have hr0 : r ≠ 0 := fun h0 => hne (sub_eq_zero.1 h0)
    set a := r ⬝ᵥ r
    set b := r ⬝ᵥ r + lam * hpPen T r
    have ha : 0 < a := by
      have := hp_quad_pos (le_refl (0 : ℝ)) hr0
      simpa using this
    have hb : 0 < b := hp_quad_pos hlam hr0
    -- perturb by `h = −s r` with `s = a/(b + 1)`
    set s := a / b
    have hs : 0 < s := div_pos ha hb
    have e := hp_obj_expand lam Y τ ((-s) • r)
    have hd : ((-s) • r) ⬝ᵥ r = -s * a := by simp [a, smul_dotProduct]
    have hq : ((-s) • r) ⬝ᵥ ((-s) • r) + lam * hpPen T ((-s) • r) = s ^ 2 * b := by
      have hp : hpPen T ((-s) • r) = s ^ 2 * hpPen T r := by
        unfold hpPen
        rw [mulVec_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by simp; ring
      rw [hp]
      simp only [b, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [hd, hq] at e
    have h2 := hmin (τ + (-s) • r)
    have hsb : s ^ 2 * b = s * a := by
      simp only [s]; field_simp
    nlinarith
  · intro hfoc τ'
    have e := hp_obj_expand lam Y τ (τ' - τ)
    rw [hfoc, sub_self, dotProduct_zero, mul_zero, add_zero, add_sub_cancel] at e
    rw [e]
    have : 0 ≤ (τ' - τ) ⬝ᵥ (τ' - τ) + lam * hpPen T (τ' - τ) := by
      rcases eq_or_ne (τ' - τ) 0 with h0 | h0
      · rw [h0]; simp [hpPen]
      · exact (hp_quad_pos hlam h0).le
    linarith

/-- AKMM, p. 412: the HP trend is unique. -/
theorem hp_unique {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y τ τ' : Fin T → ℝ)
    (h : ∀ σ, hpObj T lam Y τ ≤ hpObj T lam Y σ) (h' : ∀ σ, hpObj T lam Y τ' ≤ hpObj T lam Y σ) :
    τ = τ' := by
  have hf := (eq_14_1 hlam Y τ).1 h
  have hf' := (eq_14_1 hlam Y τ').1 h'
  have hu := (hp_posDef T hlam).isUnit
  rw [← hf'] at hf
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu) hf

/-- AKMM, p. 412: "we can obtain the trend by solving the system `τ = (I + λA)⁻¹Y`". -/
theorem hp_trend_eq {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y τ : Fin T → ℝ)
    (h : ∀ σ, hpObj T lam Y τ ≤ hpObj T lam Y σ) : τ = (1 + lam • hpA T)⁻¹ *ᵥ Y := by
  have hf := (eq_14_1 hlam Y τ).1 h
  have hu := (hp_posDef T hlam).isUnit
  rw [← hf, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hu), one_mulVec]

/-- AKMM, p. 412: `(I + λA)⁻¹Y` is the HP trend (existence). -/
theorem hp_trend_exists {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y : Fin T → ℝ) (σ : Fin T → ℝ) :
    hpObj T lam Y ((1 + lam • hpA T)⁻¹ *ᵥ Y) ≤ hpObj T lam Y σ := by
  have hu := (hp_posDef T hlam).isUnit
  refine (eq_14_1 hlam Y _).2 ?_ σ
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hu), one_mulVec]

/-- AKMM, p. 412: the printed bracket
`Δτ_t − Δτ_{t−1} − 2(Δτ_{t+1} − Δτ_t) + Δτ_{t+2} − Δτ_{t+1}` (with `Δτ_s = τ_s − τ_{s−1}`) equals
`τ_{t−2} − 4τ_{t−1} + 6τ_t − 4τ_{t+1} + τ_{t+2}`, the interior row of `A`. -/
theorem hp_bracket_eq (a b c d e : ℝ) :
    (c - b) - (b - a) - 2 * ((d - c) - (c - b)) + ((e - d) - (d - c)) =
      a - 4 * b + 6 * c - 4 * d + e := by ring

/-- **AKMM, p. 412, the interior first-order condition, corrected.** At the HP trend, for
`2 ≤ t ≤ T − 3` (the book's `3 ≤ t ≤ T − 2`),
`τ_t + λ(τ_{t−2} − 4τ_{t−1} + 6τ_t − 4τ_{t+1} + τ_{t+2}) = Y_t`. -/
theorem hp_foc_interior {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y τ : Fin T → ℝ)
    (h : ∀ σ, hpObj T lam Y τ ≤ hpObj T lam Y σ) (t : Fin T) (h2 : 2 ≤ t.val)
    (h3 : t.val + 3 ≤ T) :
    τ t + lam * (hpExt τ (t.val - 2) - 4 * hpExt τ (t.val - 1) + 6 * τ t -
      4 * hpExt τ (t.val + 1) + hpExt τ (t.val + 2)) = Y t := by
  have hf := congrFun ((eq_14_1 hlam Y τ).1 h) t
  rwa [hp_M_apply, hp_A_interior τ t h2 h3] at hf

/-- At the HP trend with `λ ≠ 0`, the printed condition `τ_t − λ(…) = Y_t` holds only where the
bracket vanishes. -/
theorem hp_foc_printed_iff {T : ℕ} {lam : ℝ} (hlam : 0 < lam) (Y τ : Fin T → ℝ)
    (h : ∀ σ, hpObj T lam Y τ ≤ hpObj T lam Y σ) (t : Fin T) (h2 : 2 ≤ t.val)
    (h3 : t.val + 3 ≤ T) :
    τ t - lam * (hpExt τ (t.val - 2) - 4 * hpExt τ (t.val - 1) + 6 * τ t -
      4 * hpExt τ (t.val + 1) + hpExt τ (t.val + 2)) = Y t ↔
    hpExt τ (t.val - 2) - 4 * hpExt τ (t.val - 1) + 6 * τ t -
      4 * hpExt τ (t.val + 1) + hpExt τ (t.val + 2) = 0 := by
  have e := hp_foc_interior hlam.le Y τ h t h2 h3
  constructor
  · intro h'
    have : lam * (hpExt τ (t.val - 2) - 4 * hpExt τ (t.val - 1) + 6 * τ t -
      4 * hpExt τ (t.val + 1) + hpExt τ (t.val + 2)) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hlam.ne'
  · intro h0
    rw [h0] at e ⊢
    linarith

/-- The unit vector `e₂` in `ℝ⁵`. -/
def hpEx : Fin 5 → ℝ := fun i => if i.val = 2 then 1 else 0

/-- **AKMM, p. 412: the printed first-order condition is false.** With `T = 5`, `λ = 1`,
`Y = (I + A)e₂` the HP trend is `e₂`, and at `t = 2` (the book's `t = 3`)
`τ_t − λ(…) ≠ Y_t`. -/
theorem hp_foc_printed_false :
    (∀ σ, hpObj 5 1 ((1 + (1 : ℝ) • hpA 5) *ᵥ hpEx) hpEx ≤
        hpObj 5 1 ((1 + (1 : ℝ) • hpA 5) *ᵥ hpEx) σ) ∧
      hpEx 2 - 1 * (hpExt hpEx (2 - 2) - 4 * hpExt hpEx (2 - 1) + 6 * hpEx 2 -
        4 * hpExt hpEx (2 + 1) + hpExt hpEx (2 + 2)) ≠ ((1 + (1 : ℝ) • hpA 5) *ᵥ hpEx) 2 := by
  have hopt : ∀ σ, hpObj 5 1 ((1 + (1 : ℝ) • hpA 5) *ᵥ hpEx) hpEx ≤
      hpObj 5 1 ((1 + (1 : ℝ) • hpA 5) *ᵥ hpEx) σ := (eq_14_1 zero_le_one _ _).2 rfl
  refine ⟨hopt, fun h' => ?_⟩
  have hb := (hp_foc_printed_iff one_pos _ hpEx hopt 2 (by decide) (by decide)).1 h'
  simp [hpExt, hpEx] at hb

/-- **AKMM, p. 411: the Lagrangian form solves the constrained form.** If `τ` minimises the
Lagrangian with `λ ≥ 0`, it minimises the fit subject to `‖Dσ‖² ≤ µ` with `µ = ‖Dτ‖²`. -/
theorem hp_constrained_of_lagrangian {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y τ : Fin T → ℝ)
    (h : ∀ σ, hpObj T lam Y τ ≤ hpObj T lam Y σ) (σ : Fin T → ℝ)
    (hσ : hpPen T σ ≤ hpPen T τ) : hpFit Y τ ≤ hpFit Y σ := by
  have e := h σ
  unfold hpObj at e
  nlinarith

/-- AKMM, p. 411: the solution of the constrained problem with `µ = ‖Dτ_λ‖²` is unique and equals
the Lagrangian trend `τ_λ`. -/
theorem hp_constrained_unique {T : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (Y τ : Fin T → ℝ)
    (h : ∀ σ, hpObj T lam Y τ ≤ hpObj T lam Y σ) (σ : Fin T → ℝ)
    (hσ : hpPen T σ ≤ hpPen T τ) (hfit : hpFit Y σ ≤ hpFit Y τ) : σ = τ := by
  have hle : hpObj T lam Y σ ≤ hpObj T lam Y τ := by
    unfold hpObj; nlinarith
  refine hp_unique hlam Y σ τ (fun ρ => hle.trans (h ρ)) h

/-- **AKMM, p. 411: `µ = 0` imposes a linear trend.** `‖Dτ‖² ≤ 0` iff
`τ_t = τ₀ + t(τ₁ − τ₀)` for every `t`. -/
theorem hp_pen_zero_iff {T : ℕ} (τ : Fin T → ℝ) :
    hpPen T τ ≤ 0 ↔ ∀ t : Fin T, τ t = hpExt τ 0 + t.val * (hpExt τ 1 - hpExt τ 0) := by
  constructor
  · intro h0
    have hall : ∀ k : Fin T, (hpD T *ᵥ τ) k = 0 := by
      have hz : hpPen T τ = 0 := le_antisymm h0 (hp_pen_nonneg T τ)
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ((hpD T *ᵥ τ) k))).1 hz k
        (Finset.mem_univ k)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hsec : ∀ m, m + 2 < T → hpExt τ (m + 2) = 2 * hpExt τ (m + 1) - hpExt τ m := by
      intro m hm
      have := hall ⟨m + 1, by omega⟩
      rw [hp_D_apply] at this
      rw [ite_eq_left (⟨by omega, by omega⟩ : 1 ≤ m + 1 ∧ m + 1 + 1 < T)] at this
      simp only [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega] at this
      linarith
    have key : ∀ m, m < T → hpExt τ m = hpExt τ 0 + m * (hpExt τ 1 - hpExt τ 0) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro hm
        match m, ih with
        | 0, _ => simp
        | 1, _ => simp
        | m + 2, ih =>
          rw [hsec m hm, ih (m + 1) (by omega) (by omega), ih m (by omega) (by omega)]
          push_cast
          ring
    intro t
    rw [← hp_ext_fin τ t]
    exact key t.val t.isLt
  · intro hlin
    have hx : ∀ m, m < T → hpExt τ m = hpExt τ 0 + m * (hpExt τ 1 - hpExt τ 0) := fun m hm => by
      rw [show hpExt τ m = τ ⟨m, hm⟩ by simp [hpExt, hm]]
      exact hlin ⟨m, hm⟩
    have hall : ∀ k : Fin T, (hpD T *ᵥ τ) k = 0 := by
      intro k
      rw [hp_D_apply]
      split_ifs with hk
      · rw [hx _ (by omega), hx _ k.isLt, hx _ hk.2]
        rw [Nat.cast_sub hk.1]
        push_cast
        ring
      · rfl
    unfold hpPen
    simp [hall]

/-- AKMM, p. 412: `1600 × (1/4)⁴ = 6.25` (Ravn–Uhlig scaling from quarterly to annual data). -/
theorem hp_ravn_uhlig : (1600 : ℝ) * (1 / 4) ^ 4 = 6.25 := by norm_num

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The HP trend as `λ → ∞`

AKMM, §14.3.1, p. 411: "In the limit as `λ → ∞`, the extracted trend converges to a linear
function." We prove the precise statement: the HP trend `(I + λA)⁻¹Y` converges to the OLS
linear trend of `Y` (the regression of `Y_t` on `(1, t)`).

* The OLS linear trend (`hpOLS`, `T ≥ 2`): explicit coefficients from the normal equations
  (`hp_ols_normal`); it is affine and has zero penalty (`hp_pen_affine`); among affine sequences
  it is the unique best fit, `fit(x) = fit(τ̂) + ‖x − τ̂‖²` (`hp_ols_pythagoras`).
* Along the HP trends, the fit is bounded by `fit(τ̂)` and the penalty by `fit(τ̂)/λ`
  (`hp_trend_bounds`).
* **The limit** (`hp_limit_ols`): `(I + λA)⁻¹Y → τ̂` as `λ → ∞`, by compactness: every cluster
  point has zero penalty (so it is affine, `hp_pen_zero_iff`) and fit at most `fit(τ̂)`, so it is
  `τ̂`.
-/

namespace AKMM.RealBusinessCycles

open Matrix Filter Topology

/-- `S₁ = Σ t`. -/
def hpS1 (T : ℕ) : ℝ := ∑ t : Fin T, (t.val : ℝ)

/-- `S₂ = Σ t²`. -/
def hpS2 (T : ℕ) : ℝ := ∑ t : Fin T, (t.val : ℝ) ^ 2

/-- The determinant `T S₂ − S₁²` of the normal equations. -/
def hpDet (T : ℕ) : ℝ := T * hpS2 T - hpS1 T ^ 2

/-- The OLS intercept. -/
noncomputable def hpOLSa {T : ℕ} (Y : Fin T → ℝ) : ℝ :=
  ((∑ t, Y t) * hpS2 T - hpS1 T * ∑ t, (t.val : ℝ) * Y t) / hpDet T

/-- The OLS slope. -/
noncomputable def hpOLSb {T : ℕ} (Y : Fin T → ℝ) : ℝ :=
  (T * ∑ t, (t.val : ℝ) * Y t - hpS1 T * ∑ t, Y t) / hpDet T

/-- The OLS linear trend `τ̂_t = â + b̂t`. -/
noncomputable def hpOLS {T : ℕ} (Y : Fin T → ℝ) : Fin T → ℝ := fun t => hpOLSa Y + hpOLSb Y * t.val

/-- `T S₂ − S₁² = T Σ(t − S₁/T)² > 0` for `T ≥ 2`. -/
theorem hp_det_pos {T : ℕ} (hT : 2 ≤ T) : 0 < hpDet T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  set m := hpS1 T / T
  have hsum : ∑ t : Fin T, ((t.val : ℝ) - m) ^ 2 = hpS2 T - hpS1 T ^ 2 / T := by
    have : ∑ t : Fin T, ((t.val : ℝ) - m) ^ 2 =
        hpS2 T - 2 * m * hpS1 T + T * m ^ 2 := by
      simp only [hpS2, hpS1, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rw [this]; simp only [m]; field_simp; ring
  have hpos : 0 < ∑ t : Fin T, ((t.val : ℝ) - m) ^ 2 := by
    by_contra hle
    have h0 := le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun t _ => sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg ((t.val : ℝ) - m)).1 h0
    have e0 := hz ⟨0, by omega⟩ (Finset.mem_univ _)
    have e1 := hz ⟨1, by omega⟩ (Finset.mem_univ _)
    simp only [Nat.cast_zero, Nat.cast_one] at e0 e1
    nlinarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 e0,
      pow_eq_zero_iff (n := 2) two_ne_zero |>.1 e1]
  unfold hpDet
  have : T * hpS2 T - hpS1 T ^ 2 = T * (hpS2 T - hpS1 T ^ 2 / T) := by field_simp
  rw [this, ← hsum]
  positivity

/-- The normal equations of the OLS linear trend: `Σ(Y_t − τ̂_t) = 0` and `Σ t(Y_t − τ̂_t) = 0`. -/
theorem hp_ols_normal {T : ℕ} (hT : 2 ≤ T) (Y : Fin T → ℝ) :
    ∑ t, (Y t - hpOLS Y t) = 0 ∧ ∑ t, (t.val : ℝ) * (Y t - hpOLS Y t) = 0 := by
  have hd := (hp_det_pos hT).ne'
  have e1 : ∑ t, (Y t - hpOLS Y t) = (∑ t, Y t) - T * hpOLSa Y - hpOLSb Y * hpS1 T := by
    simp only [hpOLS, hpS1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have e2 : ∑ t, (t.val : ℝ) * (Y t - hpOLS Y t) =
      (∑ t, (t.val : ℝ) * Y t) - hpOLSa Y * hpS1 T - hpOLSb Y * hpS2 T := by
    have e : ∀ t : Fin T, (t.val : ℝ) * (Y t - hpOLS Y t) =
        (t.val : ℝ) * Y t - hpOLSa Y * t.val - hpOLSb Y * (t.val : ℝ) ^ 2 := fun t => by
      simp only [hpOLS]; ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hpS1, hpS2]
  rw [e1, e2]
  simp only [hpOLSa, hpOLSb]
  constructor <;> field_simp <;> unfold hpDet <;> ring

/-- An affine sequence has zero penalty. -/
theorem hp_pen_affine {T : ℕ} (τ : Fin T → ℝ) (a b : ℝ) (h : ∀ t, τ t = a + b * t.val) :
    hpPen T τ = 0 := by
  have hx : ∀ m, m < T → hpExt τ m = a + b * m := fun m hm => by
    rw [show hpExt τ m = τ ⟨m, hm⟩ by simp [hpExt, hm]]
    exact h ⟨m, hm⟩
  have hall : ∀ k : Fin T, (hpD T *ᵥ τ) k = 0 := by
    intro k
    rw [hp_D_apply]
    split_ifs with hk
    · rw [hx _ (by omega), hx _ k.isLt, hx _ hk.2, Nat.cast_sub hk.1]
      push_cast
      ring
    · rfl
  unfold hpPen
  simp [hall]

/-- **The OLS trend is the best affine fit** (Pythagoras): for affine `x`,
`fit(x) = fit(τ̂) + Σ(τ̂_t − x_t)²`. -/
theorem hp_ols_pythagoras {T : ℕ} (hT : 2 ≤ T) (Y x : Fin T → ℝ) (a b : ℝ)
    (hx : ∀ t, x t = a + b * t.val) :
    hpFit Y x = hpFit Y (hpOLS Y) + ∑ t, (hpOLS Y t - x t) ^ 2 := by
  obtain ⟨n1, n2⟩ := hp_ols_normal hT Y
  have hcross : ∑ t, (Y t - hpOLS Y t) * (hpOLS Y t - x t) = 0 := by
    have e : ∀ t : Fin T, (Y t - hpOLS Y t) * (hpOLS Y t - x t) =
        (hpOLSa Y - a) * (Y t - hpOLS Y t) + (hpOLSb Y - b) * ((t.val : ℝ) * (Y t - hpOLS Y t)) :=
      fun t => by rw [hx t]; simp only [hpOLS]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, n1, n2, mul_zero, add_zero]
  unfold hpFit
  have e : ∀ t : Fin T, (Y t - x t) ^ 2 = (Y t - hpOLS Y t) ^ 2 +
      2 * ((Y t - hpOLS Y t) * (hpOLS Y t - x t)) + (hpOLS Y t - x t) ^ 2 := fun t => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
  ring

/-- The OLS trend is affine. -/
theorem hp_ols_affine {T : ℕ} (Y : Fin T → ℝ) :
    ∀ t, hpOLS Y t = hpOLSa Y + hpOLSb Y * t.val := fun _ => rfl

/-- Bounds along the HP trends: for `λ > 0`, `fit(τ_λ) ≤ fit(τ̂)` and
`λ‖Dτ_λ‖² ≤ fit(τ̂)`. -/
theorem hp_trend_bounds {T : ℕ} {lam : ℝ} (hlam : 0 < lam) (Y : Fin T → ℝ) :
    hpFit Y ((1 + lam • hpA T)⁻¹ *ᵥ Y) ≤ hpFit Y (hpOLS Y) ∧
      lam * hpPen T ((1 + lam • hpA T)⁻¹ *ᵥ Y) ≤ hpFit Y (hpOLS Y) := by
  have h := hp_trend_exists hlam.le Y (hpOLS Y)
  have hp := hp_pen_affine (hpOLS Y) _ _ (hp_ols_affine Y)
  unfold hpObj at h
  rw [hp, mul_zero, add_zero] at h
  have h1 := mul_nonneg hlam.le (hp_pen_nonneg T ((1 + lam • hpA T)⁻¹ *ᵥ Y))
  have h2 := hp_fit_nonneg Y ((1 + lam • hpA T)⁻¹ *ᵥ Y)
  constructor <;> linarith

theorem hp_continuous_pen (T : ℕ) : Continuous (hpPen T) := by
  unfold hpPen
  fun_prop

theorem hp_continuous_fit {T : ℕ} (Y : Fin T → ℝ) : Continuous (hpFit Y) := by
  unfold hpFit
  fun_prop

/-- A continuous function bounded eventually along `f` is bounded at cluster points. -/
theorem hp_cluster_le {α X : Type*} [TopologicalSpace X] {l : Filter α} {f : α → X} {x : X}
    {g : X → ℝ} (hg : Continuous g) (hx : MapClusterPt x l f) {c : ℝ}
    (hev : ∀ᶠ a in l, g (f a) ≤ c) : g x ≤ c := by
  by_contra h
  have hn : ∀ᶠ y in 𝓝 x, c < g y := (hg.tendsto x).eventually (lt_mem_nhds (not_le.1 h))
  obtain ⟨a, h1, h2⟩ := ((hx.frequently hn).and_eventually hev).exists
  linarith

/-- **AKMM, p. 411: as `λ → ∞` the HP trend converges to a linear function**, namely the OLS
linear trend of `Y` (`T ≥ 2`). -/
theorem hp_limit_ols {T : ℕ} (hT : 2 ≤ T) (Y : Fin T → ℝ) :
    Tendsto (fun lam : ℝ => (1 + lam • hpA T)⁻¹ *ᵥ Y) atTop (𝓝 (hpOLS Y)) := by
  set C := hpFit Y (hpOLS Y)
  set τ := fun lam : ℝ => (1 + lam • hpA T)⁻¹ *ᵥ Y
  set K : Set (Fin T → ℝ) := Set.pi Set.univ fun t => Set.Icc (Y t - (C + 1)) (Y t + (C + 1))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ᶠ lam in atTop, τ lam ∈ K := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    intro t _
    have hfit := (hp_trend_bounds hlam Y).1
    have ht : (Y t - τ lam t) ^ 2 ≤ C := by
      refine le_trans ?_ hfit
      exact Finset.single_le_sum (f := fun s => (Y s - τ lam s) ^ 2) (fun s _ => sq_nonneg _)
        (Finset.mem_univ t)
    have hab : |Y t - τ lam t| ≤ C + 1 := by
      have := sq_abs (Y t - τ lam t)
      nlinarith [abs_nonneg (Y t - τ lam t)]
    rw [abs_le] at hab
    exact ⟨by linarith, by linarith⟩
  refine hK.tendsto_nhds_of_unique_mapClusterPt hmem fun x _ hx => ?_
  have hpen : hpPen T x ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    refine hp_cluster_le (hp_continuous_pen T) hx ?_
    filter_upwards [eventually_gt_atTop ((C + 1) / ε)] with lam hlam
    have hl : 0 < lam := lt_of_le_of_lt (div_nonneg (by linarith [hp_fit_nonneg Y (hpOLS Y)])
      hε.le) hlam
    have hb := (hp_trend_bounds hl Y).2
    have h1 : C + 1 < lam * ε := by rwa [div_lt_iff₀ hε] at hlam
    have hp0 := hp_pen_nonneg T (τ lam)
    by_contra hc
    nlinarith
  have hfit : hpFit Y x ≤ C := by
    refine hp_cluster_le (hp_continuous_fit Y) hx ?_
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact (hp_trend_bounds hlam Y).1
  have haff := (hp_pen_zero_iff x).1 hpen
  have hpy := hp_ols_pythagoras hT Y x (hpExt x 0) (hpExt x 1 - hpExt x 0)
    (fun t => by rw [haff t]; ring)
  have hsq : ∑ t, (hpOLS Y t - x t) ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  funext t
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => sq_nonneg (hpOLS Y s - x s)).1 hsq t
    (Finset.mem_univ t)
  have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
  linarith

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The recursive structural VAR

AKMM, §14.3.3, pp. 417–419. The structural VAR `AXₜ = FXₜ₋₁ + εₜ` with a lower-triangular `A`
(timing restrictions: the first variable, TFP, does not respond contemporaneously to the others).

* A lower-triangular `A` has `det A = Π aᵢᵢ` (`svar_det`), so it is invertible iff its diagonal
  entries are nonzero (`svar_isUnit_iff`), and then `A⁻¹` is lower triangular
  (`svar_inv_lower`).
* The reduced form `Xₜ = A⁻¹FXₜ₋₁ + A⁻¹εₜ`: the reduced-form innovations are `ηₜ = A⁻¹εₜ` and
  the structural shocks are backed out as `εₜ = Aηₜ` (`svar_reduced_form`).
* **The impulse response** `∂X_{t+s}/∂εₜ = (A⁻¹F)ˢA⁻¹` (`svar_irf`), via AKMM Chapter 7's
  `sde_impulse_response` for the reduced form.
* The recursive restriction: on impact the first variable responds only to its own shock, and
  in general variable `i` responds on impact only to shocks `j ≤ i` (`svar_impact_recursive`).
-/

namespace AKMM.RealBusinessCycles

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- AKMM, p. 418: for a lower-triangular `A`, `det A = Π aᵢᵢ`. -/
theorem svar_det (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) : A.det = ∏ i, A i i :=
  det_of_isLowerTriangular A hA

/-- AKMM, p. 419 ("we invert the A matrix"): a lower-triangular `A` is invertible iff its
diagonal entries are nonzero. -/
theorem svar_isUnit_iff (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) :
    IsUnit A ↔ ∀ i, A i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, svar_det A hA, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp

/-- The inverse of an invertible lower-triangular matrix is lower triangular. -/
theorem svar_inv_lower (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) (hu : IsUnit A) :
    A⁻¹.IsLowerTriangular := by
  have : Invertible A := invertibleOfIsUnitDet A ((isUnit_iff_isUnit_det A).1 hu)
  exact blockTriangular_inv_of_blockTriangular hA

omit [LinearOrder n] in
/-- **AKMM, p. 418: the reduced form.** If `A` is invertible, `AXₜ₊₁ = FXₜ + εₜ₊₁` iff
`Xₜ₊₁ = A⁻¹FXₜ + ηₜ₊₁` with reduced-form innovation `ηₜ₊₁ = A⁻¹εₜ₊₁`; and the structural
shocks are recovered from the innovations as `ε = Aη`. -/
theorem svar_reduced_form (A F : Matrix n n ℝ) (hu : IsUnit A) (x x' e : n → ℝ) :
    (A *ᵥ x' = F *ᵥ x + e ↔ x' = (A⁻¹ * F) *ᵥ x + A⁻¹ *ᵥ e) ∧ A *ᵥ (A⁻¹ *ᵥ e) = e := by
  have hd := (isUnit_iff_isUnit_det A).1 hu
  have h1 : A⁻¹ * A = 1 := nonsing_inv_mul A hd
  have h2 : A * A⁻¹ = 1 := mul_nonsing_inv A hd
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by rw [mulVec_mulVec, h2, one_mulVec]⟩
  · rw [← mulVec_mulVec, ← mulVec_add, ← h, mulVec_mulVec, h1, one_mulVec]
  · rw [h, mulVec_add, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      one_mulVec]

omit [LinearOrder n] in
/-- **AKMM, p. 419: the impulse response of the SVAR.** Let `X` and `X′` solve
`AXₜ₊₁ = FXₜ + εₜ₊₁` from the same `X₀`, with structural shocks that differ only by `v` at date
`s + 1`. Then `X′` and `X` agree before `s + 1` and `X′_{s+1+h} − X_{s+1+h} = (A⁻¹F)ʰA⁻¹v`. -/
theorem svar_irf (A F : Matrix n n ℝ) (hu : IsUnit A) {x x' e e' : ℕ → n → ℝ}
    (hx : ∀ t, A *ᵥ x (t + 1) = F *ᵥ x t + e (t + 1))
    (hx' : ∀ t, A *ᵥ x' (t + 1) = F *ᵥ x' t + e' (t + 1)) (h0 : x' 0 = x 0) (s : ℕ)
    (v : n → ℝ) (he : ∀ t, e' t = if t = s + 1 then e t + v else e t) :
    (∀ t ≤ s, x' t = x t) ∧ ∀ h, x' (s + 1 + h) - x (s + 1 + h) = ((A⁻¹ * F) ^ h * A⁻¹) *ᵥ v := by
  refine AKMM.Uncertainty.sde_impulse_response (C := 0) (fun t => ?_) (fun t => ?_) h0 s v he
  · rw [add_zero]; exact ((svar_reduced_form A F hu _ _ _).1).1 (hx t)
  · rw [add_zero]; exact ((svar_reduced_form A F hu _ _ _).1).1 (hx' t)

/-- AKMM, p. 419: with the recursive (lower-triangular) `A`, variable `i` responds on impact
only to structural shocks `j ≤ i`; in particular the first variable (TFP) responds on impact
only to its own shock. -/
theorem svar_impact_recursive (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) (hu : IsUnit A)
    {i j : n} (hij : i < j) : (A⁻¹) i j = 0 :=
  svar_inv_lower A hA hu hij

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A simple business-cycle model

AKMM, §14.4.1, (14.2)–(14.7), pp. 420–422. The period utility of (14.2), `ln c + φ ln(1 − ℓ)`, is
Miao's `rb_u φ` (Chapter 14 of Miao, imported); production is `Y = zℓ` (14.3), the budget is
`c + B = wℓ + RB₋₁` (14.4).

* The firm: with linear technology, a profit-maximising firm employing `ℓ > 0` pays `w = z`
  (`sm_wage`).
* **(14.5)**: at an interior optimum of `ℓ ↦ ln(wℓ + m) + φ ln(1 − ℓ)` (`m = RB₋₁ − B`),
  `w/c = φ/(1 − ℓ)` (`eq_14_5`); conversely (14.5) makes `ℓ` a global maximiser
  (`sm_static_suff`, via Miao's tangent inequality `rb_u_tangent`).
* **(14.6)**: at an interior optimum of the bond choice, `1/c = βΣₛ pₛRₛ/c′ₛ` (`eq_14_6`).
* **(14.7)**: with `B = 0`, (14.5) becomes `φ/(1 − ℓ) = 1/ℓ`, so `ℓ = 1/(1 + φ)` (`eq_14_7`).
* Equilibrium (`sm_equilibrium`): hours `1/(1 + φ)` whatever `z`, and `c = Y = z/(1 + φ)`, so
  output, consumption and TFP are perfectly correlated.
* The interest rate: with `zₜ₊₁ = zₜ^ρ e^{εₛ}` (finitely many shocks), the Euler equation at
  `B = 0` gives `R = zₜ^{ρ−1}/(βΣ pₛe^{−εₛ})`, which falls when TFP rises if `ρ < 1`
  (`sm_interest_rate`, `sm_interest_rate_falls`).
* The Frisch elasticity of log–log preferences is `(1 − ℓ)/ℓ` (`sm_frisch`, through AKMM
  Chapter 12's `frischF`; also `sm_frisch_cd` from Chapter 12's `dyn_frisch_cd` at `σ = 1`), and
  `2` at `ℓ = 1/3` (`sm_frisch_two`); holding the marginal utility `λ` fixed, hours
  `ℓ(w) = 1 − φ/(λw)` respond to the wage with elasticity `(1 − ℓ)/ℓ` (`sm_frisch_response`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

/-- AKMM, p. 420: "perfect competition and linear production … imply that the equilibrium wage
will be equal to TFP, `w = z`": if employing `ℓ > 0` maximises the profit `(z − w)ℓ'` over
`ℓ' ≥ 0`, then `w = z`. -/
theorem sm_wage {z w ℓ : ℝ} (hℓ : 0 < ℓ) (hmax : ∀ ℓ', 0 ≤ ℓ' → (z - w) * ℓ' ≤ (z - w) * ℓ) :
    w = z := by
  have h0 := hmax 0 le_rfl
  have h2 := hmax (2 * ℓ) (by linarith)
  nlinarith

/-- The derivative of the static objective `ℓ ↦ ln(wℓ + m) + φ ln(1 − ℓ)`. -/
theorem sm_static_deriv {φ w m ℓ : ℝ} (hc : 0 < w * ℓ + m) (hℓ : ℓ < 1) :
    HasDerivAt (fun x => Real.log (w * x + m) + φ * Real.log (1 - x))
      (w / (w * ℓ + m) - φ / (1 - ℓ)) ℓ := by
  have h1 : HasDerivAt (fun x => w * x + m) w ℓ := by
    simpa using ((hasDerivAt_id ℓ).const_mul w).add_const m
  have h2 : HasDerivAt (fun x => 1 - x) (-1) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_sub 1
  have := (h1.log hc.ne').add ((h2.log (by linarith)).const_mul φ)
  convert this using 1
  ring

/-- **AKMM, (14.5), p. 421.** If `ℓ ∈ (0, 1)` maximises `ln(wℓ′ + m) + φ ln(1 − ℓ′)` locally
(consumption `c = wℓ + m > 0`), then `w/c = φ/(1 − ℓ)`. -/
theorem eq_14_5 {φ w m ℓ : ℝ} (hc : 0 < w * ℓ + m) (hℓ : ℓ < 1)
    (hmax : IsLocalMax (fun x => Real.log (w * x + m) + φ * Real.log (1 - x)) ℓ) :
    w / (w * ℓ + m) = φ / (1 - ℓ) := by
  have := hmax.hasDerivAt_eq_zero (sm_static_deriv hc hℓ)
  linarith

/-- AKMM, p. 421: (14.5) is sufficient: if `w/c = φ/(1 − ℓ)` with `c = wℓ + m > 0`, `ℓ < 1`,
`φ ≥ 0`, then `ℓ` maximises `ln(wℓ′ + m) + φ ln(1 − ℓ′)` over all `ℓ′ < 1` with positive
consumption. -/
theorem sm_static_suff {φ w m ℓ : ℝ} (hφ : 0 ≤ φ) (hc : 0 < w * ℓ + m) (hℓ : ℓ < 1)
    (hfoc : w / (w * ℓ + m) = φ / (1 - ℓ)) (ℓ' : ℝ) (hc' : 0 < w * ℓ' + m) (hℓ' : ℓ' < 1) :
    rb_u φ (w * ℓ' + m) ℓ' ≤ rb_u φ (w * ℓ + m) ℓ := by
  have ht := rb_u_tangent hφ hc hℓ hc' hℓ'
  have e : (w * ℓ' + m - (w * ℓ + m)) / (w * ℓ + m) - φ * ((ℓ' - ℓ) / (1 - ℓ)) =
      (ℓ' - ℓ) * (w / (w * ℓ + m) - φ / (1 - ℓ)) := by
    field_simp
    ring
  rw [hfoc, sub_self, mul_zero] at e
  linarith

/-- **AKMM, (14.6), p. 421: the Euler equation.** With income `y₀` today and `yₛ` tomorrow in
state `s` (probability `pₛ`), gross returns `Rₛ`, if the bond holding `b` maximises
`ln(y₀ − b) + βΣₛ pₛ ln(yₛ + Rₛb)` locally (interior consumption), then
`1/c = βΣₛ pₛRₛ/c′ₛ`. -/
theorem eq_14_6 {S : Type*} [Fintype S] {β y0 b : ℝ} {p y R : S → ℝ} (hc : 0 < y0 - b)
    (hc' : ∀ s, 0 < y s + R s * b)
    (hmax : IsLocalMax (fun x => Real.log (y0 - x) + β * ∑ s, p s * Real.log (y s + R s * x)) b) :
    1 / (y0 - b) = β * ∑ s, p s * (R s / (y s + R s * b)) := by
  have h0 : HasDerivAt (fun x => y0 - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub y0
  have hs : ∀ s, HasDerivAt (fun x => Real.log (y s + R s * x)) (R s / (y s + R s * b)) b := by
    intro s
    have : HasDerivAt (fun x => y s + R s * x) (R s) b := by
      simpa using ((hasDerivAt_id b).const_mul (R s)).const_add (y s)
    exact this.log (hc' s).ne'
  have hsum : HasDerivAt (fun x => ∑ s, p s * Real.log (y s + R s * x))
      (∑ s, p s * (R s / (y s + R s * b))) b :=
    HasDerivAt.fun_sum (u := Finset.univ) fun s _ => (hs s).const_mul (p s)
  have hd := (h0.log hc.ne').add (hsum.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  have e : -1 / (y0 - b) = -(1 / (y0 - b)) := by ring
  linarith

/-- **AKMM, (14.7), p. 421.** With zero bond holdings `c = wℓ` (`w > 0`), the intratemporal
condition (14.5) reads `φ/(1 − ℓ) = 1/ℓ`, and holds iff `ℓ = 1/(1 + φ)`. -/
theorem eq_14_7 {φ w ℓ : ℝ} (hφ : 0 ≤ φ) (hw : 0 < w) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (w / (w * ℓ + 0) = φ / (1 - ℓ) ↔ φ / (1 - ℓ) = w / (w * ℓ) ∧ w / (w * ℓ) = 1 / ℓ ∧
      ℓ = 1 / (1 + φ)) := by
  have h1 : 0 < 1 - ℓ := by linarith
  have hwl : w / (w * ℓ) = 1 / ℓ := by field_simp
  rw [add_zero]
  constructor
  · intro h
    refine ⟨h.symm, hwl, ?_⟩
    rw [hwl] at h
    field_simp at h ⊢
    linarith
  · rintro ⟨h, -, -⟩
    exact h.symm

/-- **AKMM, p. 421: constant hours in equilibrium.** With `w = z > 0` and `B = 0`, the household's
intratemporal condition holds iff `ℓ = 1/(1 + φ)`, whatever `z`; then `c = Y = zℓ = z/(1 + φ)`, so
output, consumption and TFP are proportional (perfectly correlated) and hours do not move. -/
theorem sm_equilibrium {φ z ℓ : ℝ} (hφ : 0 ≤ φ) (hz : 0 < z) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hfoc : z / (z * ℓ + 0) = φ / (1 - ℓ)) :
    ℓ = 1 / (1 + φ) ∧ z * ℓ = z / (1 + φ) := by
  have h := ((eq_14_7 hφ hz hℓ0 hℓ1).1 hfoc).2.2
  refine ⟨h, by rw [h]; ring⟩

/-- AKMM, p. 421: "the real interest rate must adjust": with `B = 0`, `cₜ = zₜ/(1 + φ)` and
`zₜ₊₁ = zₜ^ρe^{εₛ}` in state `s` (probability `pₛ`), the Euler equation (14.6) with a risk-free
return `R` holds iff `R = zₜ^{ρ−1}/(βΣₛ pₛe^{−εₛ})`. -/
theorem sm_interest_rate {S : Type*} [Fintype S] {φ β ρ z R : ℝ} {p ε : S → ℝ} (hφ : 0 ≤ φ)
    (hβ : 0 < β) (hz : 0 < z) (hE : 0 < ∑ s, p s * Real.exp (-ε s)) :
    1 / (z / (1 + φ)) = β * ∑ s, p s * (R / (z ^ ρ * Real.exp (ε s) / (1 + φ))) ↔
      R = z ^ (ρ - 1) / (β * ∑ s, p s * Real.exp (-ε s)) := by
  have h1 : 0 < 1 + φ := by linarith
  have hzr : 0 < z ^ ρ := Real.rpow_pos_of_pos hz ρ
  have hsum : ∑ s, p s * (R / (z ^ ρ * Real.exp (ε s) / (1 + φ))) =
      R * (1 + φ) / z ^ ρ * ∑ s, p s * Real.exp (-ε s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Real.exp_neg]
    field_simp
  have hzz : z ^ (ρ - 1) = z ^ ρ / z := Real.rpow_sub_one hz.ne' ρ
  rw [hsum, hzz]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp

/-- AKMM, p. 421: "When TFP is high, consumption rises and the real interest rate falls": for
`ρ < 1`, `R(z) = z^{ρ−1}/(βΣₛ pₛe^{−εₛ})` is strictly decreasing in `z`. -/
theorem sm_interest_rate_falls {S : Type*} [Fintype S] {β ρ : ℝ} {p ε : S → ℝ} (hβ : 0 < β)
    (hρ : ρ < 1) (hE : 0 < ∑ s, p s * Real.exp (-ε s)) {z z' : ℝ} (hz : 0 < z) (hzz : z < z') :
    z' ^ (ρ - 1) / (β * ∑ s, p s * Real.exp (-ε s)) <
      z ^ (ρ - 1) / (β * ∑ s, p s * Real.exp (-ε s)) :=
  div_lt_div_of_pos_right (Real.rpow_lt_rpow_of_neg hz hzz (by linarith)) (mul_pos hβ hE)

/-- The partial derivatives of `φ ln(1 − ℓ)`: `U_ℓ = −φ/(1 − ℓ)`, `U_ℓℓ = −φ/(1 − ℓ)²`. -/
theorem sm_leisure_derivs {φ ℓ : ℝ} (hℓ : ℓ < 1) :
    HasDerivAt (fun x => φ * Real.log (1 - x)) (-(φ / (1 - ℓ))) ℓ ∧
      HasDerivAt (fun x => -(φ / (1 - x))) (-(φ / (1 - ℓ) ^ 2)) ℓ := by
  have h2 : HasDerivAt (fun x => 1 - x) (-1) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_sub 1
  have h1 : 1 - ℓ ≠ 0 := by linarith
  constructor
  · convert (h2.log h1).const_mul φ using 1
    field_simp
  · convert ((h2.inv h1).const_mul φ).neg using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp

/-- **AKMM, p. 421: the Frisch elasticity of log–log preferences is `(1 − ℓ)/ℓ`**, by AKMM
Chapter 12's formula (12.21) `ε^F = U_ℓ/(ℓU_ℓℓ − ℓU_ℓc²/U_cc)` with the separable partials
`U_ℓ = −φ/(1 − ℓ)`, `U_ℓℓ = −φ/(1 − ℓ)²`, `U_ℓc = 0`. -/
theorem sm_frisch {φ ℓ Ucc : ℝ} (hφ : 0 < φ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    AKMM.LaborSupply.frischF ℓ (-(φ / (1 - ℓ))) (-(φ / (1 - ℓ) ^ 2)) 0 0 Ucc = (1 - ℓ) / ℓ := by
  unfold AKMM.LaborSupply.frischF
  have h1 : 0 < 1 - ℓ := by linarith
  have := hφ.ne'
  simp only [mul_zero, zero_div, sub_zero]
  field_simp

/-- AKMM, p. 421: "If households work one-third of their available time, this gives a Frisch
elasticity of 2". -/
theorem sm_frisch_two {φ Ucc : ℝ} (hφ : 0 < φ) :
    AKMM.LaborSupply.frischF (1 / 3) (-(φ / (1 - 1 / 3))) (-(φ / (1 - 1 / 3) ^ 2)) 0 0 Ucc = 2 := by
  rw [sm_frisch hφ (by norm_num) (by norm_num)]
  norm_num

/-- The same value from AKMM Chapter 12's Cobb–Douglas formula `dyn_frisch_cd` at `σ = 1`
(the calibrated utility `(1 − ψ) ln c + ψ ln(1 − ℓ)` of p. 428 has these partials). -/
theorem sm_frisch_cd {ψ c ℓ : ℝ} (hψ : 0 < ψ) (hψ1 : ψ < 1) (hc : 0 < c) (hℓ0 : 0 < ℓ)
    (hℓ1 : 0 < 1 - ℓ) :
    AKMM.LaborSupply.frischF ℓ (-(ψ * c ^ ((1 - ψ) * (1 - 1)) * (1 - ℓ) ^ (ψ * (1 - 1) - 1)))
      (ψ * (ψ * (1 - 1) - 1) * c ^ ((1 - ψ) * (1 - 1)) * (1 - ℓ) ^ (ψ * (1 - 1) - 1 - 1))
      (-((1 - ψ) * ψ * (1 - 1) * c ^ ((1 - ψ) * (1 - 1) - 1) * (1 - ℓ) ^ (ψ * (1 - 1) - 1)))
      (-((1 - ψ) * ψ * (1 - 1) * c ^ ((1 - ψ) * (1 - 1) - 1) * (1 - ℓ) ^ (ψ * (1 - 1) - 1)))
      ((1 - ψ) * ((1 - ψ) * (1 - 1) - 1) * c ^ ((1 - ψ) * (1 - 1) - 1 - 1) *
        (1 - ℓ) ^ (ψ * (1 - 1))) = (1 - ℓ) / ℓ := by
  rw [AKMM.LaborSupply.dyn_frisch_cd hψ hψ1 one_ne_zero (by norm_num) hc hℓ0 hℓ1]
  ring

/-- AKMM, p. 421: the Frisch elasticity measures the response of hours to the wage "holding the
marginal utility of consumption constant": with `λ > 0` fixed, `φ/(1 − ℓ) = λw` gives
`ℓ(w) = 1 − φ/(λw)`, and along `w(s) = we^s` the derivative of `ln ℓ` at `s = 0` is
`(1 − ℓ)/ℓ`. -/
theorem sm_frisch_response {φ lam w : ℝ} (hφ : 0 < φ) (hlam : 0 < lam) (hw : 0 < w)
    (hℓ : 0 < 1 - φ / (lam * w)) :
    HasDerivAt (fun s => Real.log (1 - φ / (lam * (w * Real.exp s))))
      ((1 - (1 - φ / (lam * w))) / (1 - φ / (lam * w))) 0 := by
  have hg : HasDerivAt (fun s => 1 - φ / (lam * (w * Real.exp s))) (φ / (lam * w)) 0 := by
    have he : HasDerivAt (fun s => lam * (w * Real.exp s)) (lam * w) 0 := by
      have := ((Real.hasDerivAt_exp 0).const_mul w).const_mul lam
      simpa using this
    have hne : lam * (w * Real.exp 0) ≠ 0 := by positivity
    have := (he.inv hne).const_mul φ |>.const_sub 1
    convert this using 1
    · funext s; simp [div_eq_mul_inv]
    · simp only [Real.exp_zero, mul_one]
      field_simp
  have := hg.log (by simpa using hℓ.ne')
  convert this using 1
  simp

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The core RBC model: the planner's Bellman equation

AKMM, §14.4.2, (14.8)–(14.11), pp. 422–424.

TFP takes finitely many values `z s` and moves from `s` to `s′` with probability `P s s′`.
Resources are `zF(k, ℓ) + (1 − δ)k`, consumption `c = zF(k, ℓ) + (1 − δ)k − k′`, and
`V(s, k) = max_{k′, ℓ} U(c, 1 − ℓ) + βΣ_{s′}P(s, s′)V(s′, k′)`, attained at `k′ = g(s, k)`,
`ℓ = h(s, k)` with interior choices (`rbc_Bellman`). Partial derivatives are Miao's
`rx_HasPartials` (imported).

* **(14.8)** `zF₂(k, ℓ)U₁ = U₂`, i.e. `zF₂ = U₂/U₁` (`eq_14_8`), from the labour choice.
* **(14.9)** `U₁ = βΣP V₁(s′, k′)` (`eq_14_9`), from the capital choice.
* **(14.10)** the envelope condition `V₁(s, k) = (zF₁ + 1 − δ)U₁` (`eq_14_10`), by comparing
  with the plan that keeps `(k′, ℓ)`.
* **(14.11)** the stochastic Euler equation (`eq_14_11`).
* The printed Bellman equation omits `β`; with it, (14.9) holds with `β`, and the two first-order
  conditions are compatible only if `β = 1` or `U₁ = 0` (`rbc_printed_bellman_beta`).
* Non-vacuity (`rbc_example_bellman`): `U(c, x) = c + ln x`, `F(k, ℓ) = k + ℓ`, `z = 2`,
  `δ = 1`, `β = 1/2`, with `V(k) = 2k + 2(1 − ln 2)`, `g(k) = k`, `h = 1/2`.
* The welfare theorems (p. 423, asserted): for the calibrated utility `(1 − φ)ln c + φ ln(1 − ℓ)`
  and Cobb–Douglas technology they are Miao's `rb_sce_iff` and `rb_sce_optimal` (imported), whose
  utility `ln c + χ ln(1 − ℓ)` is a positive multiple of the calibrated one with
  `χ = φ/(1 − φ)` (`rbc_calib_utility`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

variable {S : Type*} [Fintype S]

/-- Resources `zF(k, ℓ) + (1 − δ)k`. -/
def rbcRes (F : ℝ × ℝ → ℝ) (δ z k ℓ : ℝ) : ℝ := z * F (k, ℓ) + (1 - δ) * k

/-- The Bellman equation of the core RBC planner (AKMM, p. 423, with the discount factor `β`):
at every `k > 0` the policy `(g, h)` is interior (`g > 0`, `0 < h < 1`, positive consumption),
attains the maximum, and `V` is the maximum value. -/
def rbc_Bellman (U F : ℝ × ℝ → ℝ) (β δ : ℝ) (z : S → ℝ) (P : S → S → ℝ) (V g h : S → ℝ → ℝ) :
    Prop :=
  ∀ s k, 0 < k → (0 < g s k ∧ 0 < h s k ∧ h s k < 1 ∧ g s k < rbcRes F δ (z s) k (h s k)) ∧
    V s k = U (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k) +
      β * ∑ s', P s s' * V s' (g s k) ∧
    ∀ k' ℓ', 0 < k' → 0 < ℓ' → ℓ' < 1 → k' < rbcRes F δ (z s) k ℓ' →
      U (rbcRes F δ (z s) k ℓ' - k', 1 - ℓ') + β * ∑ s', P s s' * V s' k' ≤ V s k

/-- **AKMM, (14.8), p. 423: the intratemporal condition.** If `U` has partials `(U₁, U₂)` at
`(c, 1 − ℓ)` and `F` has partials `(F₁, F₂)` at `(k, ℓ)` (the policy at `(s, k)`), then
`zF₂(k, ℓ)U₁ = U₂`; so `zF₂ = U₂/U₁` when `U₁ ≠ 0`. -/
theorem eq_14_8 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {s : S} {k : ℝ} (hk : 0 < k) {U1 U2 F1 F2 : ℝ}
    (hU : rx_HasPartials U U1 U2 (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    (hF : rx_HasPartials F F1 F2 (k, h s k)) :
    z s * F2 * U1 = U2 ∧ (U1 ≠ 0 → z s * F2 = U2 / U1) := by
  obtain ⟨⟨hg0, hh0, hh1, hgc⟩, hval, hle⟩ := hB s k hk
  set ℓ := h s k
  set k' := g s k
  -- the resources along the labour choice
  have hFℓ : HasDerivAt (fun x => F (k, x)) F2 ℓ := by
    have := hF.comp (x := fun _ => k) (y := id) (hasDerivAt_const ℓ k) (hasDerivAt_id ℓ)
    simpa using this
  have hres : HasDerivAt (fun x => rbcRes F δ (z s) k x - k') (z s * F2) ℓ := by
    have := (hFℓ.const_mul (z s)).add_const ((1 - δ) * k) |>.sub_const k'
    simpa [rbcRes] using this
  have hleis : HasDerivAt (fun x : ℝ => 1 - x) (-1) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_sub 1
  have hd : HasDerivAt (fun x => U (rbcRes F δ (z s) k x - k', 1 - x))
      (U1 * (z s * F2) + U2 * (-1)) ℓ := hU.comp hres hleis
  have hpos : (0 : ℝ) < rbcRes F δ (z s) k ℓ - k' := by linarith
  have hmax : IsLocalMax (fun x => U (rbcRes F δ (z s) k x - k', 1 - x)) ℓ := by
    filter_upwards [lt_mem_nhds hh0, gt_mem_nhds hh1,
      continuousAt_const.eventually_lt hres.continuousAt hpos] with x h1 h2 h3
    have := hle k' x hg0 h1 h2 (by linarith)
    rw [hval] at this
    linarith
  have h0 := hmax.hasDerivAt_eq_zero hd
  refine ⟨by linarith, fun hU1 => ?_⟩
  field_simp
  linarith

/-- **AKMM, (14.9), p. 423: the capital choice.** If `U` has partials `(U₁, U₂)` at the optimum
and each `V(s′, ·)` is differentiable at `k′ = g(s, k)` with derivative `V₁(s′)`, then
`U₁ = βΣ_{s′}P(s, s′)V₁(s′)`. -/
theorem eq_14_9 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {s : S} {k : ℝ} (hk : 0 < k) {U1 U2 : ℝ}
    (hU : rx_HasPartials U U1 U2 (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    {V1 : S → ℝ} (hV : ∀ s', HasDerivAt (V s') (V1 s') (g s k)) :
    U1 = β * ∑ s', P s s' * V1 s' := by
  obtain ⟨⟨hg0, hh0, hh1, hgc⟩, hval, hle⟩ := hB s k hk
  set ℓ := h s k
  set k' := g s k
  set R := rbcRes F δ (z s) k ℓ
  have hc : HasDerivAt (fun x => R - x) (-1) k' := by simpa using (hasDerivAt_id k').const_sub R
  have hU' : HasDerivAt (fun x => U (R - x, 1 - ℓ)) (U1 * (-1) + U2 * 0) k' :=
    hU.comp (x := fun x => R - x) (y := fun _ => 1 - ℓ) hc (hasDerivAt_const k' _)
  have hsum : HasDerivAt (fun x => ∑ s', P s s' * V s' x) (∑ s', P s s' * V1 s') k' :=
    HasDerivAt.fun_sum (u := Finset.univ) fun s' _ => (hV s').const_mul (P s s')
  have hd := hU'.add (hsum.const_mul β)
  have hmax : IsLocalMax (fun x => U (R - x, 1 - ℓ) + β * ∑ s', P s s' * V s' x) k' := by
    filter_upwards [lt_mem_nhds hg0, gt_mem_nhds hgc] with x h1 h2
    have := hle x ℓ h1 hh0 hh1 h2
    rw [hval] at this
    exact this
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, (14.10), p. 423: the envelope condition.** If `V(s, ·)` is differentiable at `k`
with derivative `V₁`, `U` has partials `(U₁, U₂)` at the optimum and `F` has partials
`(F₁, F₂)` at `(k, ℓ)`, then `V₁ = (zF₁(k, ℓ) + 1 − δ)U₁`. -/
theorem eq_14_10 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {s : S} {k : ℝ} (hk : 0 < k) {U1 U2 F1 F2 V1 : ℝ}
    (hU : rx_HasPartials U U1 U2 (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    (hF : rx_HasPartials F F1 F2 (k, h s k)) (hV : HasDerivAt (V s) V1 k) :
    V1 = (z s * F1 + 1 - δ) * U1 := by
  obtain ⟨⟨hg0, hh0, hh1, hgc⟩, hval, -⟩ := hB s k hk
  set ℓ := h s k
  set k' := g s k
  set W := β * ∑ s', P s s' * V s' k'
  have hFk : HasDerivAt (fun j => F (j, ℓ)) F1 k := by
    have := hF.comp (x := id) (y := fun _ => ℓ) (hasDerivAt_id k) (hasDerivAt_const k ℓ)
    simpa using this
  have hres : HasDerivAt (fun j => rbcRes F δ (z s) j ℓ - k') (z s * F1 + (1 - δ)) k := by
    have := ((hFk.const_mul (z s)).add ((hasDerivAt_id k).const_mul (1 - δ))).sub_const k'
    simpa [rbcRes] using this
  have hd1 : HasDerivAt (fun j => U (rbcRes F δ (z s) j ℓ - k', 1 - ℓ))
      (U1 * (z s * F1 + (1 - δ)) + U2 * 0) k :=
    hU.comp hres (hasDerivAt_const k _)
  have hd : HasDerivAt (fun j => V s j - (U (rbcRes F δ (z s) j ℓ - k', 1 - ℓ) + W))
      (V1 - (U1 * (z s * F1 + (1 - δ)) + U2 * 0)) k := hV.sub (hd1.add_const W)
  have hpos : (0 : ℝ) < rbcRes F δ (z s) k ℓ - k' := by linarith
  have hmin : IsLocalMin (fun j => V s j - (U (rbcRes F δ (z s) j ℓ - k', 1 - ℓ) + W)) k := by
    filter_upwards [lt_mem_nhds hk, continuousAt_const.eventually_lt hres.continuousAt hpos]
      with j hj hj'
    have := (hB s j hj).2.2 k' ℓ hg0 hh0 hh1 (by linarith)
    have h0 : V s k - (U (rbcRes F δ (z s) k ℓ - k', 1 - ℓ) + W) = 0 := by rw [hval]; ring
    change V s k - _ ≤ V s j - _
    rw [h0]
    linarith
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, (14.11), p. 423: the stochastic Euler equation.** With partial derivatives `U₁, U₂`
of `U` at every optimum and `F₁, F₂` of `F` at every `(k, h(s, k))`, and `V(s, ·)`
differentiable with derivative `V₁(s, ·)` on `(0, ∞)`:
`U₁(s, k) = βΣ_{s′}P(s, s′)(z(s′)F₁(s′, k′) + 1 − δ)U₁(s′, k′)`, `k′ = g(s, k)`. -/
theorem eq_14_11 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {U1 U2 F1 F2 V1 : S → ℝ → ℝ}
    (hU : ∀ s k, 0 < k →
      rx_HasPartials U (U1 s k) (U2 s k) (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    (hF : ∀ s k, 0 < k → rx_HasPartials F (F1 s k) (F2 s k) (k, h s k))
    (hV : ∀ s k, 0 < k → HasDerivAt (V s) (V1 s k) k) {s : S} {k : ℝ} (hk : 0 < k) :
    U1 s k = β * ∑ s', P s s' * ((z s' * F1 s' (g s k) + 1 - δ) * U1 s' (g s k)) := by
  have hg := (hB s k hk).1.1
  rw [eq_14_9 hB hk (hU s k hk) (fun s' => hV s' (g s k) hg)]
  congr 1
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [eq_14_10 hB hg (hU s' _ hg) (hF s' _ hg) (hV s' _ hg)]

/-- AKMM, p. 423: the printed Bellman equation has no discount factor; its first-order condition
for capital is `U₁ = ΣP V₁` (`eq_14_9` with `β = 1`), and it is compatible with the printed
(14.9) `U₁ = βΣP V₁` only if `β = 1` or `U₁ = 0`. -/
theorem rbc_printed_bellman_beta {β U1 EV : ℝ} (hprinted : U1 = EV) (h149 : U1 = β * EV) :
    β = 1 ∨ U1 = 0 := by
  rcases eq_or_ne U1 0 with h | h
  · exact Or.inr h
  · left
    have hEV : EV ≠ 0 := hprinted ▸ h
    have : β * EV = 1 * EV := by rw [← h149, one_mul, hprinted]
    exact mul_right_cancel₀ hEV this

/-- Non-vacuity of `rbc_Bellman`: with one TFP state, `U(c, x) = c + ln x`, `F(k, ℓ) = k + ℓ`,
`z = 2`, `δ = 1` and `β = 1/2`, the value `V(k) = 2k + 2(1 − ln 2)` with policies `g(k) = k`,
`h = 1/2` solves the Bellman equation. -/
theorem rbc_example_bellman :
    rbc_Bellman (S := Unit) (fun p => p.1 + Real.log p.2) (fun p => p.1 + p.2) (1 / 2) 1
      (fun _ => 2) (fun _ _ => 1) (fun _ k => 2 * k + 2 * (1 - Real.log 2)) (fun _ k => k)
      (fun _ _ => 1 / 2) := by
  intro s k hk
  simp only [rbcRes, Finset.univ_unique, Finset.sum_singleton, one_mul, sub_self, zero_mul,
    add_zero]
  have hl2 : Real.log (1 - 1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  refine ⟨⟨hk, by norm_num, by norm_num, by linarith⟩, by rw [hl2]; ring, ?_⟩
  intro k' ℓ' _ _ hℓ1 _
  have ht := rb_log_tangent (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < 1 - ℓ')
  rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at ht
  linarith

/-- AKMM, p. 428: the calibrated utility `(1 − φ)ln c + φ ln(1 − ℓ)` is `(1 − φ)` times Miao's
`rb_u χ = ln c + χ ln(1 − ℓ)` with `χ = φ/(1 − φ)`; so it ranks allocations as `rb_u χ` does,
and Miao's welfare theorems `rb_sce_iff`, `rb_sce_optimal` apply to the calibrated model. -/
theorem rbc_calib_utility {φ c ℓ : ℝ} (hφ : φ < 1) :
    (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) = (1 - φ) * rb_u (φ / (1 - φ)) c ℓ ∧
      ∀ c' ℓ', ((1 - φ) * Real.log c' + φ * Real.log (1 - ℓ') ≤
        (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) ↔
        rb_u (φ / (1 - φ)) c' ℓ' ≤ rb_u (φ / (1 - φ)) c ℓ) := by
  have h1 : 0 < 1 - φ := by linarith
  have e : ∀ c ℓ, (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) =
      (1 - φ) * rb_u (φ / (1 - φ)) c ℓ := fun c ℓ => by
    unfold rb_u; field_simp
  refine ⟨e c ℓ, fun c' ℓ' => ?_⟩
  rw [e, e]
  exact mul_le_mul_iff_of_pos_left h1

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Impulse responses from linear policy functions

AKMM, §14.4.2, p. 424. Linearised around the steady state (all variables in deviations), the
policies are `y = G(k, z) = G_k k + G_z z` and `k′ = H(k, z) = H_k k + H_z z`, and
`zₜ = ρzₜ₋₁`. The impulse response to a TFP shock `ε` at the steady state is
`k₀ = 0`, `z_s = ρˢε`, `k_{s+1} = H(k_s, z_s)` (`irfK`), `y_s = G(k_s, z_s)` (`irfY`).

* The sequence `y₀ = G(k_ss, z₀)`, `y₁ = G(H(k_ss, z₀), z₁)`, `y₂ = G(H(H(k_ss, z₀), z₁), z₂)`
  (`irf_first_terms`; the book labels the third term `y₁` again).
* "The composition of linear functions is linear": the response is linear in the shock, so
  `y_s/ε` does not depend on `ε` (`irf_linear`); closed form
  `k_s = H_zεΣ_{j<s}H_kˢ⁻¹⁻ʲρʲ` (`irf_closed`).
* Geometric decay: with `m ≥ |H_k|, |ρ|`, `|k_{s+1}| ≤ |H_z||ε|(s + 1)mˢ` (`irf_bound`), so for
  `|H_k| < 1` and `|ρ| < 1` the responses of capital, TFP and output vanish (`irf_decay`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology

/-- The capital response `k₀ = 0`, `k_{s+1} = H_k k_s + H_z ρˢε`. -/
def irfK (Hk Hz ρ ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => Hk * irfK Hk Hz ρ ε s + Hz * (ρ ^ s * ε)

/-- The output response `y_s = G_k k_s + G_z ρˢε`. -/
def irfY (Gk Gz Hk Hz ρ ε : ℝ) (s : ℕ) : ℝ := Gk * irfK Hk Hz ρ ε s + Gz * (ρ ^ s * ε)

/-- **AKMM, p. 424: the impulse-response sequence.** With `G(k, z) = G_k k + G_z z`,
`H(k, z) = H_k k + H_z z`, `k_ss = 0` (deviations) and `z_s = ρˢz₀`, `z₀ = ε`:
`y₀ = G(0, z₀)`, `y₁ = G(H(0, z₀), z₁)` and `y₂ = G(H(H(0, z₀), z₁), z₂)`. -/
theorem irf_first_terms (Gk Gz Hk Hz ρ ε : ℝ) :
    let G := fun k z => Gk * k + Gz * z
    let H := fun k z => Hk * k + Hz * z
    irfY Gk Gz Hk Hz ρ ε 0 = G 0 ε ∧ irfY Gk Gz Hk Hz ρ ε 1 = G (H 0 ε) (ρ * ε) ∧
      irfY Gk Gz Hk Hz ρ ε 2 = G (H (H 0 ε) (ρ * ε)) (ρ ^ 2 * ε) := by
  simp only [irfY, irfK]
  refine ⟨by ring, by ring, by ring⟩

/-- The response is linear in the shock: `k_s(ε) = εk_s(1)`. -/
theorem irf_K_linear (Hk Hz ρ ε : ℝ) (s : ℕ) : irfK Hk Hz ρ ε s = ε * irfK Hk Hz ρ 1 s := by
  induction s with
  | zero => simp [irfK]
  | succ s ih => simp only [irfK]; rw [ih]; ring

/-- AKMM, p. 424: "since the composition of linear functions is linear", the impulse response
per unit of shock `y_s/ε` is independent of the size of the shock: `y_s(ε) = εy_s(1)`. -/
theorem irf_linear (Gk Gz Hk Hz ρ ε : ℝ) (s : ℕ) :
    irfY Gk Gz Hk Hz ρ ε s = ε * irfY Gk Gz Hk Hz ρ 1 s := by
  simp only [irfY]
  rw [irf_K_linear Hk Hz ρ ε s]
  ring

/-- Closed form: `k_s = H_zεΣ_{j<s}H_k^{s−1−j}ρʲ`. -/
theorem irf_closed (Hk Hz ρ ε : ℝ) (s : ℕ) :
    irfK Hk Hz ρ ε s = Hz * ε * ∑ j ∈ Finset.range s, Hk ^ (s - 1 - j) * ρ ^ j := by
  induction s with
  | zero => simp [irfK]
  | succ s ih =>
    simp only [irfK]
    rw [ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have : ∀ j ∈ Finset.range s, Hk * (Hz * ε * (Hk ^ (s - 1 - j) * ρ ^ j)) =
        Hz * ε * (Hk ^ (s - j) * ρ ^ j) := fun j hj => by
      have hj' : j < s := Finset.mem_range.1 hj
      rw [show s - j = (s - 1 - j) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- The geometric bound `|k_{s+1}| ≤ |H_z||ε|(s + 1)mˢ` for `|H_k| ≤ m` and `|ρ| ≤ m`. -/
theorem irf_bound {Hk Hz ρ ε m : ℝ} (hk : |Hk| ≤ m) (hr : |ρ| ≤ m) (s : ℕ) :
    |irfK Hk Hz ρ ε (s + 1)| ≤ |Hz| * |ε| * ((s + 1) * m ^ s) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hk
  have hz : ∀ j : ℕ, |ρ ^ j * ε| ≤ m ^ j * |ε| := fun j => by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hr j) (abs_nonneg _)
  induction s with
  | zero => simp [irfK, abs_mul]
  | succ s ih =>
    simp only [irfK] at ih ⊢
    calc |Hk * irfK Hk Hz ρ ε (s + 1) + Hz * (ρ ^ (s + 1) * ε)|
        ≤ |Hk| * |irfK Hk Hz ρ ε (s + 1)| + |Hz| * |ρ ^ (s + 1) * ε| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ m * (|Hz| * |ε| * ((s + 1) * m ^ s)) + |Hz| * (m ^ (s + 1) * |ε|) := by
          gcongr
          · simpa [irfK] using ih
          · exact hz (s + 1)
      _ = |Hz| * |ε| * ((↑(s + 1) + 1) * m ^ (s + 1)) := by push_cast; ring

/-- **AKMM, p. 424: the impulse responses die out geometrically.** If `|H_k| < 1` and `|ρ| < 1`,
the responses of capital, TFP and output tend to zero. -/
theorem irf_decay {Gk Gz Hk Hz ρ ε : ℝ} (hk : |Hk| < 1) (hr : |ρ| < 1) :
    Tendsto (irfK Hk Hz ρ ε) atTop (𝓝 0) ∧ Tendsto (fun s : ℕ => ρ ^ s * ε) atTop (𝓝 0) ∧
      Tendsto (irfY Gk Gz Hk Hz ρ ε) atTop (𝓝 0) := by
  set m := max |Hk| |ρ|
  have hm0 : 0 ≤ m := le_max_of_le_left (abs_nonneg _)
  have hm1 : m < 1 := max_lt hk hr
  have hz : Tendsto (fun s : ℕ => ρ ^ s * ε) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).mul_const ε
  have hb : Tendsto (fun s : ℕ => |Hz| * |ε| * ((s + 1 : ℝ) * m ^ s)) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hm0 hm1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hm0 hm1
    have := (h1.add h2).const_mul (|Hz| * |ε|)
    simp only [add_zero, mul_zero] at this
    refine this.congr fun s => ?_
    ring
  have hK1 : Tendsto (fun s => irfK Hk Hz ρ ε (s + 1)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun s => irf_bound (le_max_left _ _) (le_max_right _ _) s) hb
  have hK : Tendsto (irfK Hk Hz ρ ε) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).1 hK1
  refine ⟨hK, hz, ?_⟩
  have := (hK.const_mul Gk).add (hz.const_mul Gz)
  simp only [mul_zero, add_zero] at this
  exact this

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Calibration of the core RBC model

AKMM, §14.4.3–14.4.4, pp. 425–428.

* The Solow residual `log zₜ = log yₜ − α log kₜ − (1 − α) log ℓₜ` for `y = zk^αℓ^{1−α}`
  (`cal_solow_residual`).
* Perpetual inventory: `kₜ = (1 − δ)kₜ₋₁ + iₜ` gives `kₜ = (1 − δ)ᵗk₀ + Σ(1 − δ)^{t−1−s}i_{s+1}`
  (`cal_perpetual_inventory`); the effect of the initial guess decays as `(1 − δ)ᵗ`
  (`cal_perpetual_guess`).
* The quarterly `β = 0.99` is an annual discount rate of about 4%: `(1/0.99)⁴ − 1 ∈ (0.040, 0.042)`
  (`cal_discount_rate`).
* **The calibration identity** (p. 428): with `u = (1 − φ)ln c + φ ln(1 − ℓ)` and
  `y = zk^αℓ^{1−α}`, (14.8) `zF₂ = U₂/U₁` is equivalent to
  `φ/(1 − φ)·ℓ/(1 − ℓ) = (1 − α)y/c` (`cal_phi_identity`, with the marginal product of labour
  `zF₂ = (1 − α)y/ℓ`, `cal_mpl`).
* The steady state: the Euler equation gives `k/y = αβ/(1 − β(1 − δ))` and `c/y = 1 − δk/y`
  (`cal_steady_ratios`); at `ℓ = 1/3`, `φ = X/(1 + X)` with `X = 2(1 − α)y/c`
  (`cal_phi_formula`).
* **Numeric certificate** (p. 428, "`φ = 0.6325`"): at `α = 0.36`, `β = 0.99`, `δ = 0.025`,
  `0.63245 < φ < 0.63255` (`cal_phi_value`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology

/-- AKMM, p. 426: the Solow residual. If `y = zk^αℓ^{1−α}` with `z, k, ℓ > 0`, then
`log z = log y − α log k − (1 − α) log ℓ`. -/
theorem cal_solow_residual {α z k ℓ y : ℝ} (hz : 0 < z) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hy : y = z * k ^ α * ℓ ^ (1 - α)) :
    Real.log z = Real.log y - α * Real.log k - (1 - α) * Real.log ℓ := by
  rw [hy, Real.log_mul (by positivity) (by positivity), Real.log_mul hz.ne' (by positivity),
    Real.log_rpow hk, Real.log_rpow hℓ]
  ring

/-- AKMM, p. 426: the perpetual-inventory method. If `kₜ₊₁ = (1 − δ)kₜ + iₜ₊₁`, then
`kₜ = (1 − δ)ᵗk₀ + Σ_{s<t}(1 − δ)^{t−1−s}i_{s+1}`. -/
theorem cal_perpetual_inventory {δ : ℝ} {k i : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + i (t + 1)) (t : ℕ) :
    k t = (1 - δ) ^ t * k 0 + ∑ s ∈ Finset.range t, (1 - δ) ^ (t - 1 - s) * i (s + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hk, ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum]
    have : ∀ s ∈ Finset.range t, (1 - δ) * ((1 - δ) ^ (t - 1 - s) * i (s + 1)) =
        (1 - δ) ^ (t - s) * i (s + 1) := fun s hs => by
      have := Finset.mem_range.1 hs
      rw [show t - s = (t - 1 - s) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- AKMM, p. 426: with `0 < δ ≤ 1`, two capital series built by perpetual inventory from the same
investment data but different initial guesses differ by `(1 − δ)ᵗ(k₀ − k₀′) → 0`. -/
theorem cal_perpetual_guess {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {k k' i : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + i (t + 1))
    (hk' : ∀ t, k' (t + 1) = (1 - δ) * k' t + i (t + 1)) :
    (∀ t, k t - k' t = (1 - δ) ^ t * (k 0 - k' 0)) ∧
      Tendsto (fun t => k t - k' t) atTop (𝓝 0) := by
  have e : ∀ t, k t - k' t = (1 - δ) ^ t * (k 0 - k' 0) := fun t => by
    rw [cal_perpetual_inventory hk t, cal_perpetual_inventory hk' t]
    ring
  refine ⟨e, ?_⟩
  rw [show (fun t => k t - k' t) = fun t => (1 - δ) ^ t * (k 0 - k' 0) from funext e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const
    (k 0 - k' 0)

/-- AKMM, p. 428: "`β = 0.99`, representing an annual 4% discount rate":
`0.040 < (1/0.99)⁴ − 1 < 0.042`. -/
theorem cal_discount_rate : (0.040 : ℝ) < (1 / 0.99) ^ 4 - 1 ∧ (1 / 0.99 : ℝ) ^ 4 - 1 < 0.042 := by
  constructor <;> norm_num

/-- The marginal product of labour of `y = zk^αℓ^{1−α}`: `zF₂ = (1 − α)y/ℓ`. -/
theorem cal_mpl {α z k ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasDerivAt (fun x => z * k ^ α * x ^ (1 - α)) ((1 - α) * (z * k ^ α * ℓ ^ (1 - α)) / ℓ) ℓ := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hℓ.ne')).const_mul (z * k ^ α)
  convert this using 1
  rw [Real.rpow_sub_one hℓ.ne']
  ring

/-- **AKMM, p. 428: the calibration identity.** With `U₁ = (1 − φ)/c`, `U₂ = φ/(1 − ℓ)` and
`zF₂ = (1 − α)y/ℓ`, (14.8) holds iff `φ/(1 − φ)·ℓ/(1 − ℓ) = (1 − α)y/c`. -/
theorem cal_phi_identity {α φ c ℓ y : ℝ} (hφ1 : φ < 1) (hc : 0 < c) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (1 - α) * y / ℓ = (φ / (1 - ℓ)) / ((1 - φ) / c) ↔
      φ / (1 - φ) * (ℓ / (1 - ℓ)) = (1 - α) * (y / c) := by
  have h1 : 0 < 1 - φ := by linarith
  have h2 : 0 < 1 - ℓ := by linarith
  have e1 : (φ / (1 - ℓ)) / ((1 - φ) / c) = φ * c / ((1 - ℓ) * (1 - φ)) := by
    field_simp
  have e2 : φ / (1 - φ) * (ℓ / (1 - ℓ)) = φ * ℓ / ((1 - φ) * (1 - ℓ)) := by
    field_simp
  have e3 : (1 - α) * (y / c) = (1 - α) * y / c := by ring
  rw [e1, e2, e3, div_eq_div_iff hℓ0.ne' (by positivity),
    div_eq_div_iff (by positivity) hc.ne']
  constructor <;> intro h <;> linarith

/-- AKMM, p. 428: the steady state of the calibrated model. With `c` constant the Euler equation
`1 = β(αy/k + 1 − δ)` holds iff `k/y = αβ/(1 − β(1 − δ))`; the resource constraint
`c + δk = y` gives `c/y = 1 − δk/y`. -/
theorem cal_steady_ratios {α β δ k y c : ℝ} (hk : 0 < k) (hy : 0 < y)
    (hb : β * (1 - δ) ≠ 1) :
    (1 = β * (α * y / k + 1 - δ) ↔ k / y = α * β / (1 - β * (1 - δ))) ∧
      (c + δ * k = y → c / y = 1 - δ * (k / y)) := by
  have hb' : 1 - β * (1 - δ) ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · rw [div_eq_div_iff hy.ne' hb']
    field_simp at h
    linarith
  · rw [div_eq_div_iff hy.ne' hb'] at h
    field_simp
    linarith
  · have hne : c + δ * k ≠ 0 := by rw [h]; exact hy.ne'
    rw [← h]
    field_simp
    ring

/-- AKMM, p. 428: at the target `ℓ = 1/3`, the identity gives `φ/(1 − φ) = X` with
`X = 2(1 − α)y/c`, i.e. `φ = X/(1 + X)`. -/
theorem cal_phi_formula {α φ y c : ℝ} (hφ1 : φ < 1) (hα : α < 1) (hyc : 0 < y / c) :
    φ / (1 - φ) * ((1 / 3) / (1 - 1 / 3)) = (1 - α) * (y / c) ↔
      φ = 2 * (1 - α) * (y / c) / (1 + 2 * (1 - α) * (y / c)) := by
  have h1 : 0 < 1 - φ := by linarith
  have hX : 0 < 1 + 2 * (1 - α) * (y / c) := by
    have : 0 < (1 - α) * (y / c) := mul_pos (by linarith) hyc
    linarith
  set q := y / c
  have e : φ / (1 - φ) * ((1 / 3) / (1 - 1 / 3)) = φ / (2 * (1 - φ)) := by
    field_simp; ring
  rw [eq_div_iff hX.ne', e, div_eq_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- The calibrated capital–output ratio `k/y = αβ/(1 − β(1 − δ))` at `α = 0.36`, `β = 0.99`,
`δ = 0.025`. -/
noncomputable def calKY : ℝ := 0.36 * 0.99 / (1 - 0.99 * (1 - 0.025))

/-- The calibrated `φ = X/(1 + X)`, `X = 2(1 − α)y/c`, `c/y = 1 − δk/y`. -/
noncomputable def calPhi : ℝ :=
  2 * (1 - 0.36) * (1 / (1 - 0.025 * calKY)) / (1 + 2 * (1 - 0.36) * (1 / (1 - 0.025 * calKY)))

/-- **AKMM, p. 428: "we can then solve for `φ = 0.6325`"** (numeric certificate):
`0.63245 < φ < 0.63255` at `α = 0.36`, `β = 0.99`, `δ = 0.025`, `ℓ = 1/3`. -/
theorem cal_phi_value : (0.63245 : ℝ) < calPhi ∧ calPhi < 0.63255 := by
  unfold calPhi calKY
  constructor <;> norm_num

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Balanced-growth preferences and extensions of the RBC model

AKMM, §14.4.4, p. 427, and §14.5, pp. 432–434.

* **KPR preferences** `(c v(1 − ℓ))^{1−σ}/(1 − σ)` are AKMM Chapter 12's `kprU σ (v^{1−σ})`
  (`ext_kpr_form`), so the marginal rate of substitution is homogeneous of degree one in `c`
  (`ext_kpr_homog`, from Chapter 12's `kpr_homog`) and balanced growth with constant hours holds
  (Chapter 12's `eq_12_37_if`). With `σ = 1` and the Cobb–Douglas aggregator,
  `ln(c^{1−φ}(1 − ℓ)^φ) = (1 − φ)ln c + φ ln(1 − ℓ)` (`ext_cd_log`).
* The steady-state interest rate is `R = g^σ/β` (`ext_bgp_interest`), not `gσ/β`
  (`ext_interest_printed_false`).
* **Adjustment costs** (§14.5.2): `Ψ(i, k) = (ψ/2)(i/k − δ)²k` (`adjPsi`) is homogeneous of degree
  one (`adj_homog`; Miao's form for `Φ(i, k) = i − Ψ(i, k)`, `adj_Phi_homog`), zero at
  maintenance investment `i = δk` and nonnegative (`adj_maintenance`), convex in `i`
  (`adj_convex_i`) and jointly convex for `k > 0` (`adj_jointly_convex`).
  The accumulation `k′ = (1 − δ)k + i − Ψ(i, k)` has `∂k′/∂i = 1 − ψ(i/k − δ)` (`adj_dk_di`),
  so the shadow price of installed capital is exactly `q = 1/(1 − ψ(i/k − δ))`
  (`adj_shadow_price`); the printed `1 + ψ(i/k − δ)` agrees only at `i = δk` (`adj_q_printed_iff`,
  counterexample `adj_q_printed_false`) and is its first-order approximation, the error being
  `ψ²x²/(1 − ψx)` (`adj_q_first_order`); it is exact when the cost is paid out of output
  (`adj_shadow_price_resource`). Marginal `q` equals average `q` (Hayashi) by Miao's
  `proposition_14_3_1`, applied to this `Φ` (`adj_hayashi`).
* **Utilisation** (§14.5.3): with `y = z(uk)^αℓ^{1−α}`, the Solow residual computed with
  measured capital is `log z + α log u` (`ext_util_solow`); utilisation amplifies TFP shocks
  (Miao's `rx_cu_amplification`).
* **Investment-specific shocks** (§14.5.4): with `k′ = (1 − δ)k + qi`, the planner's shadow price
  of capital in consumption units is `1/q` (`ext_ist_price`; Miao's `rx_ist_price`: it falls when
  `q` rises).
* **Government spending** (§14.5.4): in the static economy `c = zℓ − g` with log–log utility,
  hours are `ℓ = (z + φg)/((1 + φ)z)` and rise with `g` (the negative income effect,
  `ext_gov_hours`, `ext_gov_hours_increasing`); if `g` is a perfect substitute for `c`
  (`C = c + g`), hours are `1/(1 + φ)` whatever `g` (`ext_gov_perfect_subst`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

/-! ### KPR preferences -/

/-- AKMM, p. 427: for `σ ≠ 1`, `c > 0`, `v > 0`, the KPR utility `(c v(x))^{1−σ}/(1 − σ)` is AKMM
Chapter 12's `kprU σ (v^{1−σ}) c x`. -/
theorem ext_kpr_form {σ c : ℝ} {v : ℝ → ℝ} (hσ : σ ≠ 1) (hc : 0 < c) {x : ℝ} (hv : 0 < v x) :
    (c * v x) ^ (1 - σ) / (1 - σ) = AKMM.LaborSupply.kprU σ (fun y => v y ^ (1 - σ)) c x := by
  simp only [AKMM.LaborSupply.kprU, hσ, ↓reduceIte, Real.mul_rpow hc.le hv.le]

/-- AKMM, p. 427, balanced growth: for KPR utility the marginal rate of substitution
`U_x/U_c` is homogeneous of degree one in consumption, `MRS(gc) = g·MRS(c)` (`g, c > 0`), so
consumption and the wage can grow at the same rate with constant hours. -/
theorem ext_kpr_homog {σ g c x : ℝ} {v v' : ℝ → ℝ} (hg : 0 < g) (hc : 0 < c) :
    AKMM.LaborSupply.kprUl σ v' (g * c) x / AKMM.LaborSupply.kprUC σ v (g * c) x =
      g * (AKMM.LaborSupply.kprUl σ v' c x / AKMM.LaborSupply.kprUC σ v c x) := by
  obtain ⟨h1, h2⟩ := AKMM.LaborSupply.kpr_homog (σ := σ) (v := v) (v' := v') (l := x) hg hc
  rw [h1, h2]
  have hp : 0 < g ^ (-σ) := Real.rpow_pos_of_pos hg _
  have e : g ^ (1 - σ) = g * g ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hg, Real.rpow_one]
  rw [e]
  by_cases h0 : AKMM.LaborSupply.kprUC σ v c x = 0
  · simp [h0]
  · field_simp

/-- AKMM, p. 427: with `σ = 1` and the Cobb–Douglas aggregator,
`ln(c^{1−φ}(1 − ℓ)^φ) = (1 − φ)ln c + φ ln(1 − ℓ)`. -/
theorem ext_cd_log {φ c ℓ : ℝ} (hc : 0 < c) (hℓ : ℓ < 1) :
    Real.log (c ^ (1 - φ) * (1 - ℓ) ^ φ) = (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) := by
  have h1 : 0 < 1 - ℓ := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hc, Real.log_rpow h1]

/-- **AKMM, p. 427, the steady-state interest rate, corrected.** If marginal utility has the
KPR form `c^{−σ}w` (`w > 0` the constant leisure factor) and consumption grows at the gross rate
`g > 0`, the Euler equation `c^{−σ}w = βR(gc)^{−σ}w` holds iff `R = g^σ/β`. -/
theorem ext_bgp_interest {σ β g c w R : ℝ} (hβ : 0 < β) (hg : 0 < g) (hc : 0 < c) (hw : 0 < w) :
    c ^ (-σ) * w = β * R * ((g * c) ^ (-σ) * w) ↔ R = g ^ σ / β := by
  have hcs : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have hgs : 0 < g ^ σ := Real.rpow_pos_of_pos hg _
  have e : (g * c) ^ (-σ) = c ^ (-σ) / g ^ σ := by
    rw [Real.mul_rpow hg.le hc.le, Real.rpow_neg hg.le]
    field_simp
  rw [e]
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith
  · intro h
    rw [h]
    field_simp

/-- AKMM, p. 427: the printed "growth rate of consumption times `σ` divided by `β`" is not the
steady-state interest rate: at `g = 1.02`, `σ = 2`, `β = 0.99`, `g^σ/β ≠ gσ/β`. -/
theorem ext_interest_printed_false : (1.02 : ℝ) ^ (2 : ℝ) / 0.99 ≠ 1.02 * 2 / 0.99 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-! ### Capital adjustment costs -/

/-- AKMM, p. 433: the adjustment cost `Ψ(i, k) = (ψ/2)(i/k − δ)²k`. -/
noncomputable def adjPsi (ψ δ i k : ℝ) : ℝ := ψ / 2 * (i / k - δ) ^ 2 * k

/-- AKMM, p. 433, footnote 15: `Ψ` is homogeneous of degree one in `(i, k)`. -/
theorem adj_homog (ψ δ : ℝ) {l : ℝ} (hl : 0 < l) (i k : ℝ) :
    adjPsi ψ δ (l * i) (l * k) = l * adjPsi ψ δ i k := by
  unfold adjPsi
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · rw [mul_div_mul_left _ _ hl.ne']
    ring

/-- The net investment function `Φ(i, k) = i − Ψ(i, k)` of `k′ = (1 − δ)k + Φ(i, k)` is
homogeneous of degree one in Miao's form (the hypothesis of `proposition_14_3_1`). -/
theorem adj_Phi_homog (ψ δ : ℝ) :
    ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l →
      (fun q : ℝ × ℝ => q.1 - adjPsi ψ δ q.1 q.2) (l * p.1, l * p.2) =
        l * (fun q : ℝ × ℝ => q.1 - adjPsi ψ δ q.1 q.2) p := by
  intro l p hl
  simp only [adj_homog ψ δ hl]
  ring

/-- AKMM, p. 433: replacing depreciated capital is costless, `Ψ(δk, k) = 0`, and `Ψ ≥ 0` for
`ψ ≥ 0`, `k ≥ 0`. -/
theorem adj_maintenance {ψ δ k : ℝ} (hk : k ≠ 0) :
    adjPsi ψ δ (δ * k) k = 0 ∧ ∀ i, 0 ≤ ψ → 0 ≤ k → 0 ≤ adjPsi ψ δ i k := by
  refine ⟨by unfold adjPsi; rw [mul_div_cancel_right₀ _ hk]; ring, fun i hψ hk0 => ?_⟩
  unfold adjPsi
  positivity

/-- AKMM, p. 433: the adjustment cost is convex in investment (`ψ ≥ 0`, `k > 0`). -/
theorem adj_convex_i {ψ δ k : ℝ} (hψ : 0 ≤ ψ) (hk : 0 < k) :
    ConvexOn ℝ Set.univ (fun i => adjPsi ψ δ i k) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [adjPsi, smul_eq_mul]
  have hk' : k ≠ 0 := hk.ne'
  have e : ∀ u : ℝ, ψ / 2 * (u / k - δ) ^ 2 * k = ψ / (2 * k) * (u - δ * k) ^ 2 := fun u => by
    field_simp
  rw [e, e, e]
  have hc : 0 ≤ ψ / (2 * k) := by positivity
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : (a * x + (1 - a) * y - δ * k) ^ 2 ≤
      a * (x - δ * k) ^ 2 + (1 - a) * (y - δ * k) ^ 2 := by
    nlinarith [sq_nonneg (x - y), mul_nonneg ha hb]
  nlinarith [mul_le_mul_of_nonneg_left key hc]

/-- AKMM, p. 433: `Ψ` is jointly convex in `(i, k)` on `k > 0` (`ψ ≥ 0`): it is
`(ψ/2)(i − δk)²/k`, a quadratic-over-linear function. -/
theorem adj_jointly_convex {ψ δ : ℝ} (hψ : 0 ≤ ψ) :
    ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2} (fun p => adjPsi ψ δ p.1 p.2) := by
  have hcv : Convex ℝ {p : ℝ × ℝ | 0 < p.2} := by
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hp hq ⊢
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_mul, zero_add, show b = 1 by linarith, one_mul]; exact hq
    · have := mul_pos h hp; nlinarith [mul_nonneg hb hq.le]
  refine ⟨hcv, fun p hp q hq a b ha hb hab => ?_⟩
  simp only [Set.mem_ofPred_eq] at hp hq
  simp only [adjPsi, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  set x1 := p.1 - δ * p.2
  set x2 := q.1 - δ * q.2
  have e : ∀ u k : ℝ, k ≠ 0 → ψ / 2 * (u / k - δ) ^ 2 * k = ψ / 2 * ((u - δ * k) ^ 2 / k) :=
    fun u k hk => by field_simp
  have hk : 0 < a * p.2 + b * q.2 := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_mul, zero_add, show b = 1 by linarith, one_mul]; exact hq
    · have := mul_pos h hp; nlinarith [mul_nonneg hb hq.le]
  rw [e _ _ hk.ne', e _ _ hp.ne', e _ _ hq.ne']
  have hx : a * p.1 + b * q.1 - δ * (a * p.2 + b * q.2) = a * x1 + b * x2 := by
    simp only [x1, x2]; ring
  rw [hx]
  -- `(a x₁ + b x₂)²/(a k₁ + b k₂) ≤ a x₁²/k₁ + b x₂²/k₂`
  have key : (a * x1 + b * x2) ^ 2 / (a * p.2 + b * q.2) ≤
      a * (x1 ^ 2 / p.2) + b * (x2 ^ 2 / q.2) := by
    rw [div_le_iff₀ hk]
    have e2 : (a * (x1 ^ 2 / p.2) + b * (x2 ^ 2 / q.2)) * (a * p.2 + b * q.2) =
        (a * x1 + b * x2) ^ 2 + a * b * (x1 * q.2 - x2 * p.2) ^ 2 / (p.2 * q.2) := by
      field_simp; ring
    rw [e2]
    have : 0 ≤ a * b * (x1 * q.2 - x2 * p.2) ^ 2 / (p.2 * q.2) := by positivity
    linarith
  have hc : 0 ≤ ψ / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hc]

/-- AKMM, p. 433: in `k′ = (1 − δ)k + i − Ψ(i, k)`, `∂k′/∂i = 1 − ψ(i/k − δ)` (`k ≠ 0`). -/
theorem adj_dk_di {ψ δ i k : ℝ} (hk : k ≠ 0) :
    HasDerivAt (fun j => (1 - δ) * k + j - adjPsi ψ δ j k) (1 - ψ * (i / k - δ)) i := by
  have h1 : HasDerivAt (fun j => j / k - δ) (1 / k) i := by
    simpa using ((hasDerivAt_id i).div_const k).sub_const δ
  have h2 := ((h1.pow 2).const_mul (ψ / 2)).mul_const k
  have h3 := ((hasDerivAt_id i).const_add ((1 - δ) * k)).sub h2
  convert h3 using 1
  · funext j; simp [adjPsi]
  · simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp

/-- **AKMM, p. 433, the shadow price of installed capital, corrected.** If investment `i`
maximises `u(y − j) + W((1 − δ)k + j − Ψ(j, k))` locally, with `u′(c) = u₁ ≠ 0` and
`W′(k′) = w₁`, then `(w₁/u₁)(1 − ψ(i/k − δ)) = 1`: Tobin's `q = w₁/u₁` (the value of a unit of
installed capital in consumption units) is `1/(1 − ψ(i/k − δ))`. -/
theorem adj_shadow_price {ψ δ i k y u1 w1 : ℝ} {u W : ℝ → ℝ} (hk : k ≠ 0)
    (hu : HasDerivAt u u1 (y - i)) (hW : HasDerivAt W w1 ((1 - δ) * k + i - adjPsi ψ δ i k))
    (hmax : IsLocalMax (fun j => u (y - j) + W ((1 - δ) * k + j - adjPsi ψ δ j k)) i)
    (hu1 : u1 ≠ 0) :
    w1 / u1 * (1 - ψ * (i / k - δ)) = 1 ∧
      (1 - ψ * (i / k - δ) ≠ 0 → w1 / u1 = 1 / (1 - ψ * (i / k - δ))) := by
  have hc : HasDerivAt (fun j => y - j) (-1) i := by simpa using (hasDerivAt_id i).const_sub y
  have hd := (hu.comp i hc).add (hW.comp i (adj_dk_di hk))
  have h0 := hmax.hasDerivAt_eq_zero hd
  have e : w1 * (1 - ψ * (i / k - δ)) = u1 := by linarith
  have h1 : w1 / u1 * (1 - ψ * (i / k - δ)) = 1 := by
    rw [div_mul_eq_mul_div, e, div_self hu1]
  exact ⟨h1, fun hne => by rw [eq_div_iff hne, h1]⟩

/-- AKMM, p. 433: the printed `q = 1 + ψ(i/k − δ)` equals the exact `1/(1 − ψ(i/k − δ))` iff
`ψ(i/k − δ) = 0` (when `ψ(i/k − δ) ≠ 1`). -/
theorem adj_q_printed_iff {u : ℝ} (hu : 1 - u ≠ 0) : 1 / (1 - u) = 1 + u ↔ u = 0 := by
  rw [div_eq_iff hu]
  constructor
  · intro h
    have : u ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  · intro h; rw [h]; ring

/-- AKMM, p. 433: counterexample to the printed shadow price: `ψ = 1`, `i/k − δ = 1/2` gives
`1/(1 − ψ(i/k − δ)) = 2` but `1 + ψ(i/k − δ) = 3/2`. -/
theorem adj_q_printed_false : (1 : ℝ) / (1 - 1 * (1 / 2)) ≠ 1 + 1 * (1 / 2) := by norm_num

/-- The printed `1 + u` is the first-order approximation of `1/(1 − u)`:
`1/(1 − u) − (1 + u) = u²/(1 − u)`. -/
theorem adj_q_first_order {u : ℝ} (hu : 1 - u ≠ 0) : 1 / (1 - u) - (1 + u) = u ^ 2 / (1 - u) := by
  field_simp
  ring

/-- The printed `q` is exact when the adjustment cost is paid out of output: if `i` maximises
`u(y − j − Ψ(j, k)) + W((1 − δ)k + j)` locally (`u′ = u₁ ≠ 0`, `W′ = w₁`), then
`w₁/u₁ = 1 + ψ(i/k − δ)`. -/
theorem adj_shadow_price_resource {ψ δ i k y u1 w1 : ℝ} {u W : ℝ → ℝ} (hk : k ≠ 0)
    (hu : HasDerivAt u u1 (y - i - adjPsi ψ δ i k)) (hW : HasDerivAt W w1 ((1 - δ) * k + i))
    (hmax : IsLocalMax (fun j => u (y - j - adjPsi ψ δ j k) + W ((1 - δ) * k + j)) i)
    (hu1 : u1 ≠ 0) : w1 / u1 = 1 + ψ * (i / k - δ) := by
  have hdk := adj_dk_di (ψ := ψ) (δ := δ) (i := i) hk
  have hpsi : HasDerivAt (fun j => adjPsi ψ δ j k) (ψ * (i / k - δ)) i := by
    have := (((hasDerivAt_id i).const_add ((1 - δ) * k)).sub hdk)
    convert this using 1
    · funext j; simp
    · ring
  have hy : HasDerivAt (fun j => y - j) (-1) i := by simpa using (hasDerivAt_id i).const_sub y
  have hc : HasDerivAt (fun j => y - j - adjPsi ψ δ j k) (-1 - ψ * (i / k - δ)) i :=
    hy.sub hpsi
  have hl : HasDerivAt (fun j => (1 - δ) * k + j) 1 i := by
    simpa using (hasDerivAt_id i).const_add ((1 - δ) * k)
  have hd := (hu.comp i hc).add (hW.comp i hl)
  have h0 := hmax.hasDerivAt_eq_zero hd
  rw [div_eq_iff hu1]
  linarith

/-- **Hayashi's theorem for the AKMM adjustment cost** (AKMM, p. 433; Miao's
`proposition_14_3_1`): with `Φ(i, k) = i − Ψ(i, k)` (homogeneous of degree one, `adj_Phi_homog`)
and a linearly homogeneous production function, marginal `q` equals average `q`. -/
theorem adj_hayashi {S : Type*} [Fintype S] (T : RXTree S) {F : ℝ × ℝ → ℝ} {ψ δ β : ℝ}
    {Kn I N z w Λ Q a b FK FN P : List S → ℝ}
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p)
    (hΦd : ∀ h s, rx_HasPartials (fun q : ℝ × ℝ => q.1 - adjPsi ψ δ q.1 q.2) (a (s :: h))
      (b (s :: h)) (I (s :: h), Kn h))
    (hFd : ∀ h s, rx_HasPartials F (FK (s :: h)) (FN (s :: h)) (Kn h, N (s :: h)))
    (hacc : ∀ h s, Kn (s :: h) = (1 - δ) * Kn h + (I (s :: h) - adjPsi ψ δ (I (s :: h)) (Kn h)))
    (h48 : ∀ h s, Q (s :: h) * a (s :: h) = 1)
    (hw : ∀ h s, w (s :: h) = z (s :: h) * FN (s :: h))
    (h49 : ∀ h, Λ h * Q h = β * rx_E T (fun g => Λ g * (z g * FK g + Q g * (1 - δ + b g))) h)
    (hΛ : ∀ h, 0 < Λ h) (h : List S)
    (hP : Tendsto (fun n => ∑ j ∈ Finset.range n,
      rx_pv T (rx_sdf β Λ) (j + 1) (rx_div F z w N I Kn) h) atTop (𝓝 (P h)))
    (htvc : Tendsto (fun n => rx_pv T (rx_sdf β Λ) n (fun g => Q g * Kn g) h) atTop (𝓝 0)) :
    Q h * Kn h = P h ∧ (0 < Kn h → Q h = P h / Kn h) :=
  proposition_14_3_1 T (adj_Phi_homog ψ δ) hFhom hΦd hFd hacc h48 hw h49 hΛ h hP htvc

/-! ### Utilisation, investment-specific shocks, government spending -/

/-- AKMM, pp. 426–427 and 433: with variable utilisation, `y = z(uk)^αℓ^{1−α}`, the Solow residual
computed with measured capital `k` is `log y − α log k − (1 − α) log ℓ = log z + α log u`: it
mismeasures TFP by `α log u`. -/
theorem ext_util_solow {α z u k ℓ : ℝ} (hz : 0 < z) (hu : 0 < u) (hk : 0 < k) (hℓ : 0 < ℓ) :
    Real.log (z * (u * k) ^ α * ℓ ^ (1 - α)) - α * Real.log k - (1 - α) * Real.log ℓ =
      Real.log z + α * Real.log u := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hz.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow hℓ, Real.log_mul hu.ne' hk.ne']
  ring

/-- AKMM, p. 434: with investment-specific technology `k′ = (1 − δ)k + qi` (`q ≠ 0`), if `i`
maximises `u(y − j) + W((1 − δ)k + qj)` locally with `u′ = u₁ ≠ 0`, `W′ = w₁`, the shadow price
of capital in consumption units is `w₁/u₁ = 1/q`. -/
theorem ext_ist_price {δ k q y i u1 w1 : ℝ} {u W : ℝ → ℝ} (hq : q ≠ 0)
    (hu : HasDerivAt u u1 (y - i)) (hW : HasDerivAt W w1 ((1 - δ) * k + q * i))
    (hmax : IsLocalMax (fun j => u (y - j) + W ((1 - δ) * k + q * j)) i) (hu1 : u1 ≠ 0) :
    w1 / u1 = 1 / q := by
  have hc : HasDerivAt (fun j => y - j) (-1) i := by simpa using (hasDerivAt_id i).const_sub y
  have hl : HasDerivAt (fun j => (1 - δ) * k + q * j) q i := by
    simpa using ((hasDerivAt_id i).const_mul q).const_add ((1 - δ) * k)
  have h0 := hmax.hasDerivAt_eq_zero ((hu.comp i hc).add (hW.comp i hl))
  rw [div_eq_div_iff hu1 hq]
  linarith

/-- AKMM, p. 434: government spending financed out of output, `c = zℓ − g`, with log–log
utility: the intratemporal condition `z/c = φ/(1 − ℓ)` holds iff `ℓ = (z + φg)/((1 + φ)z)`
(`z > 0`, `c > 0`, `ℓ < 1`). -/
theorem ext_gov_hours {φ z g ℓ : ℝ} (hφ : 0 ≤ φ) (hz : 0 < z) (hc : 0 < z * ℓ - g) (hℓ : ℓ < 1) :
    z / (z * ℓ - g) = φ / (1 - ℓ) ↔ ℓ = (z + φ * g) / ((1 + φ) * z) := by
  have h1 : 0 < 1 - ℓ := by linarith
  have h2 : 0 < (1 + φ) * z := by positivity
  rw [div_eq_div_iff hc.ne' h1.ne', eq_div_iff h2.ne']
  constructor <;> intro h <;> linarith

/-- AKMM, p. 434: "if this elasticity is low, government spending is more like a tax … increasing
labor supply due to a negative income effect": hours `(z + φg)/((1 + φ)z)` strictly increase in
`g` (`φ > 0`). -/
theorem ext_gov_hours_increasing {φ z : ℝ} (hφ : 0 < φ) (hz : 0 < z) :
    StrictMono (fun g => (z + φ * g) / ((1 + φ) * z)) := by
  intro g g' hg
  have h2 : 0 < (1 + φ) * z := by positivity
  exact div_lt_div_of_pos_right (by nlinarith) h2

/-- AKMM, p. 434: "if the elasticity is very high, government spending is like private
consumption": if utility depends on `C = c + g` (perfect substitutes; the CES aggregate with
`ϕ = 1`, `θ = 1/2`, up to scale) and `c = zℓ − g`, then `C = zℓ` and the condition
`z/C = φ/(1 − ℓ)` gives `ℓ = 1/(1 + φ)`, whatever `g`. -/
theorem ext_gov_perfect_subst {φ z g ℓ : ℝ} (hφ : 0 ≤ φ) (hz : 0 < z) (hℓ0 : 0 < ℓ)
    (hℓ1 : ℓ < 1) :
    (z * ℓ - g) + g = z * ℓ ∧
      (z / ((z * ℓ - g) + g) = φ / (1 - ℓ) ↔ ℓ = 1 / (1 + φ)) := by
  have h1 : 0 < 1 - ℓ := by linarith
  refine ⟨by ring, ?_⟩
  rw [sub_add_cancel, div_eq_div_iff (by positivity) h1.ne', eq_div_iff (by positivity)]
  constructor
  · intro h
    have : z * (1 - ℓ) = z * (φ * ℓ) := by linarith
    have := mul_left_cancel₀ hz.ne' this
    linarith
  · intro h
    nlinarith

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Business-cycle accounting

AKMM, §14.6, pp. 434–437 (Chari, Kehoe and McGrattan, 2007). The prototype economy has an
efficiency wedge `z` (`Y = zF(k, ℓ)`), a labour wedge `1 − τ^ℓ`, an investment wedge
`1/(1 + τ^i)` and a government-consumption wedge `g`.

* **The household's first-order conditions** with a labour-income tax `τ^ℓ` and an investment
  price `1 + τ^i`: `(1 − τ^ℓ)wU₁ = U₂` (`bca_labour_foc`, giving the modified (14.8) with
  `w = zF₂`) and the investment-wedge Euler equation
  `U₁(1 + τ^i) = βE[(r′ + (1 − δ)(1 + τ^i′))U₁′]` (`bca_investment_euler`, with `r′ = z′F₁′`).
* **Backing out the wedges**: for any allocation with `F(k, ℓ) > 0`, `F₂ > 0`, `U₁ > 0`, the
  wedges `z = Y/F`, `1 − τ^ℓ = (U₂/U₁)/(zF₂)`, `g = Y − c − i` make the allocation satisfy the
  wedge economy's production function, labour condition and resource constraint, and they are the
  only such wedges (`bca_static_wedges`, `bca_static_unique`).
* For the investment wedge, given `τ^i` today, a successor wedge (constant across next period's
  states) exists and is unique when `δ < 1` (`bca_investment_wedge`).
* With zero wedges (`τ^ℓ = τ^i = 0`, `g = 0`) the wedge conditions are the planner's (14.8) and
  (14.11) (`bca_zero_wedges`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

/-- **AKMM, p. 435, the labour wedge.** If hours `ℓ` maximise `U(c(ℓ′), 1 − ℓ′)` locally with
`c(ℓ′) = (1 − τ^ℓ)wℓ′ + m` and `U` has partials `(U₁, U₂)` at the optimum, then
`(1 − τ^ℓ)wU₁ = U₂`; with `w = zF₂(k, ℓ)` this is the modified (14.8)
`(1 − τ^ℓ)zF₂ = U₂/U₁`. -/
theorem bca_labour_foc {U : ℝ × ℝ → ℝ} {τl w m ℓ U1 U2 : ℝ}
    (hU : rx_HasPartials U U1 U2 ((1 - τl) * w * ℓ + m, 1 - ℓ))
    (hmax : IsLocalMax (fun x => U ((1 - τl) * w * x + m, 1 - x)) ℓ) :
    (1 - τl) * w * U1 = U2 ∧ (U1 ≠ 0 → (1 - τl) * w = U2 / U1) := by
  have hc : HasDerivAt (fun x => (1 - τl) * w * x + m) ((1 - τl) * w) ℓ := by
    simpa using ((hasDerivAt_id ℓ).const_mul ((1 - τl) * w)).add_const m
  have hx : HasDerivAt (fun x : ℝ => 1 - x) (-1) ℓ := by simpa using (hasDerivAt_id ℓ).const_sub 1
  have h0 := hmax.hasDerivAt_eq_zero (hU.comp hc hx)
  refine ⟨by linarith, fun h1 => ?_⟩
  rw [eq_div_iff h1]
  linarith

/-- **AKMM, p. 435, the investment-wedge Euler equation.** A household pays `1 + τ^i` per unit of
investment `i = k′ − (1 − δ)k`. Today `c = m₀ − (1 + τ^i)(k′ − (1 − δ)k)`; in state `s` tomorrow
(probability `pₛ`) `c′ₛ = mₛ + rₛk′ − (1 + τ^i′ₛ)(k″ₛ − (1 − δ)k′)`. If `k′` maximises
`u(c) + βΣₛpₛu(c′ₛ)` locally, with `u′(c) = U₁` and `u′(c′ₛ) = U₁′ₛ`, then
`U₁(1 + τ^i) = βΣₛpₛ(rₛ + (1 − δ)(1 + τ^i′ₛ))U₁′ₛ`. -/
theorem bca_investment_euler {S : Type*} [Fintype S] {u : ℝ → ℝ} {β δ τ m0 k kp U1 : ℝ}
    {p m r τ' k2 U1' : S → ℝ}
    (hu0 : HasDerivAt u U1 (m0 - (1 + τ) * (kp - (1 - δ) * k)))
    (hus : ∀ s, HasDerivAt u (U1' s) (m s + r s * kp - (1 + τ' s) * (k2 s - (1 - δ) * kp)))
    (hmax : IsLocalMax (fun x => u (m0 - (1 + τ) * (x - (1 - δ) * k)) +
      β * ∑ s, p s * u (m s + r s * x - (1 + τ' s) * (k2 s - (1 - δ) * x))) kp) :
    U1 * (1 + τ) = β * ∑ s, p s * ((r s + (1 - δ) * (1 + τ' s)) * U1' s) := by
  have hc0 : HasDerivAt (fun x => m0 - (1 + τ) * (x - (1 - δ) * k)) (-(1 + τ)) kp :=
    ((((hasDerivAt_id' kp).sub_const ((1 - δ) * k)).const_mul (1 + τ)).const_sub m0).congr_deriv
      (by ring)
  have hcs : ∀ s, HasDerivAt (fun x => m s + r s * x - (1 + τ' s) * (k2 s - (1 - δ) * x))
      (r s + (1 - δ) * (1 + τ' s)) kp := fun s =>
    ((((hasDerivAt_id' kp).const_mul (r s)).const_add (m s)).sub
      ((((hasDerivAt_id' kp).const_mul (1 - δ)).const_sub (k2 s)).const_mul (1 + τ' s))).congr_deriv
        (by ring)
  have hsum : HasDerivAt
      (fun x => ∑ s, p s * u (m s + r s * x - (1 + τ' s) * (k2 s - (1 - δ) * x)))
      (∑ s, p s * (U1' s * (r s + (1 - δ) * (1 + τ' s)))) kp :=
    HasDerivAt.fun_sum (u := Finset.univ) fun s _ => ((hus s).comp kp (hcs s)).const_mul (p s)
  have h0 := hmax.hasDerivAt_eq_zero ((hu0.comp kp hc0).add (hsum.const_mul β))
  have e : ∑ s, p s * (U1' s * (r s + (1 - δ) * (1 + τ' s))) =
      ∑ s, p s * ((r s + (1 - δ) * (1 + τ' s)) * U1' s) :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [← e]
  linarith

/-- **AKMM, p. 435, backing out the static wedges.** For any allocation `(c, i, ℓ, k, Y)` with
`F(k, ℓ) > 0`, `F₂ ≠ 0` and `U₁ ≠ 0`, the efficiency wedge `z = Y/F(k, ℓ)`, the labour wedge
`1 − τ^ℓ = (U₂/U₁)/(zF₂)` and the government wedge `g = Y − c − i` satisfy `Y = zF(k, ℓ)`,
`(1 − τ^ℓ)zF₂ = U₂/U₁` and `c + i + g = Y`. -/
theorem bca_static_wedges {c i Y Fkl F2 U1 U2 : ℝ} (hF : 0 < Fkl) (hY : Y ≠ 0) (hF2 : F2 ≠ 0) :
    let z := Y / Fkl
    let τl := 1 - (U2 / U1) / (z * F2)
    let g := Y - c - i
    Y = z * Fkl ∧ (1 - τl) * z * F2 = U2 / U1 ∧ c + i + g = Y := by
  intro z τl g
  have hz : z ≠ 0 := div_ne_zero hY hF.ne'
  refine ⟨by simp only [z]; field_simp, ?_, by simp only [g]; ring⟩
  simp only [τl]
  field_simp
  ring

/-- AKMM, p. 435: the static wedges are determined by the allocation: if `(z, τ^ℓ, g)` make the
allocation satisfy the wedge conditions, they are the backed-out ones. -/
theorem bca_static_unique {c i Y Fkl F2 U1 U2 z τl g : ℝ} (hF : 0 < Fkl) (hz : z ≠ 0)
    (hF2 : F2 ≠ 0) (hprod : Y = z * Fkl) (hlab : (1 - τl) * z * F2 = U2 / U1)
    (hres : c + i + g = Y) :
    z = Y / Fkl ∧ τl = 1 - (U2 / U1) / (z * F2) ∧ g = Y - c - i := by
  refine ⟨by rw [hprod]; field_simp, ?_, by linarith⟩
  rw [← hlab]
  field_simp
  ring

/-- AKMM, p. 435: backing out the investment wedge. Given today's `1 + τ^i`, marginal utility
`U₁`, and next period's states `s` with probabilities `pₛ`, returns `rₛ` and marginal utilities
`U₁′ₛ` with `D = (1 − δ)Σₛ pₛU₁′ₛ ≠ 0`, the constant successor wedge
`1 + τ^i′ = (U₁(1 + τ^i)/β − Σₛ pₛrₛU₁′ₛ)/D` solves the investment-wedge Euler equation, and it
is the only constant successor wedge that does. -/
theorem bca_investment_wedge {S : Type*} [Fintype S] {β δ τ U1 : ℝ} {p r U1' : S → ℝ}
    (hβ : β ≠ 0) (hD : (1 - δ) * ∑ s, p s * U1' s ≠ 0) (x : ℝ) :
    U1 * (1 + τ) = β * ∑ s, p s * ((r s + (1 - δ) * x) * U1' s) ↔
      x = (U1 * (1 + τ) / β - ∑ s, p s * r s * U1' s) / ((1 - δ) * ∑ s, p s * U1' s) := by
  have e : ∑ s, p s * ((r s + (1 - δ) * x) * U1' s) =
      ∑ s, p s * r s * U1' s + x * ((1 - δ) * ∑ s, p s * U1' s) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, eq_div_iff hD]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have : x * ((1 - δ) * ∑ s, p s * U1' s) = U1 * (1 + τ) / β - ∑ s, p s * r s * U1' s := h
    field_simp at this ⊢
    linarith

/-- AKMM, pp. 435–436: with zero wedges the wedge conditions are the planner's: the labour
condition `(1 − 0)zF₂ = U₂/U₁` is (14.8) and the investment condition with `τ^i = τ^i′ = 0` is
(14.11). -/
theorem bca_zero_wedges {S : Type*} [Fintype S] {β δ z F2 U1 U2 : ℝ} {p r U1' : S → ℝ} :
    ((1 - 0) * z * F2 = U2 / U1 ↔ z * F2 = U2 / U1) ∧
      (U1 * (1 + 0) = β * ∑ s, p s * ((r s + (1 - δ) * (1 + 0)) * U1' s) ↔
        U1 = β * ∑ s, p s * ((r s + 1 - δ) * U1' s)) := by
  constructor
  · simp
  · simp only [add_zero, mul_one]
    constructor <;> intro h <;> rw [h] <;> congr 1 <;>
      exact Finset.sum_congr rfl fun s _ => by ring

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gain functions of linear filters

AKMM, Appendix 14.A, pp. 864–865.

* **The first difference** `C(L) = 1 − L`: `|1 − e^{−iω}|² = 2(1 − cos ω)`, so the gain is
  `√(2(1 − cos ω))` (`appx_gain_diff_sq`, `appx_gain_diff`); it is `0` at `ω = 0` and strictly
  increasing on `[0, π]` up to `2` (`appx_gain_diff_mono`).
* **The HP cyclical filter** `C(L) = λ(1 − L)²(1 − L⁻¹)²/(1 + λ(1 − L)²(1 − L⁻¹)²)`: since
  `(1 − e^{−iω})(1 − e^{iω}) = 2(1 − cos ω)` (`appx_diff_prod`),
  `C(e^{−iω}) = 4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)` (`appx_hp_gain_eq`, `hpGain`). It lies in
  `[0, 1)` (`appx_hp_gain_bounds`), vanishes at `ω = 0` (`appx_hp_gain_zero`), is strictly
  increasing on `[0, π]` (`appx_hp_gain_mono`) and tends to `1` as `λ → ∞` for `ω ∈ (0, π]`
  (`appx_hp_gain_limit`).
* A larger `λ` means **more** smoothing: the gain of the trend filter, `1 − C`, is
  `1/(1 + 4λ(1 − cos ω)²)`, strictly decreasing in `λ` for `ω ∈ (0, π]`
  (`appx_hp_trend_gain_anti`).
* **The ideal band-pass filter** with gain `1` on `ω₁ ≤ |ω| ≤ ω₂` and `0` elsewhere has
  coefficients `b_k = (1/2π)∫ G(ω)e^{ikω}dω = (sin kω₂ − sin kω₁)/(πk)` for `k ≠ 0`
  (`appx_bandpass_coeff`) and `b₀ = (ω₂ − ω₁)/π` (`appx_bandpass_coeff_zero`).
-/

namespace AKMM.RealBusinessCycles

open Complex Filter Topology

/-- `e^{ix} − e^{−ix} = 2i sin x` for real `x`. -/
theorem appx_exp_sub_exp (x : ℝ) :
    Complex.exp (x * I) - Complex.exp (-x * I) = 2 * Real.sin x * I := by
  rw [show (-x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, exp_mul_I, exp_mul_I, ← ofReal_cos,
    ← ofReal_sin, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- `(1 − e^{−iω})(1 − e^{iω}) = 2(1 − cos ω)`. -/
theorem appx_diff_prod (ω : ℝ) :
    (1 - Complex.exp (-ω * I)) * (1 - Complex.exp (ω * I)) = 2 * (1 - Real.cos ω) := by
  have h : Complex.exp (-ω * I) * Complex.exp (ω * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hc : Complex.exp (ω * I) + Complex.exp (-ω * I) = 2 * Real.cos ω := by
    rw [show (-ω : ℂ) = ((-ω : ℝ) : ℂ) by push_cast; ring, exp_mul_I, exp_mul_I, ← ofReal_cos,
      ← ofReal_sin, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  linear_combination h - hc

/-- **AKMM, p. 865: the squared gain of the first difference** `|1 − e^{−iω}|² = 2(1 − cos ω)`. -/
theorem appx_gain_diff_sq (ω : ℝ) :
    Complex.normSq (1 - Complex.exp (-ω * I)) = 2 * (1 - Real.cos ω) := by
  have hconj : (starRingEnd ℂ) (1 - Complex.exp (-ω * I)) = 1 - Complex.exp (ω * I) := by
    rw [map_sub, map_one, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  have := Complex.mul_conj (1 - Complex.exp (-ω * I))
  rw [hconj, appx_diff_prod] at this
  exact_mod_cast this.symm

/-- **AKMM, p. 865: the gain of the first difference** `G(ω) = |1 − e^{−iω}| = √(2(1 − cos ω))`. -/
theorem appx_gain_diff (ω : ℝ) : ‖1 - Complex.exp (-ω * I)‖ = Real.sqrt (2 * (1 - Real.cos ω)) := by
  rw [← appx_gain_diff_sq, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- AKMM, p. 865: the first difference "fully attenuates" frequency `0` and its gain is strictly
increasing on `[0, π]`, reaching `2` at `π`. -/
theorem appx_gain_diff_mono :
    Real.sqrt (2 * (1 - Real.cos 0)) = 0 ∧ Real.sqrt (2 * (1 - Real.cos Real.pi)) = 2 ∧
      StrictMonoOn (fun ω => Real.sqrt (2 * (1 - Real.cos ω))) (Set.Icc 0 Real.pi) := by
  refine ⟨by simp, ?_, fun a ha b hb hab => ?_⟩
  · rw [Real.cos_pi, show (2 : ℝ) * (1 - -1) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · have hc := Real.strictAntiOn_cos ha hb hab
    have h0 : 0 ≤ 2 * (1 - Real.cos a) := by linarith [Real.cos_le_one a]
    exact Real.sqrt_lt_sqrt h0 (by linarith)

/-- The gain of the HP cyclical filter, `4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)`. -/
noncomputable def hpGain (lam ω : ℝ) : ℝ :=
  4 * lam * (1 - Real.cos ω) ^ 2 / (1 + 4 * lam * (1 - Real.cos ω) ^ 2)

/-- **AKMM, p. 865: the HP filter's frequency response.** With `x = (1 − e^{−iω})²(1 − e^{iω})²`,
`λx/(1 + λx) = 4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)`, a real number. -/
theorem appx_hp_gain_eq (lam ω : ℝ) :
    lam * ((1 - Complex.exp (-ω * I)) ^ 2 * (1 - Complex.exp (ω * I)) ^ 2) /
      (1 + lam * ((1 - Complex.exp (-ω * I)) ^ 2 * (1 - Complex.exp (ω * I)) ^ 2)) =
      (hpGain lam ω : ℂ) := by
  have h : (1 - Complex.exp (-ω * I)) ^ 2 * (1 - Complex.exp (ω * I)) ^ 2 =
      4 * (1 - Real.cos ω) ^ 2 := by
    rw [← mul_pow, appx_diff_prod]; ring
  rw [h, hpGain]
  push_cast
  ring

theorem appx_hp_den_pos {lam : ℝ} (hlam : 0 ≤ lam) (ω : ℝ) :
    0 < 1 + 4 * lam * (1 - Real.cos ω) ^ 2 := by positivity

/-- The HP gain lies in `[0, 1)` for `λ ≥ 0`. -/
theorem appx_hp_gain_bounds {lam : ℝ} (hlam : 0 ≤ lam) (ω : ℝ) :
    0 ≤ hpGain lam ω ∧ hpGain lam ω < 1 := by
  have hd := appx_hp_den_pos hlam ω
  unfold hpGain
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hd]
  linarith

/-- AKMM, p. 865: "at very low frequencies … the gain function `G(ω) ≈ 0`": `G(0) = 0`. -/
theorem appx_hp_gain_zero (lam : ℝ) : hpGain lam 0 = 0 := by simp [hpGain]

/-- AKMM, p. 865: the HP filter removes low frequencies more than high ones: for `λ > 0` its gain
is strictly increasing on `[0, π]`. -/
theorem appx_hp_gain_mono {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (hpGain lam) (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  have hc := Real.strictAntiOn_cos ha hb hab
  have hxa : 0 ≤ 1 - Real.cos a := by linarith [Real.cos_le_one a]
  have hx : (1 - Real.cos a) ^ 2 < (1 - Real.cos b) ^ 2 := by nlinarith
  unfold hpGain
  have h1 := appx_hp_den_pos hlam.le a
  have h2 := appx_hp_den_pos hlam.le b
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

theorem appx_cos_lt_one {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ Real.pi) : 0 < 1 - Real.cos ω := by
  have := Real.strictAntiOn_cos (Set.left_mem_Icc.2 Real.pi_pos.le) ⟨h0.le, h1⟩ h0
  rw [Real.cos_zero] at this
  linarith

/-- AKMM, p. 865: "the spectrum of the filtered series converges to that of the original time
series": for `ω ∈ (0, π]`, `G(ω) → 1` as `λ → ∞`. -/
theorem appx_hp_gain_limit {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ Real.pi) :
    Tendsto (fun lam => hpGain lam ω) atTop (𝓝 1) := by
  set a := 4 * (1 - Real.cos ω) ^ 2
  have ha : 0 < a := by have := appx_cos_lt_one h0 h1; positivity
  have e : ∀ lam, 0 < lam → hpGain lam ω = 1 - 1 / (1 + lam * a) := fun lam hl => by
    have : 0 < 1 + lam * a := by positivity
    unfold hpGain; simp only [a]; field_simp; ring
  have ht : Tendsto (fun lam : ℝ => 1 + lam * a) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const ha)
  have := (ht.inv_tendsto_atTop).const_sub 1
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hl
  rw [e lam hl, one_div]
  rfl

/-- AKMM, p. 865, corrected: a larger `λ` gives **more** smoothing: the gain of the trend filter
`1 − C(e^{−iω}) = 1/(1 + 4λ(1 − cos ω)²)` is strictly decreasing in `λ` at every `ω ∈ (0, π]`. -/
theorem appx_hp_trend_gain_anti {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ Real.pi) :
    (∀ lam, 0 ≤ lam → 1 - hpGain lam ω = 1 / (1 + 4 * lam * (1 - Real.cos ω) ^ 2)) ∧
      StrictAntiOn (fun lam => 1 / (1 + 4 * lam * (1 - Real.cos ω) ^ 2)) (Set.Ici 0) := by
  have hx : 0 < (1 - Real.cos ω) ^ 2 := by have := appx_cos_lt_one h0 h1; positivity
  refine ⟨fun lam hl => ?_, fun a ha b hb hab => ?_⟩
  · have := appx_hp_den_pos hl ω
    unfold hpGain; field_simp; ring
  · simp only [Set.mem_Ici] at ha hb
    have h1 := appx_hp_den_pos ha ω
    exact one_div_lt_one_div_of_lt h1 (by nlinarith)

/-- **AKMM, p. 865: the ideal band-pass filter's coefficients.** With gain `1` on
`ω₁ ≤ |ω| ≤ ω₂` and `0` elsewhere, for `k ≠ 0`,
`(1/2π)(∫_{ω₁}^{ω₂}e^{ikω}dω + ∫_{−ω₂}^{−ω₁}e^{ikω}dω) = (sin kω₂ − sin kω₁)/(πk)`. -/
theorem appx_bandpass_coeff {k : ℝ} (hk : k ≠ 0) (ω₁ ω₂ : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ((∫ ω in ω₁..ω₂, Complex.exp (k * I * ω)) +
      ∫ ω in (-ω₂)..(-ω₁), Complex.exp (k * I * ω)) =
      ((Real.sin (k * ω₂) - Real.sin (k * ω₁)) / (Real.pi * k) : ℝ) := by
  have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hk) I_ne_zero
  rw [integral_exp_mul_complex hc, integral_exp_mul_complex hc]
  have hS : ∀ x : ℝ, Complex.exp (k * I * x) - Complex.exp (k * I * ((-x : ℝ) : ℂ)) =
      2 * Real.sin (k * x) * I := fun x => by
    have := appx_exp_sub_exp (k * x)
    rw [← this]
    push_cast
    ring_nf
  have h2 := hS ω₂
  have h1 := hS ω₁
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk
  have e : (Complex.exp (k * I * ω₂) - Complex.exp (k * I * ω₁)) / (k * I) +
      (Complex.exp (k * I * ((-ω₁ : ℝ) : ℂ)) - Complex.exp (k * I * ((-ω₂ : ℝ) : ℂ))) / (k * I) =
      ((Complex.exp (k * I * ω₂) - Complex.exp (k * I * ((-ω₂ : ℝ) : ℂ))) -
        (Complex.exp (k * I * ω₁) - Complex.exp (k * I * ((-ω₁ : ℝ) : ℂ)))) / (k * I) := by
    ring
  rw [e, h1, h2]
  push_cast
  field_simp

/-- AKMM, p. 865: the central band-pass coefficient `b₀ = (ω₂ − ω₁)/π`
(`(1/2π)` times the length of the two bands). -/
theorem appx_bandpass_coeff_zero (ω₁ ω₂ : ℝ) :
    1 / (2 * Real.pi) * ((∫ _ in ω₁..ω₂, (1 : ℝ)) + ∫ _ in (-ω₂)..(-ω₁), (1 : ℝ)) =
      (ω₂ - ω₁) / Real.pi := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp
  ring

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectrum of a stationary process

AKMM, Appendix 14.A, pp. 863–864.

For an absolutely summable autocovariance sequence `γ : ℤ → ℝ`, the spectrum is
`s(ω) = (1/2π)Σₖ γₖe^{−ikω}` (`specC`, complex-valued).

* Orthogonality: `∫_{−π}^{π} e^{imω}dω = 2π` if `m = 0` and `0` otherwise (`appx_orth`).
* **The inversion formula** `∫_{−π}^{π} s(ω)e^{ikω}dω = γₖ` (`appx_inversion`), interchanging the
  sum and the integral by dominated convergence (the bound `Σ|γₙ| < ∞`).
* **The variance** `Var(Y) = γ₀ = ∫_{−π}^{π} s(ω)dω` (`appx_variance`).
* For symmetric `γ` (`γ₋ₖ = γₖ`, as for autocovariances) the spectrum is even
  (`appx_spec_even`), so the variance contributed by the band `ω₁ ≤ |ω| ≤ ω₂` is
  `2∫_{ω₁}^{ω₂}s` (`appx_band_variance`).
* **Linear filters** (finite, `Y^c_t = Σ_{j∈J}c_jY_{t−j}`): the filtered autocovariances are
  `γ^c_k = Σ_jΣ_l c_jc_lγ_{k−j+l}` (`appx_filter_autocov`, from second moments of the process),
  and the filtered spectrum is `C(e^{−iω})C(e^{iω})s(ω) = |C(e^{−iω})|²s(ω)`
  (`appx_filtered_spectrum`, `appx_transfer_normSq`).

Departures: filters are finite (lead–lag polynomials with finitely many terms); the HP and
band-pass filters are infinite two-sided filters, for which only the gain functions are formalised
(`Gains`). The spectral representation theorem (Cramér) is proved in Hilbert-space form in
`Herglotz`, `SpectralDensity` and `Cramer`.
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory

/-- AKMM, p. 863: the spectrum `s(ω) = (1/2π)Σₖ γₖe^{−ikω}`. -/
noncomputable def specC (γ : ℤ → ℝ) (ω : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∑' n : ℤ, (γ n : ℂ) * Complex.exp (((-(n * ω) : ℝ) : ℂ) * I)

/-- Orthogonality of the exponentials on `[−π, π]`. -/
theorem appx_orth (m : ℤ) :
    ∫ ω in (-Real.pi)..Real.pi, Complex.exp ((((m : ℝ) * ω : ℝ) : ℂ) * I) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Int.cast_zero, zero_mul, ofReal_zero, Complex.exp_zero,
      intervalIntegral.integral_const, real_smul, mul_one]
    push_cast
    ring
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hm) I_ne_zero
    have e : (fun ω : ℝ => Complex.exp ((((m : ℝ) * ω : ℝ) : ℂ) * I)) =
        fun ω : ℝ => Complex.exp ((m : ℂ) * I * ω) := by
      funext ω; push_cast; ring_nf
    rw [e, integral_exp_mul_complex hc]
    have h2 : Complex.exp ((m : ℂ) * I * (Real.pi : ℂ)) =
        Complex.exp ((m : ℂ) * I * ((-Real.pi : ℝ) : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I m
      rw [show (m : ℂ) * I * (Real.pi : ℂ) =
        (m : ℂ) * I * ((-Real.pi : ℝ) : ℂ) + m * (2 * Real.pi * I) by push_cast; ring,
        Complex.exp_add, h1, mul_one]
    rw [h2, sub_self, zero_div]

/-- The summands `γₙe^{i(k−n)ω}` of `s(ω)e^{ikω}`, up to `1/2π`. -/
theorem appx_spec_mul_exp (γ : ℤ → ℝ) (k : ℤ) (ω : ℝ) :
    specC γ ω * Complex.exp ((((k : ℝ) * ω : ℝ) : ℂ) * I) =
      (1 / (2 * Real.pi) : ℂ) *
        ∑' n : ℤ, (γ n : ℂ) * Complex.exp (((((k - n : ℤ) : ℝ) * ω : ℝ) : ℂ) * I) := by
  unfold specC
  rw [mul_assoc, ← tsum_mul_right]
  congr 2
  funext n
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem appx_norm_term (γ : ℤ → ℝ) (n : ℤ) (x : ℝ) :
    ‖(γ n : ℂ) * Complex.exp ((x : ℂ) * I)‖ = |γ n| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **AKMM, p. 863: the inversion formula.** If `Σ|γₙ| < ∞`, then
`∫_{−π}^{π} s(ω)e^{ikω}dω = γₖ` for every integer `k`. -/
theorem appx_inversion (γ : ℤ → ℝ) (hγ : Summable fun n => |γ n|) (k : ℤ) :
    ∫ ω in (-Real.pi)..Real.pi, specC γ ω * Complex.exp ((((k : ℝ) * ω : ℝ) : ℂ) * I) = γ k := by
  set F : ℤ → ℝ → ℂ := fun n ω =>
    (γ n : ℂ) * Complex.exp (((((k - n : ℤ) : ℝ) * ω : ℝ) : ℂ) * I) with hFdef
  have hsumm : ∀ ω, Summable fun n => F n ω := fun ω =>
    Summable.of_norm_bounded hγ fun n => (appx_norm_term γ n _).le
  have hcont : ∀ n, Continuous (F n) := fun n => by
    simp only [hFdef]; fun_prop
  have hS := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -Real.pi) (b := Real.pi) (F := F) (f := fun ω => ∑' n, F n ω)
    (fun n _ => |γ n|) (fun n => (hcont n).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t _ => (appx_norm_term γ n _).le)
    (ae_of_all _ fun _ _ => hγ) intervalIntegrable_const
    (ae_of_all _ fun t _ => (hsumm t).hasSum)
  have hval : ∀ n, ∫ ω in (-Real.pi)..Real.pi, F n ω =
      if n = k then (γ k : ℂ) * (2 * Real.pi) else 0 := fun n => by
    simp only [hFdef]
    rw [intervalIntegral.integral_const_mul, appx_orth]
    by_cases h : n = k
    · subst h; simp
    · have : k - n ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      simp [this, h]
  simp only [hval] at hS
  have hI := hS.unique (hasSum_ite_eq k _)
  simp only [appx_spec_mul_exp]
  rw [intervalIntegral.integral_const_mul, hI]
  have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- **AKMM, p. 864: the variance is the integral of the spectrum**,
`Var(Yₜ) = γ₀ = ∫_{−π}^{π} s(ω)dω`. -/
theorem appx_variance (γ : ℤ → ℝ) (hγ : Summable fun n => |γ n|) :
    ∫ ω in (-Real.pi)..Real.pi, specC γ ω = γ 0 := by
  have := appx_inversion γ hγ 0
  simpa using this

/-- For a symmetric autocovariance sequence (`γ₋ₙ = γₙ`), the spectrum is even. -/
theorem appx_spec_even (γ : ℤ → ℝ) (hsym : ∀ n, γ (-n) = γ n) (ω : ℝ) :
    specC γ (-ω) = specC γ ω := by
  unfold specC
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  simp only [Equiv.neg_apply, hsym, Int.cast_neg]
  congr 3
  ring_nf

/-- **AKMM, p. 864, the variance of a frequency band, corrected.** For symmetric `γ` the variance
contributed by the frequencies `ω₁ ≤ |ω| ≤ ω₂` is `∫_{−ω₂}^{−ω₁}s + ∫_{ω₁}^{ω₂}s = 2∫_{ω₁}^{ω₂}s`
(the book writes `∫_{ω₁}^{ω₂}f(ω)dω`, with `f` undefined and the negative band omitted). -/
theorem appx_band_variance (γ : ℤ → ℝ) (hsym : ∀ n, γ (-n) = γ n) (ω₁ ω₂ : ℝ) :
    (∫ ω in (-ω₂)..(-ω₁), specC γ ω) + ∫ ω in ω₁..ω₂, specC γ ω =
      2 * ∫ ω in ω₁..ω₂, specC γ ω := by
  have h := intervalIntegral.integral_comp_neg (a := ω₁) (b := ω₂) (fun ω => specC γ ω)
  simp only [appx_spec_even γ hsym] at h
  rw [← h]
  ring

/-- The autocovariances of the filtered series `Σ_{j∈J}c_jY_{t−j}`:
`γ^c_k = Σ_jΣ_l c_jc_lγ_{k−j+l}`. -/
def filtAutocov (J : Finset ℤ) (c γ : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑ j ∈ J, ∑ l ∈ J, c j * c l * γ (k - j + l)

/-- The transfer function `C(e^{−iω}) = Σ_{j∈J}c_je^{−ijω}` of the filter. -/
noncomputable def transferFn (J : Finset ℤ) (c : ℤ → ℝ) (ω : ℝ) : ℂ :=
  ∑ j ∈ J, (c j : ℂ) * Complex.exp (((-(j * ω) : ℝ) : ℂ) * I)

/-- AKMM, p. 864: if `Y` has second moments `E[Y_sY_t] = γ_{s−t}` (mean zero, weakly stationary),
the filtered series `Y^c_t = Σ_{j∈J}c_jY_{t−j}` has `E[Y^c_tY^c_{t−k}] = γ^c_k`. -/
theorem appx_filter_autocov {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (Y : ℤ → Ω → ℝ) (γ : ℤ → ℝ) (hY : ∀ s t, ∫ x, Y s x * Y t x ∂μ = γ (s - t))
    (hint : ∀ s t, Integrable (fun x => Y s x * Y t x) μ) (J : Finset ℤ) (c : ℤ → ℝ)
    (t k : ℤ) :
    ∫ x, (∑ j ∈ J, c j * Y (t - j) x) * (∑ l ∈ J, c l * Y (t - k - l) x) ∂μ =
      filtAutocov J c γ k := by
  have e : ∀ x, (∑ j ∈ J, c j * Y (t - j) x) * (∑ l ∈ J, c l * Y (t - k - l) x) =
      ∑ j ∈ J, ∑ l ∈ J, c j * c l * (Y (t - j) x * Y (t - k - l) x) := fun x => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (hint _ _).const_mul _]
  unfold filtAutocov
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => (hint _ _).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, hY]
  congr 2
  ring

/-- **AKMM, p. 864: the spectrum of a filtered series.** For a finite filter `c` on `J` and
absolutely summable `γ`, `s^c(ω) = C(e^{−iω})C(e^{iω})s(ω)`. -/
theorem appx_filtered_spectrum (J : Finset ℤ) (c γ : ℤ → ℝ) (hγ : Summable fun n => |γ n|)
    (ω : ℝ) :
    specC (filtAutocov J c γ) ω = transferFn J c ω * transferFn J c (-ω) * specC γ ω := by
  set E : ℤ → ℂ := fun n => Complex.exp (((-(n * ω) : ℝ) : ℂ) * I) with hE
  have hEadd : ∀ m j l : ℤ, E (m + (j - l)) = E m * E j * E (-l) := fun m j l => by
    simp only [hE, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum1 : ∀ j l : ℤ, Summable fun k : ℤ => ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k :=
    fun j l => by
      have hs : Summable fun k : ℤ => |c j * c l| * |γ (k + (l - j))| :=
        (hγ.comp_injective (add_left_injective (l - j))).mul_left _
      refine Summable.of_norm_bounded hs fun k => le_of_eq ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, show k - j + l = k + (l - j) by ring]
  unfold specC
  suffices key : ∑' n : ℤ,
      ((filtAutocov J c γ n : ℝ) : ℂ) * Complex.exp (((-(n * ω) : ℝ) : ℂ) * I) =
      transferFn J c ω * transferFn J c (-ω) *
        ∑' n : ℤ, (γ n : ℂ) * Complex.exp (((-(n * ω) : ℝ) : ℂ) * I) by
    rw [key]; ring
  simp only [filtAutocov]
  have e1 : ∀ k : ℤ, ((∑ j ∈ J, ∑ l ∈ J, c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k =
      ∑ j ∈ J, ∑ l ∈ J, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k := fun k => by
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  rw [show (fun k : ℤ => ((∑ j ∈ J, ∑ l ∈ J, c j * c l * γ (k - j + l) : ℝ) : ℂ) *
      Complex.exp (((-(k * ω) : ℝ) : ℂ) * I)) =
      fun k => ∑ j ∈ J, ∑ l ∈ J, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k from funext e1]
  rw [Summable.tsum_finsetSum fun j _ => summable_sum fun l _ => hsum1 j l]
  have inner : ∀ j l : ℤ, ∑' k : ℤ, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k =
      ((c j : ℂ) * E j) * ((c l : ℂ) * E (-l)) * ∑' m : ℤ, (γ m : ℂ) * E m := fun j l => by
    rw [← (Equiv.addRight (j - l)).tsum_eq, ← tsum_mul_left]
    congr 1
    funext m
    simp only [Equiv.coe_addRight, hEadd]
    rw [show m + (j - l) - j + l = m by ring]
    push_cast
    ring
  have hsj : ∀ j, ∑' k : ℤ, ∑ l ∈ J, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k =
      ∑ l ∈ J, ∑' k : ℤ, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k := fun j =>
    Summable.tsum_finsetSum fun l _ => hsum1 j l
  simp only [hsj, inner]
  unfold transferFn
  simp only [hE]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring_nf

/-- AKMM, p. 864: `C(e^{−iω})C(e^{iω}) = |C(e^{−iω})|²` for a real filter, so
`s^c = |C(e^{−iω})|²s`. -/
theorem appx_transfer_normSq (J : Finset ℤ) (c : ℤ → ℝ) (ω : ℝ) :
    transferFn J c ω * transferFn J c (-ω) = Complex.normSq (transferFn J c ω) := by
  rw [← Complex.mul_conj]
  congr 1
  unfold transferFn
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast
  ring

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Herglotz theorem

AKMM, §14.3.1, pp. 412–413 (beyond the text).

AKMM, §14.3.1, pp. 412–413 (a result beyond the text). The book states without proof that "any
stationary process" is a random superposition of sines and cosines; the first half of that
statement is the existence and uniqueness of the spectral measure, proved here.

The circle is `AddCircle T` (`ℝ/Tℤ`, `T > 0`) with the characters `eₕ = fourier h`,
`eₕ(x) = e^{2πihx/T}`; for `T = 2π` these are `e^{ihω}`, `ω ∈ (−π, π]`.

* Positive definiteness (`hergPosDef`): `Σⱼₖ cⱼc̄ₖγ(j − k)` is real and `≥ 0` for every finite `c`.
* **The Herglotz theorem** (`herg_herglotz`): `γ : ℤ → ℂ` is positive definite if and only if
  `γ(h) = ∫ eₕ dF` for a finite positive measure `F` on the circle, and `F` is unique
  (`herg_unique`).
* Existence (`herg_exists`). The Fejér densities `f_N = Σ_{|h|<N}(1 − |h|/N)γ(h)e_{−h}` are the
  quadratic forms `(1/N)Σ_{j,k<N}cⱼc̄ₖγ(j − k)` with `cⱼ = e_{−j}(x)` (`herg_fejer_eq`, by
  `herg_sum_pairs`, `herg_card_pairs`), hence nonnegative (`herg_fejer_nonneg`); their Fourier
  coefficients `(1 − |m|/N)⁺γ(m)` tend to `γ(m)` (`herg_fejer_coeff`, `herg_fejer_tendsto`); the
  functionals `L_N(G) = ∫ G f_N dHaar` satisfy `‖L_N(G)‖ ≤ γ(0)‖G‖` (`herg_bound`) and therefore
  converge for every continuous `G` by density of trigonometric polynomials (`herg_tendsto`); the
  limit is a positive linear functional (`hergLambda`), and the Riesz–Markov–Kakutani theorem
  gives the measure.
* Uniqueness (`herg_unique`, via `herg_integral_eq_of_coeff`): trigonometric polynomials are
  dense in `C(𝕋, ℂ)`.
* The converse (`herg_posDef_of_measure`): `Σⱼₖ cⱼc̄ₖγ(j − k) = ∫ |Σⱼ cⱼeⱼ|² dF ≥ 0`.
* `γ(−h) = conj γ(h)` (`herg_conj`); for real `γ` the spectral measure is symmetric,
  `F ∘ (−·) = F` (`herg_symm_of_real`).

Departures: `γ` is complex-valued (real `γ` is the special case); the limit of the Fejér measures
is obtained from Riesz–Markov–Kakutani, not Prokhorov: the Fejér functionals converge on all of
`C(𝕋)`, so no subsequence is needed.
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory AddCircle Filter Topology
open scoped ComplexConjugate CompactlySupported

variable {T : ℝ}

/-- A function `γ : ℤ → ℂ` is positive definite if `Σⱼₖ cⱼc̄ₖγ(j − k)` is real and nonnegative for
every finite family `c`. -/
def hergPosDef (γ : ℤ → ℂ) : Prop :=
  ∀ (s : Finset ℤ) (c : ℤ → ℂ),
    (∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k)).im = 0 ∧
      0 ≤ (∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k)).re

/-- The number of pairs `(j, k) ∈ [0, N)²` with `j − k = h` is `(N − |h|)⁺`. -/
theorem herg_card_pairs (N : ℕ) (h : ℤ) :
    ((Finset.Ico (0 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N).filter (fun p => p.1 - p.2 = h)).card =
      ((N : ℤ) - |h|).toNat := by
  have hmax1 := le_max_left 0 h
  have hmax2 := le_max_right 0 h
  have hmin1 := min_le_left (N : ℤ) (N + h)
  have hmin2 := min_le_right (N : ℤ) (N + h)
  have e : (Finset.Ico (0 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N).filter (fun p => p.1 - p.2 = h) =
      (Finset.Ico (max 0 h) (min (N : ℤ) (N + h))).map
        ⟨fun j => (j, j - h), fun a b hab => by simpa using congrArg Prod.fst hab⟩ := by
    ext ⟨j, k⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_map]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      refine ⟨j, ⟨max_le h1 (by omega), lt_min h2 (by omega)⟩, ?_⟩
      change (j, j - h) = (j, k)
      rw [← h5, sub_sub_cancel]
    · rintro ⟨a, ⟨h1, h2⟩, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (he : (a, a - h) = (j, k))
      omega
  rw [e, Finset.card_map, Int.card_Ico]
  rcases le_total 0 h with h0 | h0
  · rw [max_eq_right h0, min_eq_left (by omega), abs_of_nonneg h0]
  · rw [max_eq_left h0, min_eq_right (by omega), abs_of_nonpos h0]
    congr 1
    ring

/-- Re-indexing the double sum `Σ_{j,k∈[0,N)} f(j − k)` by `h = j − k`. -/
theorem herg_sum_pairs (N : ℕ) (f : ℤ → ℂ) :
    ∑ j ∈ Finset.Ico (0 : ℤ) N, ∑ k ∈ Finset.Ico (0 : ℤ) N, f (j - k) =
      ∑ h ∈ Finset.Ioo (-(N : ℤ)) N, (((N : ℝ) - |(h : ℝ)| : ℝ) : ℂ) * f h := by
  rw [← Finset.sum_product' (f := fun j k => f (j - k)),
    ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℤ × ℤ => p.1 - p.2)
      (t := Finset.Ioo (-(N : ℤ)) N)]
  · refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f h) (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, herg_card_pairs, nsmul_eq_mul]
    congr 1
    rw [Finset.mem_Ioo] at hh
    have h0 : 0 ≤ (N : ℤ) - |h| := by rw [sub_nonneg]; exact (abs_lt.2 hh).le
    have : (((N : ℤ) - |h|).toNat : ℝ) = (N : ℝ) - |(h : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      push_cast [Int.cast_abs]
      ring
    rw [← this]
    push_cast
    ring
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_Ico] at hp
    simp only [Finset.mem_Ioo]
    omega

/-- Continuous functions are integrable for a finite measure on the circle. -/
theorem herg_integrable [Fact (0 < T)] (μ : Measure (AddCircle T)) [IsFiniteMeasure μ]
    {G : AddCircle T → ℂ} (hG : Continuous G) : Integrable G μ :=
  hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem herg_re_integral {μ : Measure (AddCircle T)} {f : AddCircle T → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  simpa using (integral_re hf).symm

theorem herg_im_integral {μ : Measure (AddCircle T)} {f : AddCircle T → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := by
  simpa using (integral_im hf).symm

/-- `∫ eₖ dHaar = 1` if `k = 0` and `0` otherwise (normalised Haar measure). -/
theorem herg_integral_fourier [Fact (0 < T)] (k : ℤ) :
    ∫ x, fourier k x ∂(haarAddCircle (T := T)) = if k = 0 then 1 else 0 := by
  have := congrFun (fourierCoeff_fourier (T := T) k) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, smul_eq_mul, one_mul] at this
  rw [this, Pi.single_apply]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [hk, Ne.symm hk]

/-- The Fejér density `f_N(x) = Σ_{|h|<N} (1 − |h|/N)γ(h)e_{−h}(x)`. -/
noncomputable def hergFejer (γ : ℤ → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ h ∈ Finset.Ioo (-(N : ℤ)) N, ((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h * fourier (-h) x

/-- The Fejér density is the quadratic form `(1/N)Σ_{j,k<N} cⱼc̄ₖγ(j − k)` with `cⱼ = e_{−j}(x)`. -/
theorem herg_fejer_eq (γ : ℤ → ℂ) (N : ℕ) (x : AddCircle T) :
    hergFejer γ N x = ((1 / N : ℝ) : ℂ) * ∑ j ∈ Finset.Ico (0 : ℤ) N,
      ∑ k ∈ Finset.Ico (0 : ℤ) N, fourier (-j) x * conj (fourier (-k) x) * γ (j - k) := by
  have e : ∀ j k : ℤ, fourier (-j) x * conj (fourier (-k) x) * γ (j - k) =
      γ (j - k) * fourier (-(j - k)) x := by
    intro j k
    rw [← fourier_neg, neg_neg, show -(j - k) = -j + k by ring, fourier_add]
    ring
  simp_rw [e]
  rw [herg_sum_pairs N (fun h => γ h * fourier (-h) x), Finset.mul_sum]
  unfold hergFejer
  refine Finset.sum_congr rfl fun h _ => ?_
  push_cast
  ring

/-- For positive definite `γ` the Fejér density is real and nonnegative. -/
theorem herg_fejer_nonneg {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ) (x : AddCircle T) :
    (hergFejer γ N x).im = 0 ∧ 0 ≤ (hergFejer γ N x).re := by
  obtain ⟨h1, h2⟩ := hpd (Finset.Ico 0 N) (fun j => fourier (-j) x)
  rw [herg_fejer_eq, Complex.im_ofReal_mul, Complex.re_ofReal_mul]
  exact ⟨by rw [h1, mul_zero], mul_nonneg (by positivity) h2⟩

theorem herg_fejer_continuous (γ : ℤ → ℂ) (N : ℕ) : Continuous (hergFejer (T := T) γ N) :=
  continuous_finsetSum _ fun h _ => continuous_const.mul (fourier (-h)).continuous

/-- The Fejér functional `L_N(G) = ∫ G f_N dHaar`. -/
noncomputable def hergL [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (G : C(AddCircle T, ℂ)) : ℂ :=
  ∫ x, G x * hergFejer γ N x ∂haarAddCircle

/-- The Fourier coefficients of the Fejér density: `(1 − |m|/N)⁺γ(m)`. -/
theorem herg_fejer_coeff [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (m : ℤ) :
    hergL γ N (fourier (T := T) m) = if m ∈ Finset.Ioo (-(N : ℤ)) N then
      ((((N : ℝ) - |(m : ℝ)|) / N : ℝ) : ℂ) * γ m else 0 := by
  unfold hergL hergFejer
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun h _ => herg_integrable _ (by fun_prop))]
  have hterm : ∀ h : ℤ, ∫ x, fourier m x * (((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h *
      fourier (-h) x) ∂(haarAddCircle (T := T)) =
      ((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h * (if m = h then 1 else 0) := by
    intro h
    have e : (fun x : AddCircle T => fourier m x * (((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) *
        γ h * fourier (-h) x)) = fun x => ((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h *
        fourier (m + -h) x := by
      funext x
      rw [fourier_add]
      ring
    rw [e, integral_const_mul, herg_integral_fourier]
    congr 1
    rcases eq_or_ne m h with rfl | hmh
    · simp
    · have : m + -h ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.2 hmh
      simp [this, hmh]
  simp_rw [hterm, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- The Fourier coefficients of the Fejér densities converge: `L_N(eₘ) → γ(m)`. -/
theorem herg_fejer_tendsto [Fact (0 < T)] (γ : ℤ → ℂ) (m : ℤ) :
    Tendsto (fun n : ℕ => hergL γ (n + 1) (fourier (T := T) m)) atTop (𝓝 (γ m)) := by
  have hev : (fun n : ℕ => ((1 - |(m : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) * γ m) =ᶠ[atTop]
      fun n => hergL γ (n + 1) (fourier (T := T) m) := by
    filter_upwards [eventually_gt_atTop m.natAbs] with n hn
    have hmem : m ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
      rw [Finset.mem_Ioo]
      omega
    simp only [herg_fejer_coeff, hmem, ↓reduceIte]
    congr 1
    push_cast
    field_simp
  have hlim : Tendsto (fun n : ℕ => (1 - |(m : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |(m : ℝ)|)
  have := ((continuous_ofReal.tendsto 1).comp hlim).mul_const (γ m)
  simp only [ofReal_one, one_mul] at this
  exact this.congr' hev

/-- `∫ f_N dHaar = γ(0)` for `N ≥ 1`. -/
theorem herg_integral_fejer [Fact (0 < T)] (γ : ℤ → ℂ) (n : ℕ) :
    ∫ x, hergFejer (T := T) γ (n + 1) x ∂haarAddCircle = γ 0 := by
  have := herg_fejer_coeff (T := T) γ (n + 1) 0
  have hmem : (0 : ℤ) ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
    rw [Finset.mem_Ioo]
    omega
  simp only [hergL, fourier_zero, one_mul, hmem, ↓reduceIte] at this
  rw [this]
  simp only [Int.cast_zero, abs_zero, sub_zero]
  rw [div_self (by positivity), ofReal_one, one_mul]

theorem herg_fejer_norm {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ) (x : AddCircle T) :
    ‖hergFejer γ N x‖ = (hergFejer γ N x).re := by
  obtain ⟨h1, h2⟩ := herg_fejer_nonneg hpd N x
  have : hergFejer γ N x = ((hergFejer γ N x).re : ℂ) := Complex.ext (by simp) (by simp [h1])
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
  simp

/-- `γ(0)` is real and nonnegative for positive definite `γ`. -/
theorem herg_posDef_zero {γ : ℤ → ℂ} (hpd : hergPosDef γ) : (γ 0).im = 0 ∧ 0 ≤ (γ 0).re := by
  simpa using hpd {0} (fun _ => 1)

/-- The uniform bound `‖L_N(G)‖ ≤ ‖G‖γ(0)`. -/
theorem herg_bound [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (n : ℕ)
    (G : C(AddCircle T, ℂ)) : ‖hergL γ (n + 1) G‖ ≤ ‖G‖ * (γ 0).re := by
  unfold hergL
  calc ‖∫ x, G x * hergFejer γ (n + 1) x ∂haarAddCircle‖
      ≤ ∫ x, ‖G‖ * (hergFejer γ (n + 1) x).re ∂haarAddCircle :=
        norm_integral_le_of_norm_le
          ((herg_integrable _ (herg_fejer_continuous γ (n + 1))).re.const_mul _)
          (ae_of_all _ fun x => by
            rw [norm_mul, herg_fejer_norm hpd]
            exact mul_le_mul_of_nonneg_right (G.norm_coe_le_norm x)
              (herg_fejer_nonneg hpd _ x).2)
    _ = ‖G‖ * (γ 0).re := by
      rw [integral_const_mul, ← herg_integral_fejer (T := T) γ n,
        herg_re_integral (herg_integrable _ (herg_fejer_continuous γ (n + 1)))]

theorem herg_L_add [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (G G' : C(AddCircle T, ℂ)) :
    hergL γ N (G + G') = hergL γ N G + hergL γ N G' := by
  unfold hergL
  simp only [ContinuousMap.add_apply, add_mul]
  exact integral_add (herg_integrable _ (G.continuous.mul (herg_fejer_continuous γ N)))
    (herg_integrable _ (G'.continuous.mul (herg_fejer_continuous γ N)))

theorem herg_L_smul [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (c : ℂ) (G : C(AddCircle T, ℂ)) :
    hergL γ N (c • G) = c * hergL γ N G := by
  unfold hergL
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem herg_L_sub [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (G G' : C(AddCircle T, ℂ)) :
    hergL γ N (G - G') = hergL γ N G - hergL γ N G' := by
  rw [sub_eq_add_neg, herg_L_add, ← neg_one_smul ℂ G', herg_L_smul]
  ring

/-- On trigonometric polynomials the Fejér functionals converge. -/
theorem herg_tendsto_span [Fact (0 < T)] (γ : ℤ → ℂ) {G : C(AddCircle T, ℂ)}
    (hG : G ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    ∃ l, Tendsto (fun n : ℕ => hergL γ (n + 1) G) atTop (𝓝 l) := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨γ m, herg_fejer_tendsto γ m⟩
  | zero => exact ⟨0, by simp [hergL]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simpa only [herg_L_add] using ha.add hb⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simpa only [herg_L_smul] using ha.const_mul c⟩

/-- For positive definite `γ` the Fejér functionals `L_N(G)` converge for every continuous `G`
(uniform bound plus density of trigonometric polynomials). -/
theorem herg_tendsto [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (G : C(AddCircle T, ℂ)) :
    ∃ l, Tendsto (fun n : ℕ => hergL γ (n + 1) G) atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set c := (γ 0).re with hc
  have hc0 : 0 ≤ c := (herg_posDef_zero hpd).2
  have hG : G ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hG (ε / (3 * (c + 1))) (by positivity)
  obtain ⟨l, hl⟩ := herg_tendsto_span γ hb
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hl.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hGb : ‖G - b‖ * c ≤ ε / 3 := by
    rw [← dist_eq_norm]
    calc dist G b * c ≤ ε / (3 * (c + 1)) * c := mul_le_mul_of_nonneg_right hdist.le hc0
      _ ≤ ε / (3 * (c + 1)) * (c + 1) := by gcongr; linarith
      _ = ε / 3 := by field_simp
  have h1 : dist (hergL γ (n + 1) G) (hergL γ (n + 1) b) ≤ ε / 3 := by
    rw [dist_eq_norm, ← herg_L_sub]
    exact (herg_bound hpd n _).trans hGb
  have h2 : dist (hergL γ (N + 1) b) (hergL γ (N + 1) G) ≤ ε / 3 := by
    rw [dist_comm, dist_eq_norm, ← herg_L_sub]
    exact (herg_bound hpd N _).trans hGb
  have h3 := hN n hn
  calc dist (hergL γ (n + 1) G) (hergL γ (N + 1) G)
      ≤ dist (hergL γ (n + 1) G) (hergL γ (n + 1) b) + dist (hergL γ (n + 1) b)
        (hergL γ (N + 1) b) + dist (hergL γ (N + 1) b) (hergL γ (N + 1) G) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- The limit functional `L(G) = lim_N L_N(G)`. -/
noncomputable def hergLim [Fact (0 < T)] (γ : ℤ → ℂ) (G : C(AddCircle T, ℂ)) : ℂ :=
  limUnder atTop (fun n : ℕ => hergL γ (n + 1) G)

theorem herg_tendsto_lim [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ)
    (G : C(AddCircle T, ℂ)) :
    Tendsto (fun n : ℕ => hergL γ (n + 1) G) atTop (𝓝 (hergLim γ G)) :=
  tendsto_nhds_limUnder (herg_tendsto hpd G)

theorem herg_lim_add [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ)
    (G G' : C(AddCircle T, ℂ)) : hergLim γ (G + G') = hergLim γ G + hergLim γ G' :=
  tendsto_nhds_unique (herg_tendsto_lim hpd (G + G'))
    (by simpa only [herg_L_add] using (herg_tendsto_lim hpd G).add (herg_tendsto_lim hpd G'))

theorem herg_lim_smul [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (c : ℂ)
    (G : C(AddCircle T, ℂ)) : hergLim γ (c • G) = c * hergLim γ G :=
  tendsto_nhds_unique (herg_tendsto_lim hpd (c • G))
    (by simpa only [herg_L_smul] using (herg_tendsto_lim hpd G).const_mul c)

/-- A real continuous function as a complex one. -/
def hergOfReal (g : C(AddCircle T, ℝ)) : C(AddCircle T, ℂ) :=
  ⟨fun x => (g x : ℂ), continuous_ofReal.comp g.continuous⟩

/-- `Re L_N(G) = ∫ G f_N`, for real `G`, is `∫ G · Re f_N`. -/
theorem herg_L_ofReal_re [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ)
    (g : C(AddCircle T, ℝ)) :
    (hergL γ N (hergOfReal g)).re = ∫ x, g x * (hergFejer γ N x).re ∂haarAddCircle := by
  unfold hergL
  have hi : Integrable (fun x => hergOfReal g x * hergFejer γ N x) haarAddCircle :=
    herg_integrable _ ((hergOfReal g).continuous.mul (herg_fejer_continuous γ N))
  rw [herg_re_integral hi]
  simp [hergOfReal]

/-- `Re L_N(Re a) = Re L_N(a)`, since `f_N` is real. -/
theorem herg_L_re [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ)
    (a : C(AddCircle T, ℂ)) :
    (hergL γ N (hergOfReal ⟨fun x => (a x).re, by fun_prop⟩)).re = (hergL γ N a).re := by
  rw [herg_L_ofReal_re]
  unfold hergL
  have hi : Integrable (fun x => a x * hergFejer γ N x) haarAddCircle :=
    herg_integrable _ (a.continuous.mul (herg_fejer_continuous γ N))
  rw [herg_re_integral hi]
  congr 1
  funext x
  simp [Complex.mul_re, (herg_fejer_nonneg hpd N x).1]

/-- `Re L_N(Im a) = Im L_N(a)`, since `f_N` is real. -/
theorem herg_L_im [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ)
    (a : C(AddCircle T, ℂ)) :
    (hergL γ N (hergOfReal ⟨fun x => (a x).im, by fun_prop⟩)).re = (hergL γ N a).im := by
  rw [herg_L_ofReal_re]
  unfold hergL
  have hi : Integrable (fun x => a x * hergFejer γ N x) haarAddCircle :=
    herg_integrable _ (a.continuous.mul (herg_fejer_continuous γ N))
  rw [herg_im_integral hi]
  congr 1
  funext x
  simp [Complex.mul_im, (herg_fejer_nonneg hpd N x).1]

/-- The positive linear functional `Λ(g) = Re L(g)` on `C(𝕋, ℝ)` (all continuous functions on
the circle are compactly supported). -/
noncomputable def hergLambda [Fact (0 < T)] (γ : ℤ → ℂ) (hpd : hergPosDef γ) :
    C_c(AddCircle T, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun g => (hergLim γ (hergOfReal g.toContinuousMap)).re
      map_add' := fun g g' => by
        have : hergOfReal (g + g').toContinuousMap =
            hergOfReal g.toContinuousMap + hergOfReal g'.toContinuousMap := by
          ext x
          simp [hergOfReal]
        rw [this, herg_lim_add hpd, Complex.add_re]
      map_smul' := fun r g => by
        have : hergOfReal (r • g).toContinuousMap = (r : ℂ) • hergOfReal g.toContinuousMap := by
          ext x
          simp [hergOfReal]
        rw [this, herg_lim_smul hpd, Complex.re_ofReal_mul]
        rfl }
    (fun g hg => by
      refine ge_of_tendsto' ((continuous_re.tendsto _).comp
        (herg_tendsto_lim hpd (hergOfReal g.toContinuousMap))) fun n => ?_
      simp only [Function.comp_apply]
      rw [herg_L_ofReal_re]
      exact integral_nonneg fun x => mul_nonneg (hg x) (herg_fejer_nonneg hpd _ x).2)

/-- AKMM, pp. 412–413 (beyond the text). **Existence in the Herglotz theorem.** A positive definite
`γ : ℤ → ℂ` is the sequence of Fourier coefficients `γ(h) = ∫ e_h dF` of a finite measure `F` on the
circle. -/
theorem herg_exists [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) :
    ∃ F : Measure (AddCircle T), IsFiniteMeasure F ∧ ∀ h, γ h = ∫ x, fourier h x ∂F := by
  refine ⟨RealRMK.rieszMeasure (hergLambda (T := T) γ hpd), inferInstance, fun h => ?_⟩
  set μ := RealRMK.rieszMeasure (hergLambda (T := T) γ hpd)
  let gr : C_c(AddCircle T, ℝ) := ⟨⟨fun x => (fourier h x).re, by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩
  let gi : C_c(AddCircle T, ℝ) := ⟨⟨fun x => (fourier h x).im, by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩
  have hint : Integrable (fun x => fourier h x) μ :=
    herg_integrable μ (fourier (T := T) h).continuous
  have hre : (∫ x, fourier h x ∂μ).re = (γ h).re := by
    rw [herg_re_integral hint]
    have := RealRMK.integral_rieszMeasure (hergLambda (T := T) γ hpd) gr
    change ∫ x, (fourier h x).re ∂μ = _ at this
    rw [this]
    change (hergLim γ (hergOfReal ⟨fun x => (fourier h x).re, by fun_prop⟩)).re = _
    refine tendsto_nhds_unique ((continuous_re.tendsto _).comp (herg_tendsto_lim hpd _)) ?_
    simp only [Function.comp_def, herg_L_re hpd]
    exact (continuous_re.tendsto _).comp (herg_fejer_tendsto γ h)
  have him : (∫ x, fourier h x ∂μ).im = (γ h).im := by
    rw [herg_im_integral hint]
    have := RealRMK.integral_rieszMeasure (hergLambda (T := T) γ hpd) gi
    change ∫ x, (fourier h x).im ∂μ = _ at this
    rw [this]
    change (hergLim γ (hergOfReal ⟨fun x => (fourier h x).im, by fun_prop⟩)).re = _
    refine tendsto_nhds_unique ((continuous_re.tendsto _).comp (herg_tendsto_lim hpd _)) ?_
    simp only [Function.comp_def, herg_L_im hpd]
    exact (continuous_im.tendsto _).comp (herg_fejer_tendsto γ h)
  exact (Complex.ext hre him).symm

/-- AKMM, pp. 412–413 (beyond the text). **The converse half of the Herglotz theorem.** The Fourier
coefficients of a finite measure on the circle are positive definite: `Σⱼₖ cⱼc̄ₖγ(j − k) = ∫ |Σⱼ
cⱼeⱼ|² dF ≥ 0`. -/
theorem herg_posDef_of_measure [Fact (0 < T)] (F : Measure (AddCircle T)) [IsFiniteMeasure F]
    {γ : ℤ → ℂ} (hγ : ∀ h, γ h = ∫ x, fourier h x ∂F) : hergPosDef γ := by
  intro s c
  have key : ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k) =
      ((∫ x, Complex.normSq (∑ j ∈ s, c j * fourier j x) ∂F : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have e : ∀ x : AddCircle T, ((Complex.normSq (∑ j ∈ s, c j * fourier j x) : ℝ) : ℂ) =
        ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * fourier (j - k) x := by
      intro x
      rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, ← fourier_neg, sub_eq_add_neg, fourier_add]
      ring
    simp_rw [e, hγ]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (herg_integrable F (fourier (T := T) (j - k)).continuous).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ =>
      (herg_integrable F (fourier (T := T) (j - k)).continuous).const_mul _]
    exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
  rw [key, ofReal_im, ofReal_re]
  exact ⟨rfl, integral_nonneg fun x => Complex.normSq_nonneg _⟩

/-- A finite measure on the circle integrates every continuous function as its Fourier
coefficients dictate: two finite measures with the same Fourier coefficients have the same
integrals of all continuous functions (density of trigonometric polynomials). -/
theorem herg_integral_eq_of_coeff [Fact (0 < T)] {F G : Measure (AddCircle T)} [IsFiniteMeasure F]
    [IsFiniteMeasure G] (hFG : ∀ h, ∫ x, fourier h x ∂F = ∫ x, fourier h x ∂G)
    (A : C(AddCircle T, ℂ)) : ∫ x, A x ∂F = ∫ x, A x ∂G := by
  have hspan : ∀ b ∈ Submodule.span ℂ (Set.range (fourier (T := T))),
      ∫ x, b x ∂F = ∫ x, b x ∂G := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact hFG m
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [ContinuousMap.add_apply]
      rw [integral_add (herg_integrable F x.continuous) (herg_integrable F y.continuous),
        integral_add (herg_integrable G x.continuous) (herg_integrable G y.continuous), hx, hy]
    | smul c x _ hx =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hx]
  have hA : A ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  refine eq_of_forall_dist_le fun ε hε => ?_
  set C := F.real Set.univ + G.real Set.univ + 1
  have hC : 0 < C := by positivity
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hA (ε / C) (by positivity)
  have hbd : ∀ (μ : Measure (AddCircle T)) [IsFiniteMeasure μ],
      ‖∫ x, A x ∂μ - ∫ x, b x ∂μ‖ ≤ ε / C * μ.real Set.univ := by
    intro μ _
    rw [← integral_sub (herg_integrable μ A.continuous) (herg_integrable μ b.continuous)]
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x => ?_)
    have := (A - b).norm_coe_le_norm x
    rw [← dist_eq_norm] at this
    simp only [ContinuousMap.sub_apply] at this
    exact this.trans hdist.le
  rw [dist_eq_norm, show ∫ x, A x ∂F - ∫ x, A x ∂G =
    (∫ x, A x ∂F - ∫ x, b x ∂F) - (∫ x, A x ∂G - ∫ x, b x ∂G) by rw [hspan b hb]; ring]
  calc ‖(∫ x, A x ∂F - ∫ x, b x ∂F) - (∫ x, A x ∂G - ∫ x, b x ∂G)‖
      ≤ ε / C * F.real Set.univ + ε / C * G.real Set.univ :=
        (norm_sub_le _ _).trans (add_le_add (hbd F) (hbd G))
    _ ≤ ε / C * C := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε := by field_simp

/-- AKMM, pp. 412–413 (beyond the text). **Uniqueness in the Herglotz theorem.** Two finite measures
on the circle with the same Fourier coefficients are equal. -/
theorem herg_unique [Fact (0 < T)] {F G : Measure (AddCircle T)} [IsFiniteMeasure F]
    [IsFiniteMeasure G] (hFG : ∀ h, ∫ x, fourier h x ∂F = ∫ x, fourier h x ∂G) : F = G := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have := herg_integral_eq_of_coeff hFG ⟨fun x => (f x : ℂ), by fun_prop⟩
  simp only [ContinuousMap.coe_mk] at this
  exact_mod_cast this

/-- AKMM, pp. 412–413 (beyond the text). **The Herglotz theorem.** `γ : ℤ → ℂ` is positive definite
if and only if `γ(h) = ∫ e^{2πihx/T} dF(x)` for a finite (positive) measure `F` on the circle
`ℝ/Tℤ`; for `T = 2π` this is `γ(h) = ∫_{(−π,π]} e^{ihω} dF(ω)`. The measure is unique
(`herg_unique`). -/
theorem herg_herglotz [Fact (0 < T)] (γ : ℤ → ℂ) :
    hergPosDef γ ↔ ∃ F : Measure (AddCircle T), IsFiniteMeasure F ∧
      ∀ h, γ h = ∫ x, fourier h x ∂F :=
  ⟨herg_exists, fun ⟨F, _, hF⟩ => herg_posDef_of_measure F hF⟩

/-- The Fourier coefficients of a finite measure are Hermitian: `γ(−h) = conj γ(h)`. -/
theorem herg_conj [Fact (0 < T)] (F : Measure (AddCircle T)) {γ : ℤ → ℂ}
    (hγ : ∀ h, γ h = ∫ x, fourier h x ∂F) (h : ℤ) : γ (-h) = conj (γ h) := by
  rw [hγ, hγ]
  simp_rw [fourier_neg]
  exact integral_conj

/-- For a real-valued (hence even) positive definite `γ` the spectral measure is symmetric:
`F(−A) = F(A)`. -/
theorem herg_symm_of_real [Fact (0 < T)] (F : Measure (AddCircle T)) [IsFiniteMeasure F]
    {γ : ℤ → ℂ} (hγ : ∀ h, γ h = ∫ x, fourier h x ∂F) (hreal : ∀ h, (γ h).im = 0) :
    F.map (fun x => -x) = F := by
  refine herg_unique fun h => ?_
  rw [integral_map measurable_neg.aemeasurable (fourier h).continuous.aestronglyMeasurable]
  have e : ∀ x : AddCircle T, fourier h (-x) = fourier (-h) x := fun x => by
    simp [fourier_apply, neg_smul, smul_neg]
  simp_rw [e]
  rw [← hγ, ← hγ, herg_conj F hγ, Complex.conj_eq_iff_im.2 (hreal h)]

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Spectral measures of weakly stationary processes

AKMM, §14.3.1, pp. 412–413 and Appendix 14.A, p. 863 (beyond the text: the book assumes the
spectrum exists).

* Weakly stationary processes (`sdenStationary`): `X : ℤ → H` in a complex Hilbert space (for
  example mean-zero `L²(Ω, ℂ)`) with `⟪Xₜ, Xₜ₊ₕ⟫ = E[Xₜ₊ₕX̄ₜ] = γ(h)` for all `t`. The
  autocovariance is positive definite (`sden_posDef`), so the process has a unique spectral
  measure `F` with `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF` (`sden_spectral`, by `herg_exists`).
* **The spectral density** (`sden_density`): if `Σ|γ(h)| < ∞`, `F` has the continuous density
  `f = (1/T)Σₕγ(h)e_{−h} ≥ 0` (real) with respect to Lebesgue measure on the circle (`sdenMeasure`);
  for `T = 2π` this is the book's `s(ω) = (1/2π)Σₖγₖe^{−ikω}`. The proof: the Fourier
  coefficients of the series are `γ` (`sden_coeff`, termwise integration), the series is the
  pointwise limit of the Fejér densities and so real and nonnegative (`sden_series_nonneg`,
  Tannery's theorem), and uniqueness.
* **AR(1)** (`sdenAR1`, `γ(h) = ρ^{|h|}/(1 − ρ²)`, `|ρ| < 1`): absolutely summable
  (`sden_ar1_summable`); the spectrum in closed form `1/((1 − ρe_{−1})(1 − ρe₁)) = 1/|1 − ρe_{−1}|²`
  (`sden_ar1_series`, `sden_ar1_eq_normSq`), `= 1/(1 − 2ρ cos θ + ρ²)` (`sden_ar1_normSq_cos`), so
  the spectral density is `1/(2π(1 − 2ρ cos ω + ρ²))` for `T = 2π`; the spectral measure
  (`sden_ar1_measure`, `sden_ar1_coeff`) and positive definiteness (`sden_ar1_posDef`).
* Concrete processes: white noise `εₜ = eₜ ∈ L²(Haar)` (`sden_white_noise`) and the AR(1) process
  `Xₜ = eₜ/(1 − ρe_{−1}) ∈ L²(Haar)` (`sdenAR1Proc`), which satisfies `Xₜ = ρXₜ₋₁ + εₜ`
  (`sden_ar1_recursion`) and is weakly stationary with autocovariance `ρ^{|h|}/(1 − ρ²)`
  (`sden_ar1_stationary`).
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory AddCircle Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {T : ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A weakly stationary process `X : ℤ → H` in a complex Hilbert space (e.g. mean-zero
`L²(Ω, ℂ)`) with autocovariance `γ`: `⟪X_t, X_{t+h}⟫ = E[X_{t+h} X̄_t] = γ(h)` for all `t`. -/
def sdenStationary (X : ℤ → H) (γ : ℤ → ℂ) : Prop :=
  ∀ t h, ⟪X t, X (t + h)⟫_ℂ = γ h

/-- The autocovariance of a weakly stationary process is positive definite:
`Σⱼₖ cⱼc̄ₖγ(j − k) = ‖Σⱼ cⱼXⱼ‖²`. -/
theorem sden_posDef {X : ℤ → H} {γ : ℤ → ℂ} (hX : sdenStationary X γ) : hergPosDef γ := by
  intro s c
  have key : ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k) =
      ⟪∑ k ∈ s, c k • X k, ∑ j ∈ s, c j • X j⟫_ℂ := by
    rw [sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← hX j (k - j), add_sub_cancel]
    ring
  rw [key]
  exact ⟨by simpa using inner_self_im (𝕜 := ℂ) (∑ j ∈ s, c j • X j),
    by simpa using inner_self_nonneg (𝕜 := ℂ) (x := ∑ j ∈ s, c j • X j)⟩

/-- AKMM, pp. 412–413 (beyond the text). **Every weakly stationary process has a spectral
measure** (Herglotz):
`⟪X_s, X_t⟫ = ∫ e_{t−s} dF` for a finite measure `F` on the circle, unique by `herg_unique`. -/
theorem sden_spectral [Fact (0 < T)] {X : ℤ → H} {γ : ℤ → ℂ} (hX : sdenStationary X γ) :
    ∃ F : Measure (AddCircle T), IsFiniteMeasure F ∧
      (∀ h, γ h = ∫ x, fourier h x ∂F) ∧ ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F := by
  obtain ⟨F, hF, hγ⟩ := herg_exists (T := T) (sden_posDef hX)
  refine ⟨F, hF, hγ, fun s t => ?_⟩
  rw [← hγ, ← hX s (t - s), add_sub_cancel]

theorem sden_norm_fourier (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

/-- `∫ eₘe_{−h} dHaar = δₘₕ`. -/
theorem sden_integral_fourier_mul [Fact (0 < T)] (m h : ℤ) :
    ∫ x, fourier m x * fourier (-h) x ∂(haarAddCircle (T := T)) = if m = h then 1 else 0 := by
  simp_rw [← fourier_add]
  rw [herg_integral_fourier]
  rcases eq_or_ne m h with rfl | hmh
  · simp
  · have : m + -h ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.2 hmh
    simp [this, hmh]

/-- The series `Σₕ γ(h)e_{−h}(x)`, i.e. `T` times the spectral density
(`s(ω) = (1/2π)Σₖγₖe^{−ikω}` for `T = 2π`, AKMM p. 863). -/
noncomputable def sdenSeries (γ : ℤ → ℂ) (x : AddCircle T) : ℂ :=
  ∑' h, γ h * fourier (-h) x

theorem sden_series_continuous {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖) :
    Continuous (sdenSeries (T := T) γ) :=
  continuous_tsum (fun h => continuous_const.mul (fourier (-h)).continuous) hs
    (fun h x => by rw [norm_mul, sden_norm_fourier, mul_one])

/-- The Fourier coefficients of the series are `γ`: `∫ eₘ(Σₕγ(h)e_{−h}) dHaar = γ(m)`
(the inversion formula of AKMM p. 863 on the circle, complex `γ`). -/
theorem sden_coeff [Fact (0 < T)] {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖) (m : ℤ) :
    ∫ x, fourier m x * sdenSeries (T := T) γ x ∂haarAddCircle = γ m := by
  unfold sdenSeries
  simp_rw [← tsum_mul_left]
  have hterm : ∀ h, ∫ x, fourier m x * (γ h * fourier (-h) x) ∂(haarAddCircle (T := T)) =
      if m = h then γ h else 0 := by
    intro h
    simp_rw [mul_left_comm (fourier m _)]
    rw [integral_const_mul, sden_integral_fourier_mul]
    split_ifs <;> simp
  rw [← integral_tsum_of_summable_integral_norm]
  · simp_rw [hterm]
    rw [tsum_eq_single m fun b hb => by simp [Ne.symm hb]]
    simp
  · exact fun h => herg_integrable _ (by fun_prop)
  · refine hs.congr fun h => ?_
    simp_rw [norm_mul, sden_norm_fourier, one_mul, mul_one]
    simp

/-- For positive definite, absolutely summable `γ`, the series `Σₕγ(h)e_{−h}(x)` is real and
nonnegative: it is the pointwise limit of the Fejér densities (Tannery's theorem). -/
theorem sden_series_nonneg {γ : ℤ → ℂ} (hpd : hergPosDef γ) (hs : Summable fun h => ‖γ h‖)
    (x : AddCircle T) : (sdenSeries γ x).im = 0 ∧ 0 ≤ (sdenSeries γ x).re := by
  set f : ℕ → ℤ → ℂ := fun n h => if h ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) then
    (((((n + 1 : ℕ) : ℝ) - |(h : ℝ)|) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * γ h * fourier (-h) x
    else 0 with hf
  have hfej : ∀ n, ∑' h, f n h = hergFejer γ (n + 1) x := by
    intro n
    rw [tsum_eq_sum (s := Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ))
      fun b hb => by simp only [hf, hb, ↓reduceIte]]
    unfold hergFejer
    exact Finset.sum_congr rfl fun h hh => by simp only [hf, hh, ↓reduceIte]
  have hlim : Tendsto (fun n => ∑' h, f n h) atTop (𝓝 (sdenSeries γ x)) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun h => ?_) (Eventually.of_forall
      fun n h => ?_)
    · have hev : (fun n : ℕ => ((1 - |(h : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) *
          (γ h * fourier (-h) x)) =ᶠ[atTop] fun n => f n h := by
        filter_upwards [eventually_gt_atTop h.natAbs] with n hn
        have hmem : h ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
          rw [Finset.mem_Ioo]
          omega
        simp only [hf, hmem, ↓reduceIte]
        rw [mul_assoc]
        congr 1
        push_cast
        field_simp
      have hl : Tendsto (fun n : ℕ => (1 - |(h : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ)) atTop
          (𝓝 1) := by
        simpa using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |(h : ℝ)|)
      have := ((continuous_ofReal.tendsto 1).comp hl).mul_const (γ h * fourier (-h) x)
      simp only [ofReal_one, one_mul] at this
      exact this.congr' hev
    · simp only [hf]
      split_ifs with hh
      · rw [norm_mul, norm_mul, sden_norm_fourier, mul_one, Complex.norm_real, Real.norm_eq_abs]
        rw [Finset.mem_Ioo] at hh
        have h1 : |(h : ℝ)| < ((n + 1 : ℕ) : ℝ) := by
          rw [abs_lt]
          constructor <;> push_cast <;> [linarith [(by exact_mod_cast hh.1 :
            (-((n : ℝ) + 1)) < h)]; linarith [(by exact_mod_cast hh.2 : (h : ℝ) < (n : ℝ) + 1)]]
        have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have h2 : 0 ≤ (((n + 1 : ℕ) : ℝ) - |(h : ℝ)|) / ((n + 1 : ℕ) : ℝ) :=
          div_nonneg (by linarith) hN.le
        have h3 : (((n + 1 : ℕ) : ℝ) - |(h : ℝ)|) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one hN]
          linarith [abs_nonneg (h : ℝ)]
        rw [abs_of_nonneg h2]
        exact mul_le_of_le_one_left (norm_nonneg _) h3
      · simp
  simp_rw [hfej] at hlim
  have hK : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
  exact hK.mem_of_tendsto hlim (Eventually.of_forall fun n => herg_fejer_nonneg hpd (n + 1) x)

/-- The measure `F(dx) = f(x)dx` with density `f = Re(Σₕγ(h)e_{−h})/T` with respect to Lebesgue
measure on the circle (for `T = 2π`: `s(ω)dω`, `s(ω) = (1/2π)Σₖγₖe^{−ikω}`, AKMM p. 863). -/
noncomputable def sdenMeasure [Fact (0 < T)] (γ : ℤ → ℂ) : Measure (AddCircle T) :=
  (volume : Measure (AddCircle T)).withDensity fun x => ENNReal.ofReal ((sdenSeries γ x).re / T)

theorem sden_measure_finite [Fact (0 < T)] {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖) :
    IsFiniteMeasure (sdenMeasure (T := T) γ) :=
  isFiniteMeasure_withDensity_ofReal
    (((continuous_re.comp (sden_series_continuous hs)).div_const T).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

/-- If the series is real and nonnegative, the density measure has Fourier coefficients `γ`. -/
theorem sden_measure_coeff [hT : Fact (0 < T)] {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖)
    (hnn : ∀ x : AddCircle T, (sdenSeries γ x).im = 0 ∧ 0 ≤ (sdenSeries γ x).re) (m : ℤ) :
    ∫ x, fourier m x ∂(sdenMeasure (T := T) γ) = γ m := by
  unfold sdenMeasure
  have hmeas : Measurable fun x : AddCircle T => (sdenSeries γ x).re / T :=
    ((continuous_re.comp (sden_series_continuous hs)).div_const T).measurable
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal ((sdenSeries γ x).re / T))
    (ENNReal.measurable_ofReal.comp hmeas) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ x : AddCircle T, (ENNReal.ofReal ((sdenSeries γ x).re / T)).toReal • fourier m x =
      T⁻¹ • (fourier m x * sdenSeries γ x) := by
    intro x
    rw [ENNReal.toReal_ofReal (div_nonneg (hnn x).2 hT.out.le)]
    have hx : sdenSeries γ x = ((sdenSeries γ x).re : ℂ) :=
      Complex.ext (by simp) (by simp [(hnn x).1])
    conv_rhs => rw [hx]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  simp_rw [e]
  rw [integral_smul, ← integral_haarAddCircle, sden_coeff hs]

/-- AKMM, p. 863 (the spectrum, made precise). **The spectral density.** If `γ` is positive definite
and `Σ|γ(h)| < ∞`, its spectral measure `F` has the continuous density `f(x) = (1/T)Σₕγ(h)e_{−h}(x)
≥ 0` (real) with respect to Lebesgue measure on the circle; for `T = 2π`, `f(ω) =
(1/2π)Σₕγ(h)e^{−ihω}`. -/
theorem sden_density [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ)
    (hs : Summable fun h => ‖γ h‖) (F : Measure (AddCircle T)) [IsFiniteMeasure F]
    (hF : ∀ h, γ h = ∫ x, fourier h x ∂F) :
    F = sdenMeasure γ ∧ Continuous (fun x => (sdenSeries (T := T) γ x).re / T) ∧
      ∀ x : AddCircle T, (sdenSeries γ x).im = 0 ∧ 0 ≤ (sdenSeries γ x).re / T := by
  have := sden_measure_finite (T := T) hs
  refine ⟨herg_unique fun h => ?_, (continuous_re.comp (sden_series_continuous hs)).div_const T,
    fun x => ⟨(sden_series_nonneg hpd hs x).1,
      div_nonneg (sden_series_nonneg hpd hs x).2 (Fact.out : 0 < T).le⟩⟩
  rw [← hF, sden_measure_coeff hs (sden_series_nonneg hpd hs)]

/-- The autocovariance `γ(h) = ρ^{|h|}/(1 − ρ²)` of the AR(1) process `Xₜ = ρXₜ₋₁ + εₜ` with
unit-variance white noise. -/
noncomputable def sdenAR1 (ρ : ℝ) (h : ℤ) : ℂ :=
  ((ρ ^ h.natAbs / (1 - ρ ^ 2) : ℝ) : ℂ)

theorem sden_ar1_summable {ρ : ℝ} (hρ : |ρ| < 1) : Summable fun h => ‖sdenAR1 ρ h‖ := by
  have hd : 0 < 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
  have e : ∀ h : ℤ, ‖sdenAR1 ρ h‖ = |ρ| ^ h.natAbs / (1 - ρ ^ 2) := fun h => by
    rw [sdenAR1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hd]
  simp_rw [e]
  have hg : Summable fun n : ℕ => |ρ| ^ n / (1 - ρ ^ 2) :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).div_const _
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hg
  · have : (fun n : ℕ => |ρ| ^ (-((n : ℤ) + 1)).natAbs / (1 - ρ ^ 2)) =
        fun n => |ρ| ^ (n + 1) / (1 - ρ ^ 2) := by
      funext n
      congr 2
    rw [this]
    exact (summable_nat_add_iff 1).2 hg

theorem sden_fourier_mul_nat (k : ℤ) (n : ℕ) (x : AddCircle T) :
    fourier (k * n) x = fourier k x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, mul_add, mul_one, fourier_add, ih, pow_succ]

theorem sden_one_sub_ne_zero {ρ : ℝ} (hρ : |ρ| < 1) (n : ℤ) (x : AddCircle T) :
    1 - (ρ : ℂ) * fourier n x ≠ 0 := by
  intro h
  have : ‖(ρ : ℂ) * fourier n x‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
  rw [norm_mul, sden_norm_fourier, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  linarith

theorem sden_ar1_alg {r z w : ℂ} (hzw : z * w = 1) (hd : 1 - r ^ 2 ≠ 0) (hw0 : 1 - r * w ≠ 0)
    (hz0 : 1 - r * z ≠ 0) :
    (1 - r ^ 2)⁻¹ * (1 - r * w)⁻¹ + (1 - r ^ 2)⁻¹ * (r * z) * (1 - r * z)⁻¹ =
      ((1 - r * w) * (1 - r * z))⁻¹ := by
  field_simp
  linear_combination (-r ^ 2) * hzw

/-- AKMM, p. 863, for the AR(1). **The AR(1) spectrum in closed form.** For `|ρ| < 1`,
`Σₕρ^{|h|}e_{−h}(x)/(1 − ρ²) = 1/((1 − ρe_{−1}(x))(1 − ρe₁(x))) = 1/|1 − ρe^{−iω}|²`. -/
theorem sden_ar1_series {ρ : ℝ} (hρ : |ρ| < 1) (x : AddCircle T) :
    sdenSeries (sdenAR1 ρ) x = ((1 - ρ * fourier (-1) x) * (1 - ρ * fourier 1 x))⁻¹ := by
  have hzw : fourier (T := T) 1 x * fourier (-1) x = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  have hn : ∀ n : ℤ, ‖(ρ : ℂ) * fourier (T := T) n x‖ < 1 := fun n => by
    rw [norm_mul, sden_norm_fourier, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hρ
  have hd : (1 - (ρ : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
    exact_mod_cast this.ne'
  have h1 : HasSum (fun n : ℕ => sdenAR1 ρ n * fourier (-(n : ℤ)) x)
      ((1 - (ρ : ℂ) ^ 2)⁻¹ * (1 - ρ * fourier (-1) x)⁻¹) := by
    have e : (fun n : ℕ => sdenAR1 ρ n * fourier (-(n : ℤ)) x) =
        fun n : ℕ => (1 - (ρ : ℂ) ^ 2)⁻¹ * ((ρ : ℂ) * fourier (-1) x) ^ n := by
      funext n
      rw [show -(n : ℤ) = -1 * n by ring, sden_fourier_mul_nat, sdenAR1, Int.natAbs_natCast]
      push_cast
      ring
    rw [e]
    exact (hasSum_geometric_of_norm_lt_one (hn (-1))).mul_left _
  have h2 : HasSum (fun n : ℕ => sdenAR1 ρ (-((n : ℤ) + 1)) * fourier (-(-((n : ℤ) + 1))) x)
      ((1 - (ρ : ℂ) ^ 2)⁻¹ * (ρ * fourier 1 x) * (1 - ρ * fourier 1 x)⁻¹) := by
    have e : (fun n : ℕ => sdenAR1 ρ (-((n : ℤ) + 1)) * fourier (-(-((n : ℤ) + 1))) x) =
        fun n : ℕ => (1 - (ρ : ℂ) ^ 2)⁻¹ * ((ρ : ℂ) * fourier 1 x) *
          ((ρ : ℂ) * fourier 1 x) ^ n := by
      funext n
      have ha : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [neg_neg, show (n : ℤ) + 1 = 1 * ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        sden_fourier_mul_nat, sdenAR1, show 1 * ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring,
        ha]
      push_cast
      ring
    rw [e]
    exact (hasSum_geometric_of_norm_lt_one (hn 1)).mul_left _
  rw [sdenSeries, (HasSum.of_nat_of_neg_add_one
    (f := fun h : ℤ => sdenAR1 ρ h * fourier (-h) x) h1 h2).tsum_eq]
  exact sden_ar1_alg hzw hd (sden_one_sub_ne_zero hρ (-1) x) (sden_one_sub_ne_zero hρ 1 x)

/-- The AR(1) spectral density in the book's form: with `x = ω ∈ ℝ` and `θ = 2πω/T`
(`θ = ω` for `T = 2π`), `(1 − ρe^{−iθ})(1 − ρe^{iθ}) = 1 − 2ρ cos θ + ρ²`. -/
theorem sden_ar1_cos (ρ ω : ℝ) :
    (1 - ρ * fourier (-1) (ω : AddCircle T)) * (1 - ρ * fourier 1 (ω : AddCircle T)) =
      ((1 - 2 * ρ * Real.cos (2 * Real.pi * ω / T) + ρ ^ 2 : ℝ) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  set θ : ℝ := 2 * Real.pi * ω / T
  have e1 : 2 * (Real.pi : ℂ) * I * ((-1 : ℤ) : ℂ) * ω / T = -(θ : ℂ) * I := by
    simp only [θ]; push_cast; ring
  have e2 : 2 * (Real.pi : ℂ) * I * ((1 : ℤ) : ℂ) * ω / T = (θ : ℂ) * I := by
    simp only [θ]; push_cast; ring
  rw [e1, e2]
  have hc := Complex.two_cos (θ : ℂ)
  have hp : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  push_cast
  rw [← Complex.ofReal_cos] at hc ⊢
  linear_combination (ρ : ℂ) ^ 2 * hp + (ρ : ℂ) * hc

theorem sden_conj_one_sub (ρ : ℝ) (x : AddCircle T) :
    conj (1 - (ρ : ℂ) * fourier (-1) x) = 1 - ρ * fourier 1 x := by
  rw [map_sub, map_one, map_mul, Complex.conj_ofReal, ← fourier_neg, neg_neg]

/-- The AR(1) spectrum is `1/|1 − ρe_{−1}(x)|²`, real and positive. -/
theorem sden_ar1_eq_normSq {ρ : ℝ} (hρ : |ρ| < 1) (x : AddCircle T) :
    sdenSeries (sdenAR1 ρ) x = (((Complex.normSq (1 - ρ * fourier (-1) x))⁻¹ : ℝ) : ℂ) := by
  rw [sden_ar1_series hρ, ← sden_conj_one_sub, Complex.mul_conj, ofReal_inv]

/-- AKMM p. 863 for the AR(1): with `x = ω` and `θ = 2πω/T`, `|1 − ρe^{−iθ}|² = 1 − 2ρ cos θ + ρ²`,
so the AR(1) spectral density is `1/(T(1 − 2ρ cos θ + ρ²))` (`1/(2π(1 − 2ρ cos ω + ρ²))`
for `T = 2π`). -/
theorem sden_ar1_normSq_cos (ρ ω : ℝ) :
    Complex.normSq (1 - ρ * fourier (-1) (ω : AddCircle T)) =
      1 - 2 * ρ * Real.cos (2 * Real.pi * ω / T) + ρ ^ 2 := by
  have := sden_ar1_cos (T := T) ρ ω
  rw [← sden_conj_one_sub, Complex.mul_conj] at this
  exact_mod_cast this

theorem sden_ar1_nonneg {ρ : ℝ} (hρ : |ρ| < 1) (x : AddCircle T) :
    (sdenSeries (sdenAR1 ρ) x).im = 0 ∧ 0 ≤ (sdenSeries (sdenAR1 ρ) x).re := by
  rw [sden_ar1_eq_normSq hρ, ofReal_im, ofReal_re]
  exact ⟨rfl, inv_nonneg.2 (Complex.normSq_nonneg _)⟩

/-- The AR(1) spectral measure: density `1/(T|1 − ρe_{−1}(x)|²)` with respect to Lebesgue
measure on the circle. -/
theorem sden_ar1_measure [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) :
    sdenMeasure (T := T) (sdenAR1 ρ) = (volume : Measure (AddCircle T)).withDensity
      fun x => ENNReal.ofReal ((Complex.normSq (1 - ρ * fourier (-1) x))⁻¹ / T) := by
  unfold sdenMeasure
  simp_rw [sden_ar1_eq_normSq hρ, ofReal_re]

/-- The AR(1) autocovariance `ρ^{|h|}/(1 − ρ²)` is the sequence of Fourier coefficients of its
spectral measure, hence positive definite (Herglotz). -/
theorem sden_ar1_coeff [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) (h : ℤ) :
    ∫ x, fourier h x ∂(sdenMeasure (T := T) (sdenAR1 ρ)) = sdenAR1 ρ h :=
  sden_measure_coeff (sden_ar1_summable hρ) (sden_ar1_nonneg hρ) h

theorem sden_ar1_posDef [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) : hergPosDef (sdenAR1 ρ) := by
  have := sden_measure_finite (T := T) (sden_ar1_summable hρ)
  exact herg_posDef_of_measure (sdenMeasure (T := T) (sdenAR1 ρ))
    fun h => (sden_ar1_coeff hρ h).symm

/-- **White noise**: the exponentials `eₜ ∈ L²(Haar)` are a weakly stationary process with
`γ(0) = 1`, `γ(h) = 0` for `h ≠ 0` (orthonormality); its spectral measure is Haar measure,
density `1/T` (`1/2π`). -/
theorem sden_white_noise [Fact (0 < T)] :
    sdenStationary (fourierLp (T := T) 2) (fun h => if h = 0 then 1 else 0) := by
  intro t h
  rw [orthonormal_iff_ite.1 orthonormal_fourier]
  simp

/-- `φ(x) = 1/(1 − ρe_{−1}(x)) = Σⱼρʲe_{−j}(x)`, the transfer function of the AR(1) filter. -/
noncomputable def sdenPhi (ρ : ℝ) (hρ : |ρ| < 1) : C(AddCircle T, ℂ) :=
  ⟨fun x => (1 - ρ * fourier (-1) x)⁻¹,
    (continuous_const.sub (continuous_const.mul (fourier (-1)).continuous)).inv₀
      fun x => sden_one_sub_ne_zero hρ (-1) x⟩

/-- The AR(1) process `Xₜ = eₜφ ∈ L²(Haar)` driven by the white noise `εₜ = eₜ`. -/
noncomputable def sdenAR1Proc [Fact (0 < T)] (ρ : ℝ) (hρ : |ρ| < 1) (t : ℤ) :
    MeasureTheory.Lp ℂ 2 (haarAddCircle (T := T)) :=
  ContinuousMap.toLp 2 haarAddCircle ℂ (fourier t * sdenPhi ρ hρ)

/-- The AR(1) recursion `Xₜ = ρXₜ₋₁ + εₜ`. -/
theorem sden_ar1_recursion [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) (t : ℤ) :
    sdenAR1Proc (T := T) ρ hρ t = (ρ : ℂ) • sdenAR1Proc ρ hρ (t - 1) + fourierLp 2 t := by
  unfold sdenAR1Proc
  rw [← map_smul, ← map_add]
  congr 1
  ext x
  have hne := sden_one_sub_ne_zero hρ (-1) x
  simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply, sdenPhi,
    ContinuousMap.coe_mk, smul_eq_mul, sub_eq_add_neg t 1, fourier_add]
  field_simp
  ring

/-- The AR(1) process is weakly stationary with autocovariance `ρ^{|h|}/(1 − ρ²)`. -/
theorem sden_ar1_stationary [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) :
    sdenStationary (sdenAR1Proc (T := T) ρ hρ) (sdenAR1 ρ) := by
  intro t h
  unfold sdenAR1Proc
  rw [ContinuousMap.inner_toLp]
  have e : ∀ x : AddCircle T, (fourier (t + h) * sdenPhi ρ hρ : C(AddCircle T, ℂ)) x *
      conj ((fourier t * sdenPhi ρ hρ : C(AddCircle T, ℂ)) x) =
        fourier h x * sdenSeries (sdenAR1 ρ) x := by
    intro x
    have hc : fourier t x * fourier (-t) x = 1 := by
      rw [← fourier_add, add_neg_cancel, fourier_zero]
    rw [sden_ar1_series hρ]
    simp only [ContinuousMap.mul_apply, sdenPhi, ContinuousMap.coe_mk, map_mul, map_inv₀,
      sden_conj_one_sub, ← fourier_neg, fourier_add, mul_inv]
    linear_combination (fourier h x * (1 - ρ * fourier (-1) x)⁻¹ * (1 - ρ * fourier 1 x)⁻¹) * hc
  simp_rw [e]
  exact sden_coeff (sden_ar1_summable hρ) h

end AKMM.RealBusinessCycles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral representation

AKMM, §14.3.1, pp. 412–413 (a result beyond the text): the spectral representation theorem
(Cramér) in its Hilbert-space form.

Let `X : ℤ → H` (a complex Hilbert space) satisfy `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF` for a finite measure
`F` on the circle, as every weakly stationary process does (`sden_spectral`).

* The exponentials `eₜ ∈ L²(F)` (`cramExp`) have the same Gram matrix (`cram_inner_exp`) and span a
  dense subspace (`cram_dense`), so `eₜ ↦ Xₜ` extends to a linear isometry
  `V : L²(F) → H` (**the Kolmogorov isometry**, `cramIso`, `cram_iso_exp`, `cram_iso_inner`),
  unique (`cram_iso_unique`), whose range is the closed linear span `H_X` of the process
  (`cram_iso_range`).
* The random measure `Z(A) = V(1_A)` (`cramZ`) has orthogonal increments:
  `⟪Z(A), Z(B)⟫ = F(A ∩ B)` (`cram_Z_inner`), `‖Z(A)‖² = F(A)` (`cram_Z_norm_sq`), `Z(A) ⊥ Z(B)`
  for disjoint `A`, `B` (`cram_Z_orth`), `Z(A ∪ B) = Z(A) + Z(B)` (`cram_Z_union`),
  `Z(𝕋) = X₀` (`cram_Z_univ`).
* `cram_spectral_representation` packages the theorem for weakly stationary processes.

In stochastic-integral notation `Xₜ = ∫ e^{itω} dZ(ω)`: the integral of a step function
`Σ aₖ1_{Aₖ}` against `Z` is `Σ aₖZ(Aₖ) = V(Σ aₖ1_{Aₖ})`, and `V` is its isometric extension to
`L²(F)`, so `∫ e^{itω} dZ(ω) = V(eₜ) = Xₜ`. The notation itself is not formalised. For a real
process `F` is symmetric (`herg_symm_of_real`), and pairing `ω` with `−ω` gives the book's real
form `Yₜ = ∫_{[0,π]} cos(ωt) dU(ω) + ∫_{(0,π]} sin(ωt) dW(ω)` with orthogonal real random
measures `U`, `W`; the book's `A(ω)dω`, `B(ω)dω` stand for `dU`, `dW` (which are given by
densities only in special cases).
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory AddCircle Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {T : ℝ} [Fact (0 < T)] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exponential `eₜ(x) = e^{2πitx/T}` as an element of `L²(F)`. -/
noncomputable def cramExp (F : Measure (AddCircle T)) [IsFiniteMeasure F] (t : ℤ) :
    Lp ℂ 2 F :=
  ContinuousMap.toLp 2 F ℂ (fourier t)

/-- `⟪eₛ, eₜ⟫_{L²(F)} = ∫ e_{t−s} dF`. -/
theorem cram_inner_exp (F : Measure (AddCircle T)) [IsFiniteMeasure F] (s t : ℤ) :
    ⟪cramExp F s, cramExp F t⟫_ℂ = ∫ x, fourier (t - s) x ∂F := by
  unfold cramExp
  rw [ContinuousMap.inner_toLp]
  congr 1
  funext x
  rw [← fourier_neg, sub_eq_add_neg, fourier_add]

/-- The exponentials span a dense subspace of `L²(F)` for every finite measure `F` on the
circle. -/
theorem cram_dense (F : Measure (AddCircle T)) [IsFiniteMeasure F] :
    (Submodule.span ℂ (Set.range (cramExp F))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange ℂ F ℂ (p := 2) (by simp)).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  rw [Submodule.map_span]
  unfold cramExp
  rw [Set.range_comp']
  simp only [ContinuousLinearMap.coe_coe]

theorem cram_denseRange (F : Measure (AddCircle T)) [IsFiniteMeasure F] :
    DenseRange (Finsupp.linearCombination ℂ (cramExp F)) := by
  have : Set.range ⇑(Finsupp.linearCombination ℂ (cramExp F)) =
      (Submodule.span ℂ (Set.range (cramExp F)) : Set (Lp ℂ 2 F)) := by
    rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
  rw [DenseRange, this, Submodule.dense_iff_topologicalClosure_eq_top]
  exact cram_dense F

/-- If `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF`, then `‖Σ cₜXₜ‖ = ‖Σ cₜeₜ‖_{L²(F)}`. -/
theorem cram_norm_eq (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (c : ℤ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ X c‖ = ‖Finsupp.linearCombination ℂ (cramExp F) c‖ := by
  have key : ⟪Finsupp.linearCombination ℂ X c, Finsupp.linearCombination ℂ X c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ (cramExp F) c,
        Finsupp.linearCombination ℂ (cramExp F) c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hX, cram_inner_exp]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

variable [CompleteSpace H]

/-- AKMM, pp. 412–413 (beyond the text). **The Kolmogorov isometry.** If `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF`,
the map `eₜ ↦ Xₜ` extends to a linear isometry `V : L²(F) → H`. -/
noncomputable def cramIso (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) : Lp ℂ 2 F →ₗᵢ[ℂ] H :=
  (Finsupp.linearCombination ℂ X).extendOfIsometry (cram_denseRange F) (cram_norm_eq F X hX)

/-- `V(eₜ) = Xₜ` for every `t`. -/
theorem cram_iso_exp (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (t : ℤ) :
    cramIso F X hX (cramExp F t) = X t := by
  have := LinearMap.extendOfIsometry_eq (f := Finsupp.linearCombination ℂ X)
    (cram_denseRange F) (cram_norm_eq F X hX) (Finsupp.single t 1)
  simp only [Finsupp.linearCombination_single, one_smul] at this
  exact this

/-- `V` preserves inner products: `⟪Vf, Vg⟫_H = ∫ ḡ… = ⟪f, g⟫_{L²(F)}`. -/
theorem cram_iso_inner (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (f g : Lp ℂ 2 F) :
    ⟪cramIso F X hX f, cramIso F X hX g⟫_ℂ = ⟪f, g⟫_ℂ :=
  LinearIsometry.inner_map_map _ _ _

/-- **Uniqueness of the Kolmogorov isometry**: it is the only linear isometry with
`V(eₜ) = Xₜ` for all `t`. -/
theorem cram_iso_unique (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (V : Lp ℂ 2 F →ₗᵢ[ℂ] H)
    (hV : ∀ t, V (cramExp F t) = X t) : V = cramIso F X hX := by
  refine (LinearMap.extendOfIsometry_unique _ (cram_denseRange F) (cram_norm_eq F X hX) V
    (Finsupp.lhom_ext fun t a => ?_)).symm
  simp [Finsupp.linearCombination_single, hV]

/-- **The range of the Kolmogorov isometry** is the closed linear span `H_X` of the process:
`V` maps `L²(F)` onto `H_X`. -/
theorem cram_iso_range (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) :
    LinearMap.range (cramIso F X hX).toLinearMap =
      (Submodule.span ℂ (Set.range X)).topologicalClosure := by
  set V := cramIso F X hX
  have hmap : (Submodule.span ℂ (Set.range (cramExp F))).map V.toLinearMap =
      Submodule.span ℂ (Set.range X) := by
    have e : (V.toLinearMap ∘ cramExp F) = X := funext fun t => cram_iso_exp F X hX t
    rw [Submodule.map_span, ← Set.range_comp, e]
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    have hf : f ∈ closure (Submodule.span ℂ (Set.range (cramExp F)) : Set (Lp ℂ 2 F)) := by
      rw [← Submodule.topologicalClosure_coe, cram_dense]
      trivial
    have h1 := image_closure_subset_closure_image V.continuous ⟨f, hf, rfl⟩
    change V f ∈ ((Submodule.span ℂ (Set.range X)).topologicalClosure : Set H)
    rw [Submodule.topologicalClosure_coe]
    refine closure_mono ?_ h1
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  · refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact ⟨cramExp F t, cram_iso_exp F X hX t⟩
    · rw [LinearMap.coe_range]
      exact V.isometry.isClosedEmbedding.isClosed_range

/-- The orthogonal-increment random measure `Z(A) = V(1_A) ∈ H` (so that, formally,
`Xₜ = ∫ e^{itω} dZ(ω)`). -/
noncomputable def cramZ (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (A : Set (AddCircle T))
    (hA : MeasurableSet A) : H :=
  cramIso F X hX (indicatorConstLp 2 hA (measure_ne_top F A) (1 : ℂ))

/-- **Orthogonal increments**: `⟪Z(A), Z(B)⟫ = F(A ∩ B)`. -/
theorem cram_Z_inner (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A B : Set (AddCircle T)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ⟪cramZ F X hX A hA, cramZ F X hX B hB⟫_ℂ = (F.real (A ∩ B) : ℂ) := by
  unfold cramZ
  rw [cram_iso_inner, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  rfl

/-- `E|Z(A)|² = ‖Z(A)‖² = F(A)`. -/
theorem cram_Z_norm_sq (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) : ‖cramZ F X hX A hA‖ ^ 2 = F.real A := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), cram_Z_inner, Set.inter_self]
  simp

/-- Increments over disjoint sets are orthogonal. -/
theorem cram_Z_orth (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A B : Set (AddCircle T)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ⟪cramZ F X hX A hA, cramZ F X hX B hB⟫_ℂ = 0 := by
  rw [cram_Z_inner, Set.disjoint_iff_inter_eq_empty.1 hAB]
  simp

/-- `Z` is additive: `Z(A ∪ B) = Z(A) + Z(B)` for disjoint `A`, `B`. -/
theorem cram_Z_union (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A B : Set (AddCircle T)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    cramZ F X hX (A ∪ B) (hA.union hB) = cramZ F X hX A hA + cramZ F X hX B hB := by
  unfold cramZ
  rw [indicatorConstLp_disjoint_union hA hB (measure_ne_top F A) (measure_ne_top F B) hAB,
    map_add]

/-- `Z(𝕋) = X₀`: the total increment is the value at time `0`. -/
theorem cram_Z_univ (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) :
    cramZ F X hX Set.univ MeasurableSet.univ = X 0 := by
  rw [← cram_iso_exp F X hX 0]
  unfold cramZ
  congr 1
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := F) (s := Set.univ)
    (hs := MeasurableSet.univ) (hμs := measure_ne_top F _) (c := (1 : ℂ)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := F) (fourier (T := T) 0)] with x h1 h2
  rw [cramExp, h1, h2, fourier_zero]
  simp

/-- AKMM, pp. 412–413 (beyond the text). **The spectral representation theorem (Cramér),
Hilbert-space form.** A weakly stationary
process `X : ℤ → H` with autocovariance `γ` has a finite spectral measure `F` on the circle, and
there is a linear isometry `V` of `L²(F)` onto the closed linear span `H_X` of the process with
`V(eₜ) = Xₜ` for all `t`; it is unique (`cram_iso_unique`) and `Z(A) = V(1_A)` has orthogonal
increments with `‖Z(A)‖² = F(A)` (`cram_Z_inner`, `cram_Z_norm_sq`). -/
theorem cram_spectral_representation {X : ℤ → H} {γ : ℤ → ℂ} (hX : sdenStationary X γ) :
    ∃ F : Measure (AddCircle T), ∃ _ : IsFiniteMeasure F, (∀ h, γ h = ∫ x, fourier h x ∂F) ∧
      ∃ V : Lp ℂ 2 F →ₗᵢ[ℂ] H, (∀ t, V (cramExp F t) = X t) ∧
        LinearMap.range V.toLinearMap = (Submodule.span ℂ (Set.range X)).topologicalClosure := by
  obtain ⟨F, hF, hγ, hXF⟩ := sden_spectral (T := T) hX
  exact ⟨F, hF, hγ, cramIso F X hXF, cram_iso_exp F X hXF, cram_iso_range F X hXF⟩

end AKMM.RealBusinessCycles

set_option linter.style.longLine false
#print axioms AKMM.RealBusinessCycles.hpD
#print axioms AKMM.RealBusinessCycles.hpA
#print axioms AKMM.RealBusinessCycles.hpFit
#print axioms AKMM.RealBusinessCycles.hpPen
#print axioms AKMM.RealBusinessCycles.hpObj
#print axioms AKMM.RealBusinessCycles.hpExt
#print axioms AKMM.RealBusinessCycles.hp_sum_ite_val
#print axioms AKMM.RealBusinessCycles.hp_pen_nonneg
#print axioms AKMM.RealBusinessCycles.hp_fit_nonneg
#print axioms AKMM.RealBusinessCycles.hp_D_apply
#print axioms AKMM.RealBusinessCycles.hpSec
#print axioms AKMM.RealBusinessCycles.hp_ext_fin
#print axioms AKMM.RealBusinessCycles.hp_A_apply
#print axioms AKMM.RealBusinessCycles.hp_A_interior
#print axioms AKMM.RealBusinessCycles.hp_A_row0
#print axioms AKMM.RealBusinessCycles.hp_A_row1
#print axioms AKMM.RealBusinessCycles.hp_A_rowLast
#print axioms AKMM.RealBusinessCycles.hp_A_rowLast1
#print axioms AKMM.RealBusinessCycles.hp_pen_eq
#print axioms AKMM.RealBusinessCycles.hp_cross
#print axioms AKMM.RealBusinessCycles.hp_M_apply
#print axioms AKMM.RealBusinessCycles.hp_obj_expand
#print axioms AKMM.RealBusinessCycles.hp_quad_pos
#print axioms AKMM.RealBusinessCycles.hp_posDef
#print axioms AKMM.RealBusinessCycles.eq_14_1
#print axioms AKMM.RealBusinessCycles.hp_unique
#print axioms AKMM.RealBusinessCycles.hp_trend_eq
#print axioms AKMM.RealBusinessCycles.hp_trend_exists
#print axioms AKMM.RealBusinessCycles.hp_bracket_eq
#print axioms AKMM.RealBusinessCycles.hp_foc_interior
#print axioms AKMM.RealBusinessCycles.hp_foc_printed_iff
#print axioms AKMM.RealBusinessCycles.hpEx
#print axioms AKMM.RealBusinessCycles.hp_foc_printed_false
#print axioms AKMM.RealBusinessCycles.hp_constrained_of_lagrangian
#print axioms AKMM.RealBusinessCycles.hp_constrained_unique
#print axioms AKMM.RealBusinessCycles.hp_pen_zero_iff
#print axioms AKMM.RealBusinessCycles.hp_ravn_uhlig
#print axioms AKMM.RealBusinessCycles.hpS1
#print axioms AKMM.RealBusinessCycles.hpS2
#print axioms AKMM.RealBusinessCycles.hpDet
#print axioms AKMM.RealBusinessCycles.hpOLSa
#print axioms AKMM.RealBusinessCycles.hpOLSb
#print axioms AKMM.RealBusinessCycles.hpOLS
#print axioms AKMM.RealBusinessCycles.hp_det_pos
#print axioms AKMM.RealBusinessCycles.hp_ols_normal
#print axioms AKMM.RealBusinessCycles.hp_pen_affine
#print axioms AKMM.RealBusinessCycles.hp_ols_pythagoras
#print axioms AKMM.RealBusinessCycles.hp_ols_affine
#print axioms AKMM.RealBusinessCycles.hp_trend_bounds
#print axioms AKMM.RealBusinessCycles.hp_continuous_pen
#print axioms AKMM.RealBusinessCycles.hp_continuous_fit
#print axioms AKMM.RealBusinessCycles.hp_cluster_le
#print axioms AKMM.RealBusinessCycles.hp_limit_ols
#print axioms AKMM.RealBusinessCycles.svar_det
#print axioms AKMM.RealBusinessCycles.svar_isUnit_iff
#print axioms AKMM.RealBusinessCycles.svar_inv_lower
#print axioms AKMM.RealBusinessCycles.svar_reduced_form
#print axioms AKMM.RealBusinessCycles.svar_irf
#print axioms AKMM.RealBusinessCycles.svar_impact_recursive
#print axioms AKMM.RealBusinessCycles.sm_wage
#print axioms AKMM.RealBusinessCycles.sm_static_deriv
#print axioms AKMM.RealBusinessCycles.eq_14_5
#print axioms AKMM.RealBusinessCycles.sm_static_suff
#print axioms AKMM.RealBusinessCycles.eq_14_6
#print axioms AKMM.RealBusinessCycles.eq_14_7
#print axioms AKMM.RealBusinessCycles.sm_equilibrium
#print axioms AKMM.RealBusinessCycles.sm_interest_rate
#print axioms AKMM.RealBusinessCycles.sm_interest_rate_falls
#print axioms AKMM.RealBusinessCycles.sm_leisure_derivs
#print axioms AKMM.RealBusinessCycles.sm_frisch
#print axioms AKMM.RealBusinessCycles.sm_frisch_two
#print axioms AKMM.RealBusinessCycles.sm_frisch_cd
#print axioms AKMM.RealBusinessCycles.sm_frisch_response
#print axioms AKMM.RealBusinessCycles.rbcRes
#print axioms AKMM.RealBusinessCycles.rbc_Bellman
#print axioms AKMM.RealBusinessCycles.eq_14_8
#print axioms AKMM.RealBusinessCycles.eq_14_9
#print axioms AKMM.RealBusinessCycles.eq_14_10
#print axioms AKMM.RealBusinessCycles.eq_14_11
#print axioms AKMM.RealBusinessCycles.rbc_printed_bellman_beta
#print axioms AKMM.RealBusinessCycles.rbc_example_bellman
#print axioms AKMM.RealBusinessCycles.rbc_calib_utility
#print axioms AKMM.RealBusinessCycles.irfK
#print axioms AKMM.RealBusinessCycles.irfY
#print axioms AKMM.RealBusinessCycles.irf_first_terms
#print axioms AKMM.RealBusinessCycles.irf_K_linear
#print axioms AKMM.RealBusinessCycles.irf_linear
#print axioms AKMM.RealBusinessCycles.irf_closed
#print axioms AKMM.RealBusinessCycles.irf_bound
#print axioms AKMM.RealBusinessCycles.irf_decay
#print axioms AKMM.RealBusinessCycles.cal_solow_residual
#print axioms AKMM.RealBusinessCycles.cal_perpetual_inventory
#print axioms AKMM.RealBusinessCycles.cal_perpetual_guess
#print axioms AKMM.RealBusinessCycles.cal_discount_rate
#print axioms AKMM.RealBusinessCycles.cal_mpl
#print axioms AKMM.RealBusinessCycles.cal_phi_identity
#print axioms AKMM.RealBusinessCycles.cal_steady_ratios
#print axioms AKMM.RealBusinessCycles.cal_phi_formula
#print axioms AKMM.RealBusinessCycles.calKY
#print axioms AKMM.RealBusinessCycles.calPhi
#print axioms AKMM.RealBusinessCycles.cal_phi_value
#print axioms AKMM.RealBusinessCycles.ext_kpr_form
#print axioms AKMM.RealBusinessCycles.ext_kpr_homog
#print axioms AKMM.RealBusinessCycles.ext_cd_log
#print axioms AKMM.RealBusinessCycles.ext_bgp_interest
#print axioms AKMM.RealBusinessCycles.ext_interest_printed_false
#print axioms AKMM.RealBusinessCycles.adjPsi
#print axioms AKMM.RealBusinessCycles.adj_homog
#print axioms AKMM.RealBusinessCycles.adj_Phi_homog
#print axioms AKMM.RealBusinessCycles.adj_maintenance
#print axioms AKMM.RealBusinessCycles.adj_convex_i
#print axioms AKMM.RealBusinessCycles.adj_jointly_convex
#print axioms AKMM.RealBusinessCycles.adj_dk_di
#print axioms AKMM.RealBusinessCycles.adj_shadow_price
#print axioms AKMM.RealBusinessCycles.adj_q_printed_iff
#print axioms AKMM.RealBusinessCycles.adj_q_printed_false
#print axioms AKMM.RealBusinessCycles.adj_q_first_order
#print axioms AKMM.RealBusinessCycles.adj_shadow_price_resource
#print axioms AKMM.RealBusinessCycles.adj_hayashi
#print axioms AKMM.RealBusinessCycles.ext_util_solow
#print axioms AKMM.RealBusinessCycles.ext_ist_price
#print axioms AKMM.RealBusinessCycles.ext_gov_hours
#print axioms AKMM.RealBusinessCycles.ext_gov_hours_increasing
#print axioms AKMM.RealBusinessCycles.ext_gov_perfect_subst
#print axioms AKMM.RealBusinessCycles.bca_labour_foc
#print axioms AKMM.RealBusinessCycles.bca_investment_euler
#print axioms AKMM.RealBusinessCycles.bca_static_wedges
#print axioms AKMM.RealBusinessCycles.bca_static_unique
#print axioms AKMM.RealBusinessCycles.bca_investment_wedge
#print axioms AKMM.RealBusinessCycles.bca_zero_wedges
#print axioms AKMM.RealBusinessCycles.appx_exp_sub_exp
#print axioms AKMM.RealBusinessCycles.appx_diff_prod
#print axioms AKMM.RealBusinessCycles.appx_gain_diff_sq
#print axioms AKMM.RealBusinessCycles.appx_gain_diff
#print axioms AKMM.RealBusinessCycles.appx_gain_diff_mono
#print axioms AKMM.RealBusinessCycles.hpGain
#print axioms AKMM.RealBusinessCycles.appx_hp_gain_eq
#print axioms AKMM.RealBusinessCycles.appx_hp_den_pos
#print axioms AKMM.RealBusinessCycles.appx_hp_gain_bounds
#print axioms AKMM.RealBusinessCycles.appx_hp_gain_zero
#print axioms AKMM.RealBusinessCycles.appx_hp_gain_mono
#print axioms AKMM.RealBusinessCycles.appx_cos_lt_one
#print axioms AKMM.RealBusinessCycles.appx_hp_gain_limit
#print axioms AKMM.RealBusinessCycles.appx_hp_trend_gain_anti
#print axioms AKMM.RealBusinessCycles.appx_bandpass_coeff
#print axioms AKMM.RealBusinessCycles.appx_bandpass_coeff_zero
#print axioms AKMM.RealBusinessCycles.specC
#print axioms AKMM.RealBusinessCycles.appx_orth
#print axioms AKMM.RealBusinessCycles.appx_spec_mul_exp
#print axioms AKMM.RealBusinessCycles.appx_norm_term
#print axioms AKMM.RealBusinessCycles.appx_inversion
#print axioms AKMM.RealBusinessCycles.appx_variance
#print axioms AKMM.RealBusinessCycles.appx_spec_even
#print axioms AKMM.RealBusinessCycles.appx_band_variance
#print axioms AKMM.RealBusinessCycles.filtAutocov
#print axioms AKMM.RealBusinessCycles.transferFn
#print axioms AKMM.RealBusinessCycles.appx_filter_autocov
#print axioms AKMM.RealBusinessCycles.appx_filtered_spectrum
#print axioms AKMM.RealBusinessCycles.appx_transfer_normSq
#print axioms AKMM.RealBusinessCycles.hergPosDef
#print axioms AKMM.RealBusinessCycles.herg_card_pairs
#print axioms AKMM.RealBusinessCycles.herg_sum_pairs
#print axioms AKMM.RealBusinessCycles.herg_integrable
#print axioms AKMM.RealBusinessCycles.herg_re_integral
#print axioms AKMM.RealBusinessCycles.herg_im_integral
#print axioms AKMM.RealBusinessCycles.herg_integral_fourier
#print axioms AKMM.RealBusinessCycles.hergFejer
#print axioms AKMM.RealBusinessCycles.herg_fejer_eq
#print axioms AKMM.RealBusinessCycles.herg_fejer_nonneg
#print axioms AKMM.RealBusinessCycles.herg_fejer_continuous
#print axioms AKMM.RealBusinessCycles.hergL
#print axioms AKMM.RealBusinessCycles.herg_fejer_coeff
#print axioms AKMM.RealBusinessCycles.herg_fejer_tendsto
#print axioms AKMM.RealBusinessCycles.herg_integral_fejer
#print axioms AKMM.RealBusinessCycles.herg_fejer_norm
#print axioms AKMM.RealBusinessCycles.herg_posDef_zero
#print axioms AKMM.RealBusinessCycles.herg_bound
#print axioms AKMM.RealBusinessCycles.herg_L_add
#print axioms AKMM.RealBusinessCycles.herg_L_smul
#print axioms AKMM.RealBusinessCycles.herg_L_sub
#print axioms AKMM.RealBusinessCycles.herg_tendsto_span
#print axioms AKMM.RealBusinessCycles.herg_tendsto
#print axioms AKMM.RealBusinessCycles.hergLim
#print axioms AKMM.RealBusinessCycles.herg_tendsto_lim
#print axioms AKMM.RealBusinessCycles.herg_lim_add
#print axioms AKMM.RealBusinessCycles.herg_lim_smul
#print axioms AKMM.RealBusinessCycles.hergOfReal
#print axioms AKMM.RealBusinessCycles.herg_L_ofReal_re
#print axioms AKMM.RealBusinessCycles.herg_L_re
#print axioms AKMM.RealBusinessCycles.herg_L_im
#print axioms AKMM.RealBusinessCycles.hergLambda
#print axioms AKMM.RealBusinessCycles.herg_exists
#print axioms AKMM.RealBusinessCycles.herg_posDef_of_measure
#print axioms AKMM.RealBusinessCycles.herg_integral_eq_of_coeff
#print axioms AKMM.RealBusinessCycles.herg_unique
#print axioms AKMM.RealBusinessCycles.herg_herglotz
#print axioms AKMM.RealBusinessCycles.herg_conj
#print axioms AKMM.RealBusinessCycles.herg_symm_of_real
#print axioms AKMM.RealBusinessCycles.sdenStationary
#print axioms AKMM.RealBusinessCycles.sden_posDef
#print axioms AKMM.RealBusinessCycles.sden_spectral
#print axioms AKMM.RealBusinessCycles.sden_norm_fourier
#print axioms AKMM.RealBusinessCycles.sden_integral_fourier_mul
#print axioms AKMM.RealBusinessCycles.sdenSeries
#print axioms AKMM.RealBusinessCycles.sden_series_continuous
#print axioms AKMM.RealBusinessCycles.sden_coeff
#print axioms AKMM.RealBusinessCycles.sden_series_nonneg
#print axioms AKMM.RealBusinessCycles.sdenMeasure
#print axioms AKMM.RealBusinessCycles.sden_measure_finite
#print axioms AKMM.RealBusinessCycles.sden_measure_coeff
#print axioms AKMM.RealBusinessCycles.sden_density
#print axioms AKMM.RealBusinessCycles.sdenAR1
#print axioms AKMM.RealBusinessCycles.sden_ar1_summable
#print axioms AKMM.RealBusinessCycles.sden_fourier_mul_nat
#print axioms AKMM.RealBusinessCycles.sden_one_sub_ne_zero
#print axioms AKMM.RealBusinessCycles.sden_ar1_alg
#print axioms AKMM.RealBusinessCycles.sden_ar1_series
#print axioms AKMM.RealBusinessCycles.sden_ar1_cos
#print axioms AKMM.RealBusinessCycles.sden_conj_one_sub
#print axioms AKMM.RealBusinessCycles.sden_ar1_eq_normSq
#print axioms AKMM.RealBusinessCycles.sden_ar1_normSq_cos
#print axioms AKMM.RealBusinessCycles.sden_ar1_nonneg
#print axioms AKMM.RealBusinessCycles.sden_ar1_measure
#print axioms AKMM.RealBusinessCycles.sden_ar1_coeff
#print axioms AKMM.RealBusinessCycles.sden_ar1_posDef
#print axioms AKMM.RealBusinessCycles.sden_white_noise
#print axioms AKMM.RealBusinessCycles.sdenPhi
#print axioms AKMM.RealBusinessCycles.sdenAR1Proc
#print axioms AKMM.RealBusinessCycles.sden_ar1_recursion
#print axioms AKMM.RealBusinessCycles.sden_ar1_stationary
#print axioms AKMM.RealBusinessCycles.cramExp
#print axioms AKMM.RealBusinessCycles.cram_inner_exp
#print axioms AKMM.RealBusinessCycles.cram_dense
#print axioms AKMM.RealBusinessCycles.cram_denseRange
#print axioms AKMM.RealBusinessCycles.cram_norm_eq
#print axioms AKMM.RealBusinessCycles.cramIso
#print axioms AKMM.RealBusinessCycles.cram_iso_exp
#print axioms AKMM.RealBusinessCycles.cram_iso_inner
#print axioms AKMM.RealBusinessCycles.cram_iso_unique
#print axioms AKMM.RealBusinessCycles.cram_iso_range
#print axioms AKMM.RealBusinessCycles.cramZ
#print axioms AKMM.RealBusinessCycles.cram_Z_inner
#print axioms AKMM.RealBusinessCycles.cram_Z_norm_sq
#print axioms AKMM.RealBusinessCycles.cram_Z_orth
#print axioms AKMM.RealBusinessCycles.cram_Z_union
#print axioms AKMM.RealBusinessCycles.cram_Z_univ
#print axioms AKMM.RealBusinessCycles.cram_spectral_representation
