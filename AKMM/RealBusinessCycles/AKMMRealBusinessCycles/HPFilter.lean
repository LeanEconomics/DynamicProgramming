/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

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
