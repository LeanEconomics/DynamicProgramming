/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import NumericalMethods.NIChebInterp

/-!
# The Lebesgue constant of the Chebyshev nodes (for Theorem 11.3.1)

Ingredient of the proof of Theorem 11.3.1 (Miao, p. 359, citing Rivlin 1990): the Lebesgue
function `Λₙ(x) = ∑ₖ |ℓₖ(x)|` of the `N = n + 1` roots of `T_N` grows only logarithmically,
`Λₙ(x) ≤ 4π (1 + ln(n + 1))` on `[−1, 1]` (`ni_lebesgueFn_le`). (Rivlin's sharp constant is
`(2/π) ln(n + 1) + 1`; any logarithmic bound suffices for Theorem 11.3.1, whose constant `dₖ` is
free.)

* `ni_cheb_deriv_node`: `T_N'(cos θ) sin θ = N sin(Nθ)`; at a node `|T_N'(xₖ)| sin θₖ = N`.
* `ni_basis_mul_eq`: `ℓₖ(x) (x − xₖ) T_N'(xₖ) = T_N(x)`.
* `ni_basis_abs_le`: `|ℓₖ(cos θ)| ≤ 2π / (1 + N|θ − θₖ|)` for `θ ∈ [0, π]`.
* `ni_harmonic_sum_le`: `∑_{k=1}^{N} 1/(1 + |a − k|) ≤ 2(1 + ln N)` for `a ≥ 0`.
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

/-- The angle `θₖ = π(2k − 1)/(2N)` of the `k`th Chebyshev node. -/
noncomputable def ni_chebAngle (N k : ℕ) : ℝ := π * (2 * k - 1) / (2 * N)

theorem ni_chebAngle_mem {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    0 < ni_chebAngle N k ∧ ni_chebAngle N k < π := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ N := by exact_mod_cast hk2
  have hN : (0 : ℝ) < N := by linarith
  unfold ni_chebAngle
  constructor
  · apply div_pos _ (by positivity)
    exact mul_pos pi_pos (by linarith)
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

/-- `T_N'(cos θ) sin θ = N sin(Nθ)`. -/
theorem ni_cheb_deriv_cos (N : ℕ) (θ : ℝ) :
    (derivative (T ℝ N)).eval (cos θ) * sin θ = N * sin (N * θ) := by
  rw [T_derivative_eq_U, eval_mul, mul_assoc]
  have h := U_real_cos θ ((N : ℤ) - 1)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at h
  rw [h]
  simp

/-- At a Chebyshev node, `|T_N'(xₖ)| sin θₖ = N`. -/
theorem ni_cheb_deriv_node {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    |(derivative (T ℝ N)).eval (ni_chebNode N k)| * sin (ni_chebAngle N k) = N := by
  have hsin : 0 < sin (ni_chebAngle N k) :=
    sin_pos_of_pos_of_lt_pi (ni_chebAngle_mem hk).1 (ni_chebAngle_mem hk).2
  have hN : (N : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hk); exact_mod_cast (show N ≠ 0 by omega)
  have h := ni_cheb_deriv_cos N (ni_chebAngle N k)
  have hnode : ni_chebNode N k = cos (ni_chebAngle N k) := rfl
  have hs : |sin (N * ni_chebAngle N k)| = 1 := by
    have e : (N : ℝ) * ni_chebAngle N k = k * π - π / 2 := by
      unfold ni_chebAngle; field_simp
    rw [e, sin_sub_pi_div_two, cos_nat_mul_pi, abs_neg, abs_pow, abs_neg, abs_one, one_pow]
  rw [hnode, ← abs_of_pos hsin, ← abs_mul, h, abs_mul, hs, mul_one, Nat.abs_cast]

/-- `ℓₖ(x) (x − xₖ) T_N'(xₖ) = T_N(x)` for the Lagrange basis at the roots of `T_N`. -/
theorem ni_basis_mul_eq {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) (x : ℝ) :
    (Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval x * (x - ni_chebNode N k) *
      (derivative (T ℝ N)).eval (ni_chebNode N k) = (T ℝ N).eval x := by
  set s := Finset.Icc 1 N
  set v := ni_chebNode N
  have hinj : Set.InjOn v s := ni_chebNode_injOn N
  have hroot : (T ℝ N).IsRoot (v k) := (ni_cheb_roots N (v k)).mpr ⟨k, hk, rfl⟩
  set P := T ℝ N /ₘ (X - C (v k))
  have hP : (X - C (v k)) * P = T ℝ N := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hder : (derivative (T ℝ N)).eval (v k) = P.eval (v k) := by
    rw [← hP, derivative_mul]
    simp
  have hPk : P.eval (v k) ≠ 0 := by
    rw [← hder]
    intro h0
    have := ni_cheb_deriv_node hk
    rw [h0, abs_zero, zero_mul] at this
    have hN : N ≠ 0 := by have := Finset.mem_Icc.mp hk; omega
    exact hN (by exact_mod_cast this.symm)
  have hcard : s.card = N := by simp [s]
  have hN : 1 ≤ N := (Finset.mem_Icc.mp hk).1.trans (Finset.mem_Icc.mp hk).2
  have hPdeg : P.degree < s.card := by
    rw [hcard]
    have hnat : P.natDegree = N - 1 := by
      rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_T, natDegree_X_sub_C]
      simp
    refine (degree_le_natDegree).trans_lt ?_
    rw [hnat]
    exact_mod_cast (show N - 1 < N by omega)
  have hbasis : Lagrange.basis s v k = C (P.eval (v k))⁻¹ * P := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq s hinj ?_ ?_ fun j hj => ?_
    · rw [Lagrange.degree_basis hinj hk]
      exact_mod_cast (show s.card - 1 < s.card by omega)
    · rw [degree_C_mul (inv_ne_zero hPk)]
      exact hPdeg
    · rw [eval_mul, eval_C]
      by_cases hjk : j = k
      · subst hjk
        rw [Lagrange.eval_basis_self hinj hj, inv_mul_cancel₀ hPk]
      · rw [Lagrange.eval_basis_of_ne (Ne.symm hjk) hj]
        have hTj : (T ℝ N).eval (v j) = 0 := (ni_cheb_roots N (v j)).mpr ⟨j, hj, rfl⟩
        rw [← hP, eval_mul] at hTj
        have hne : v j - v k ≠ 0 := sub_ne_zero.mpr fun h => hjk (hinj hj hk h)
        simp only [eval_sub, eval_X, eval_C] at hTj
        rcases mul_eq_zero.mp hTj with h | h
        · exact absurd h hne
        · rw [h, mul_zero]
  rw [hbasis, hder, ← hP]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  field_simp

/-- `sin θₖ ≤ 2 sin((θ + θₖ)/2)` for `θ, θₖ ∈ [0, π]`. -/
theorem ni_sin_le_two_sin_half {θ φ : ℝ} (hθ : θ ∈ Set.Icc 0 π) (hφ : φ ∈ Set.Icc 0 π) :
    sin φ ≤ 2 * sin ((θ + φ) / 2) := by
  have ha0 : 0 ≤ φ / 2 := by linarith [hφ.1]
  have ha1 : φ / 2 ≤ π / 2 := by linarith [hφ.2]
  have hs : 0 ≤ sin (φ / 2) := sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith)
  have hc : cos (φ / 2) ≤ 1 := cos_le_one _
  have hc0 : 0 ≤ cos (φ / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, ha1⟩
  have hsc : sin (φ / 2) * cos (φ / 2) ≤ sin ((θ + φ) / 2) := by
    by_cases h : (θ + φ) / 2 ≤ π / 2
    · have : sin (φ / 2) ≤ sin ((θ + φ) / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) h (by linarith [hθ.1])
      nlinarith
    · push Not at h
      have e : sin ((θ + φ) / 2) = sin (π - (θ + φ) / 2) := (sin_pi_sub _).symm
      have : cos (φ / 2) ≤ sin (π - (θ + φ) / 2) := by
        rw [← sin_pi_div_two_sub]
        exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
          (by linarith [hθ.2])
      rw [e]
      nlinarith [sin_le_one (φ / 2)]
  have e2 : sin φ = 2 * sin (φ / 2) * cos (φ / 2) := by
    rw [← sin_two_mul]; ring_nf
  rw [e2]
  linarith

/-- `|ℓₖ(cos θ)| ≤ 2π / (1 + N|θ − θₖ|)` for `θ ∈ [0, π]`. -/
theorem ni_basis_abs_le {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 π) :
    |(Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval (cos θ)| ≤
      2 * π / (1 + N * |θ - ni_chebAngle N k|) := by
  set ℓ := |(Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval (cos θ)|
  set u := θ - ni_chebAngle N k
  have hφ := ni_chebAngle_mem hk
  have hφI : ni_chebAngle N k ∈ Set.Icc 0 π := ⟨hφ.1.le, hφ.2.le⟩
  have hN : (0 : ℝ) < N := by
    have := Finset.mem_Icc.mp hk; exact_mod_cast (show 0 < N by omega)
  have hden : 0 < 1 + N * |u| := by positivity
  rw [le_div_iff₀ hden]
  by_cases hu : u = 0
  · have : θ = ni_chebAngle N k := by linarith
    have hval : ℓ = 1 := by
      simp only [ℓ, this]
      rw [show cos (ni_chebAngle N k) = ni_chebNode N k from rfl,
        Lagrange.eval_basis_self (ni_chebNode_injOn N) hk, abs_one]
    rw [hval, hu, abs_zero, mul_zero, add_zero, one_mul]
    linarith [pi_gt_three]
  -- the identity `ℓ |cos θ − cos θₖ| |T'(xₖ)| = |cos Nθ|`
  have hid := congrArg abs (ni_basis_mul_eq hk (cos θ))
  rw [abs_mul, abs_mul, ni_cheb_cos] at hid
  have hder := ni_cheb_deriv_node hk
  set D := |(derivative (T ℝ N)).eval (ni_chebNode N k)|
  have hsinφ : 0 < sin (ni_chebAngle N k) := sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  -- `|cos θ − cos θₖ| = 2 A B`
  set A := sin ((θ + ni_chebAngle N k) / 2)
  set B := |sin (u / 2)|
  have hA : 0 < A := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1, hφ.1]
    · linarith [hθ.2, hφ.2]
  have hcs : |cos θ - ni_chebNode N k| = 2 * A * B := by
    rw [show ni_chebNode N k = cos (ni_chebAngle N k) from rfl, cos_sub_cos, abs_mul, abs_mul]
    simp only [abs_neg, abs_two]
    change 2 * |A| * |sin (u / 2)| = 2 * A * B
    rw [abs_of_pos hA]
  have hsA := ni_sin_le_two_sin_half hθ hφI
  -- `ℓ N B ≤ |cos Nθ|`
  have h1 : ℓ * N * B ≤ |cos (N * θ)| := by
    have e : ℓ * (2 * A * B) * D = |cos (N * θ)| := by rw [← hcs]; exact hid
    have e2 : D * sin (ni_chebAngle N k) = N := hder
    have hD : 0 ≤ D := abs_nonneg _
    have hℓ : 0 ≤ ℓ := abs_nonneg _
    have hB : 0 ≤ B := abs_nonneg _
    -- `ℓ N B * 2A = ℓ D sin θₖ B * 2A / sin θₖ ≤ …`
    have : ℓ * N * B * sin (ni_chebAngle N k) ≤ |cos (N * θ)| * sin (ni_chebAngle N k) := by
      calc ℓ * N * B * sin (ni_chebAngle N k)
          = ℓ * B * D * sin (ni_chebAngle N k) * sin (ni_chebAngle N k) := by
            rw [← e2]; ring
        _ ≤ ℓ * B * D * sin (ni_chebAngle N k) * (2 * A) := by
            gcongr
        _ = |cos (N * θ)| * sin (ni_chebAngle N k) := by rw [← e]; ring
    exact le_of_mul_le_mul_right this hsinφ
  -- `B ≥ |u|/π`
  have hu_le : |u| ≤ π := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]
  have hu2 := abs_le.mp hu_le
  have hB : |u| / π ≤ B := by
    have habs : B = sin (|u| / 2) := by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h]
        exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
      · rw [abs_of_nonpos h, show -u / 2 = -(u / 2) by ring, sin_neg]
        refine abs_of_nonpos ?_
        have : 0 ≤ sin (-(u / 2)) :=
          sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_of_nonpos h])
        rw [sin_neg] at this
        linarith
    rw [habs]
    have := mul_le_sin (x := |u| / 2) (by positivity) (by linarith)
    calc |u| / π = 2 / π * (|u| / 2) := by ring
      _ ≤ _ := this
  -- `|cos Nθ| ≤ 1` and `≤ N|u|`
  have hc1 : |cos (N * θ)| ≤ 1 := abs_cos_le_one _
  have hc2 : |cos (N * θ)| ≤ N * |u| := by
    have h0 : cos (N * ni_chebAngle N k) = 0 := by
      have e : (N : ℝ) * ni_chebAngle N k = (2 * k - 1) * (π / 2) := by
        unfold ni_chebAngle; field_simp
      rw [e, cos_eq_zero_iff]
      refine ⟨k - 1, ?_⟩
      push_cast
      ring
    have := abs_cos_sub_cos_le (N * θ) (N * ni_chebAngle N k)
    rw [h0, sub_zero, ← mul_sub, abs_mul, Nat.abs_cast] at this
    exact this
  have hpi := pi_pos
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  have key : ℓ * (N * |u|) ≤ π * |cos (N * θ)| := by
    have : ℓ * N * (|u| / π) ≤ |cos (N * θ)| :=
      le_trans (mul_le_mul_of_nonneg_left hB (by positivity)) h1
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hpi] at this
    linarith
  have hupos : 0 < N * |u| := mul_pos hN (abs_pos.mpr hu)
  rcases le_total (N * |u|) 1 with hsmall | hbig
  · have hℓπ : ℓ ≤ π := by
      have : ℓ * (N * |u|) ≤ π * (N * |u|) := by nlinarith
      exact le_of_mul_le_mul_right this hupos
    nlinarith
  · have h2 : ℓ * (N * |u|) ≤ π := by nlinarith
    have hℓπ : ℓ ≤ π := by nlinarith
    nlinarith

/-- `∑_{j < r} 1/(1 + j) ≤ 1 + ln N` for `r ≤ N`. -/
theorem ni_harmonic_le {r N : ℕ} (hr : r ≤ N) :
    ∑ j ∈ Finset.range r, (1 : ℝ) / (1 + j) ≤ 1 + Real.log N := by
  have h1 : ∑ j ∈ Finset.range r, (1 : ℝ) / (1 + j) ≤ ∑ j ∈ Finset.range N, (1 : ℝ) / (1 + j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
      (fun j _ _ => by positivity)
  have h2 : ∑ j ∈ Finset.range N, (1 : ℝ) / (1 + j) = (harmonic N : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  linarith [harmonic_le_one_add_log N]

/-- `∑_{k=1}^{N} 1/(1 + |a − k|) ≤ 2(1 + ln N)` for `a ≥ 0`. -/
theorem ni_harmonic_sum_le (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (1 + |a - k|) ≤ 2 * (1 + Real.log N) := by
  set m := min ⌊a⌋₊ N
  have hmN : m ≤ N := min_le_right _ _
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext k; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmN]
  have hA : ∑ k ∈ Finset.Ioc 0 m, (1 : ℝ) / (1 + |a - k|) ≤ 1 + Real.log N := by
    have hle : ∀ k ∈ Finset.Ioc 0 m, (1 : ℝ) / (1 + |a - k|) ≤ 1 / (1 + ((m - k : ℕ) : ℝ)) := by
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Ioc.mp hk).2
      have hka : (k : ℝ) ≤ a := by
        have : (m : ℝ) ≤ a := by
          calc (m : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
            _ ≤ a := Nat.floor_le ha
        exact le_trans (by exact_mod_cast hkm) this
      have hma : (m : ℝ) ≤ a := by
        calc (m : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
          _ ≤ a := Nat.floor_le ha
      rw [abs_of_nonneg (by linarith), Nat.cast_sub hkm]
      apply one_div_le_one_div_of_le (by
        have : (k : ℝ) ≤ m := by exact_mod_cast hkm
        linarith)
      linarith
    refine (Finset.sum_le_sum hle).trans (le_of_eq_of_le ?_ (ni_harmonic_le hmN))
    refine Finset.sum_nbij' (fun k => m - k) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      omega
    · intro j hj
      have := Finset.mem_range.mp hj
      omega
    · intro k _
      rfl
  have hB : ∑ k ∈ Finset.Ioc m N, (1 : ℝ) / (1 + |a - k|) ≤ 1 + Real.log N := by
    have hle : ∀ k ∈ Finset.Ioc m N, (1 : ℝ) / (1 + |a - k|) ≤
        1 / (1 + ((k - m - 1 : ℕ) : ℝ)) := by
      intro k hk
      have hk' := Finset.mem_Ioc.mp hk
      have hmlt : m < N := lt_of_lt_of_le hk'.1 hk'.2
      have hm : m = ⌊a⌋₊ := by
        rcases min_cases ⌊a⌋₊ N with h | h
        · exact h.1
        · omega
      have hak : a < k := by
        have h1 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
        have h2 : ((⌊a⌋₊ : ℕ) : ℝ) + 1 ≤ k := by
          rw [← hm]; exact_mod_cast hk'.1
        linarith
      have hcast : ((k - m - 1 : ℕ) : ℝ) = k - m - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp
      rw [abs_of_neg (by linarith), hcast]
      have hfa : (m : ℝ) ≤ a := by rw [hm]; exact Nat.floor_le ha
      have hfa2 : a < m + 1 := by rw [hm]; exact Nat.lt_floor_add_one a
      have hpos : (0 : ℝ) < 1 + (k - m - 1) := by
        have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk'.1
        linarith
      apply one_div_le_one_div_of_le hpos
      linarith
    refine (Finset.sum_le_sum hle).trans (le_of_eq_of_le ?_ (ni_harmonic_le (r := N - m)
      (by omega)))
    refine Finset.sum_nbij' (fun k => k - m - 1) (fun j => j + m + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      omega
    · intro j _
      omega
    · intro k _
      rfl
  linarith

/-- The Lebesgue function of the Chebyshev nodes is at most `4π(1 + ln(n + 1))` on `[−1, 1]`. -/
theorem ni_lebesgueFn_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ni_lebesgueFn n x ≤ 4 * π * (1 + Real.log (n + 1)) := by
  set N := n + 1
  set θ := arccos x
  have hθ : θ ∈ Set.Icc 0 π := ⟨arccos_nonneg x, arccos_le_pi x⟩
  have hxθ : x = cos θ := (cos_arccos hx.1 hx.2).symm
  set a := N * θ / π + 1 / 2
  have ha : 0 ≤ a := by
    have : 0 ≤ (N : ℝ) * θ / π := div_nonneg (mul_nonneg (by positivity) hθ.1) pi_pos.le
    simp only [a]
    linarith
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      |(Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval x| ≤
        2 * π * (1 / (1 + |a - k|)) := by
    intro k hk
    rw [hxθ]
    refine (ni_basis_abs_le hk hθ).trans ?_
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    -- `|a − k| ≤ N|θ − θₖ|`
    have e : (N : ℝ) * (θ - ni_chebAngle N k) = π * (a - k) := by
      have hN : (N : ℝ) ≠ 0 := by positivity
      simp only [a, ni_chebAngle]
      field_simp
      ring
    have : |a - k| ≤ N * |θ - ni_chebAngle N k| := by
      have h1 : (N : ℝ) * |θ - ni_chebAngle N k| = π * |a - k| := by
        rw [← abs_of_nonneg (show (0 : ℝ) ≤ N by positivity), ← abs_mul, e, abs_mul,
          abs_of_pos pi_pos]
      rw [h1]
      have : 1 ≤ π := by linarith [pi_gt_three]
      nlinarith [abs_nonneg (a - k)]
    linarith
  unfold ni_lebesgueFn
  calc ∑ k ∈ Finset.Icc 1 (n + 1),
        |(Lagrange.basis (Finset.Icc 1 (n + 1)) (ni_chebNode (n + 1)) k).eval x|
      ≤ ∑ k ∈ Finset.Icc 1 N, 2 * π * (1 / (1 + |a - k|)) := Finset.sum_le_sum hterm
    _ = 2 * π * ∑ k ∈ Finset.Icc 1 N, 1 / (1 + |a - k|) := by rw [Finset.mul_sum]
    _ ≤ 2 * π * (2 * (1 + Real.log N)) := by
        gcongr
        exact ni_harmonic_sum_le N ha
    _ = 4 * π * (1 + Real.log (n + 1)) := by
        simp only [N]; push_cast; ring

end Miao.NumericalMethods
