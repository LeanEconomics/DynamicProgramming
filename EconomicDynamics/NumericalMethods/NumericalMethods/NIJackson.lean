/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Real.Pi.Bounds
import NumericalMethods.NIChebyshev

/-!
# Jackson's theorem for Lipschitz functions (for Theorem 11.3.1)

Ingredient of the proof of Theorem 11.3.1 (Miao, p. 359, citing Rivlin 1990): a function that is
`M`-Lipschitz on `[−1, 1]` can be approximated by a polynomial of degree `≤ n` to within
`C M / n` uniformly on `[−1, 1]`, with the absolute constant `C = 12(1 + π⁴)/π`
(`ni_jackson_lipschitz`).

The proof is Jackson's: put `g(θ) = f(cos θ)` (even, `2π`-periodic, `M`-Lipschitz) and convolve
it with the Jackson kernel `K(t) = F_m(t)²`, where `F_m(t) = ∑_{i<m} (1 + 2∑_{j=1}^{i} cos jt)` is
the Fejér kernel, `(1 − cos t) F_m(t) = 1 − cos mt` (`ni_fej_identity`). Since `K` is a cosine
polynomial of degree `2m − 2` and `g` is even, the convolution is a polynomial in `cos θ`
(`ni_conv_poly`); the error is at most `M ∫|t|K / ∫K ≤ 6(1 + π⁴) M / (π m)` (`ni_jackK_mass_ge`,
`ni_jackK_moment_le`).
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

/-- Every polynomial of degree `< D` is a combination of `T₀, …, T_{D−1}`. -/
theorem ni_cheb_expand (R : ℝ[X]) (D : ℕ) (hR : R.degree < D) :
    ∃ c : ℕ → ℝ, ∀ y, R.eval y = ∑ i ∈ Finset.range D, c i * (T ℝ (i : ℤ)).eval y := by
  have hmem : R ∈ degreeLT ℝ D := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio D = Finset.range D by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, fun y => ?_⟩
  rw [← hc, eval_finsetSum]
  simp [chebyshevTsequence]

/-- The Dirichlet polynomial `1 + 2∑_{j=1}^{i} T_j`. -/
noncomputable def ni_dirPoly (i : ℕ) : ℝ[X] := 1 + 2 * ∑ j ∈ Finset.Icc 1 i, T ℝ (j : ℤ)

/-- The Fejér polynomial `∑_{i<m} (1 + 2∑_{j=1}^{i} T_j)`. -/
noncomputable def ni_fejPoly (m : ℕ) : ℝ[X] := ∑ i ∈ Finset.range m, ni_dirPoly i

/-- The (unnormalised) Jackson polynomial `F_m²`. -/
noncomputable def ni_jackPoly (m : ℕ) : ℝ[X] := ni_fejPoly m ^ 2

/-- The Jackson kernel `K(t) = F_m(cos t)²`. -/
noncomputable def ni_jackK (m : ℕ) (t : ℝ) : ℝ := (ni_jackPoly m).eval (cos t)

/-- The Dirichlet sum `1 + 2∑_{j=1}^{i} cos jt`. -/
noncomputable def ni_dir (i : ℕ) (t : ℝ) : ℝ := 1 + 2 * ∑ j ∈ Finset.Icc 1 i, cos (j * t)

/-- The Fejér sum `∑_{i<m} (1 + 2∑_{j=1}^{i} cos jt)`. -/
noncomputable def ni_fej (m : ℕ) (t : ℝ) : ℝ := ∑ i ∈ Finset.range m, ni_dir i t

theorem ni_dirPoly_eval (i : ℕ) (t : ℝ) : (ni_dirPoly i).eval (cos t) = ni_dir i t := by
  simp [ni_dirPoly, ni_dir, eval_finsetSum]

theorem ni_fejPoly_eval (m : ℕ) (t : ℝ) : (ni_fejPoly m).eval (cos t) = ni_fej m t := by
  simp [ni_fejPoly, ni_fej, eval_finsetSum, ni_dirPoly_eval]

theorem ni_jackK_eq (m : ℕ) (t : ℝ) : ni_jackK m t = ni_fej m t ^ 2 := by
  simp [ni_jackK, ni_jackPoly, ni_fejPoly_eval]

theorem ni_jackK_nonneg (m : ℕ) (t : ℝ) : 0 ≤ ni_jackK m t := by
  rw [ni_jackK_eq]; positivity

theorem ni_jackK_continuous (m : ℕ) : Continuous (ni_jackK m) :=
  (Polynomial.continuous _).comp continuous_cos

theorem ni_jackK_even (m : ℕ) (t : ℝ) : ni_jackK m (-t) = ni_jackK m t := by
  simp [ni_jackK, cos_neg]

theorem ni_jackK_periodic (m : ℕ) (t : ℝ) : ni_jackK m (t + 2 * π) = ni_jackK m t := by
  simp [ni_jackK, cos_add_two_pi]

theorem ni_jackPoly_natDegree (m : ℕ) : (ni_jackPoly m).natDegree ≤ 2 * (m - 1) := by
  have hd : ∀ i, (ni_dirPoly i).natDegree ≤ i := by
    intro i
    unfold ni_dirPoly
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    have : (∑ j ∈ Finset.Icc 1 i, T ℝ (j : ℤ)).natDegree ≤ i := by
      refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      rw [natDegree_T, Int.natAbs_natCast]
      exact (Finset.mem_Icc.mp hj).2
    have h2 : (2 : ℝ[X]).natDegree = 0 := natDegree_ofNat 2
    omega
  have hf : (ni_fejPoly m).natDegree ≤ m - 1 := by
    unfold ni_fejPoly
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (hd i).trans (by have := Finset.mem_range.mp hi; omega)
  unfold ni_jackPoly
  exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hf)

/-- `(1 − cos t)(1 + 2∑_{j=1}^{i} cos jt) = cos it − cos (i + 1)t`. -/
theorem ni_dir_identity (i : ℕ) (t : ℝ) :
    (1 - cos t) * ni_dir i t = cos (i * t) - cos ((i + 1) * t) := by
  induction i with
  | zero => simp [ni_dir]
  | succ i ih =>
    unfold ni_dir at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    have htrig : cos ((i + 1 + 1) * t) + cos (i * t) = 2 * cos ((i + 1) * t) * cos t := by
      have e1 : (i + 1 + 1) * t = (i + 1) * t + t := by ring
      have e2 : (i : ℝ) * t = (i + 1) * t - t := by ring
      rw [e1, e2, cos_add, cos_sub]
      ring
    push_cast
    linear_combination ih + htrig

/-- `(1 − cos t) F_m(t) = 1 − cos mt` (Fejér). -/
theorem ni_fej_identity (m : ℕ) (t : ℝ) : (1 - cos t) * ni_fej m t = 1 - cos (m * t) := by
  unfold ni_fej
  rw [Finset.mul_sum]
  simp_rw [ni_dir_identity]
  have h := Finset.sum_range_sub' (fun i : ℕ => cos ((i : ℝ) * t)) m
  push_cast at h
  rw [h]
  simp

/-- `|F_m(t)| ≤ m²`. -/
theorem ni_fej_abs_le (m : ℕ) (t : ℝ) : |ni_fej m t| ≤ m ^ 2 := by
  have hd : ∀ i, |ni_dir i t| ≤ 1 + 2 * i := by
    intro i
    unfold ni_dir
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul, abs_two]
    have : |∑ j ∈ Finset.Icc 1 i, cos (j * t)| ≤ i := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => abs_cos_le_one _).trans ?_
      simp
    linarith
  have hsum : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 + 2 * (i : ℝ)) = m ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  unfold ni_fej
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← hsum m]
  exact Finset.sum_le_sum fun i _ => hd i

/-- Near `0`: `F_m(t) ≥ m²/2` for `|t| ≤ π/(3m)`. -/
theorem ni_fej_ge {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : |t| ≤ π / (3 * m)) :
    (m : ℝ) ^ 2 / 2 ≤ ni_fej m t := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcos : ∀ j : ℕ, j < m → 1 / 2 ≤ cos (j * t) := by
    intro j hj
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj.le
    have h1 : |(j : ℝ) * t| ≤ π / 3 := by
      rw [abs_mul, Nat.abs_cast]
      calc (j : ℝ) * |t| ≤ m * (π / (3 * m)) := by gcongr
        _ = π / 3 := by field_simp
    rw [← cos_abs, ← cos_pi_div_three]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) h1
  have hd : ∀ i ∈ Finset.range m, 1 + (i : ℝ) ≤ ni_dir i t := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold ni_dir
    have : (i : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 1 i, cos (j * t) := by
      have h : ∑ j ∈ Finset.Icc 1 i, (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 1 i, cos (j * t) :=
        Finset.sum_le_sum fun j hj => hcos j (by have := (Finset.mem_Icc.mp hj).2; omega)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h
      simp only [Nat.add_sub_cancel] at h
      linarith
    linarith
  have hsum : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 + (i : ℝ)) = m * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  unfold ni_fej
  have := Finset.sum_le_sum hd
  rw [hsum m] at this
  nlinarith

/-- `1 − cos t ≥ 2t²/π²` for `|t| ≤ π`. -/
theorem ni_one_sub_cos_ge {t : ℝ} (ht : |t| ≤ π) : 2 * t ^ 2 / π ^ 2 ≤ 1 - cos t := by
  have hs : |t| / π ≤ sin (|t| / 2) := by
    have := mul_le_sin (x := |t| / 2) (by positivity) (by linarith)
    calc |t| / π = 2 / π * (|t| / 2) := by ring
      _ ≤ _ := this
  have hcos : cos t = 1 - 2 * sin (|t| / 2) ^ 2 := by
    rw [← cos_abs, show |t| = 2 * (|t| / 2) by ring, cos_two_mul, ← sin_sq_add_cos_sq (|t| / 2)]
    ring_nf
  have h0 : 0 ≤ |t| / π := div_nonneg (abs_nonneg _) pi_pos.le
  have hsq : (|t| / π) ^ 2 ≤ sin (|t| / 2) ^ 2 := pow_le_pow_left₀ h0 hs 2
  rw [div_pow, sq_abs] at hsq
  rw [hcos]
  have : 2 * t ^ 2 / π ^ 2 = 2 * (t ^ 2 / π ^ 2) := by ring
  linarith

/-- Away from `0`: `0 ≤ F_m(t) ≤ π²/t²` for `0 < |t| ≤ π`. -/
theorem ni_fej_le {m : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ π) :
    0 ≤ ni_fej m t ∧ ni_fej m t ≤ π ^ 2 / t ^ 2 := by
  have hc := ni_one_sub_cos_ge ht
  have hpos : 0 < 2 * t ^ 2 / π ^ 2 := by positivity
  have hden : 0 < 1 - cos t := lt_of_lt_of_le hpos hc
  have hid := ni_fej_identity m t
  have hF : ni_fej m t = (1 - cos (m * t)) / (1 - cos t) := by
    field_simp; linarith
  have hnum0 : 0 ≤ 1 - cos (m * t) := by linarith [cos_le_one (m * t)]
  have hnum2 : 1 - cos (m * t) ≤ 2 := by linarith [neg_one_le_cos (m * t)]
  refine ⟨by rw [hF]; positivity, ?_⟩
  rw [hF, div_le_div_iff₀ hden (by positivity)]
  have : 2 * t ^ 2 ≤ π ^ 2 * (1 - cos t) := by
    have := mul_le_mul_of_nonneg_left hc (sq_nonneg π)
    rwa [mul_div_cancel₀ _ (by positivity)] at this
  nlinarith

/-- The mass of the Jackson kernel: `∫_{−π}^{π} K ≥ π m³/6`. -/
theorem ni_jackK_mass_ge {m : ℕ} (hm : 1 ≤ m) :
    π * (m : ℝ) ^ 3 / 6 ≤ ∫ t in -π..π, ni_jackK m t := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set δ := π / (3 * m)
  have hδ : 0 < δ := by positivity
  have hδπ : δ ≤ π := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [pi_pos]
  have hint := (ni_jackK_continuous m).intervalIntegrable (μ := MeasureTheory.volume) (-π) π
  have h1 : ∫ t in -δ..δ, ni_jackK m t ≤ ∫ t in -π..π, ni_jackK m t :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hδπ
      (Filter.Eventually.of_forall fun t => ni_jackK_nonneg m t) hint
  have h2 : ∫ t in -δ..δ, ((m : ℝ) ^ 2 / 2) ^ 2 ≤ ∫ t in -δ..δ, ni_jackK m t := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((ni_jackK_continuous m).intervalIntegrable _ _) fun t ht => ?_
    rw [ni_jackK_eq]
    have hab : |t| ≤ δ := abs_le.mpr ⟨ht.1, ht.2⟩
    have := ni_fej_ge hm hab
    have h0 : 0 ≤ (m : ℝ) ^ 2 / 2 := by positivity
    exact pow_le_pow_left₀ h0 this 2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  have e : (δ - -δ) * ((m : ℝ) ^ 2 / 2) ^ 2 = π * (m : ℝ) ^ 3 / 6 := by
    simp only [δ]; field_simp; ring
  linarith

/-- The first moment of the Jackson kernel: `∫_{−π}^{π} |t| K(t) dt ≤ (1 + π⁴) m²`. -/
theorem ni_jackK_moment_le {m : ℕ} (hm : 1 ≤ m) :
    ∫ t in -π..π, |t| * ni_jackK m t ≤ (1 + π ^ 4) * (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcont : Continuous fun t => |t| * ni_jackK m t :=
    continuous_abs.mul (ni_jackK_continuous m)
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun t => |t| * ni_jackK m t)
      MeasureTheory.volume a b := fun a b => hcont.intervalIntegrable a b
  -- evenness
  have heven : ∫ t in -π..0, |t| * ni_jackK m t = ∫ t in (0 : ℝ)..π, |t| * ni_jackK m t := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π)
      (fun t => |t| * ni_jackK m t)
    simp only [abs_neg, ni_jackK_even, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-π) 0) (hii 0 π), heven]
  -- split `[0, π]` at `1/m`
  set a := 1 / (m : ℝ)
  have ha : 0 < a := by positivity
  have haπ : a ≤ π := by
    have : a ≤ 1 := by rw [div_le_one hm']; exact hm1
    linarith [pi_gt_three]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 a) (hii a π)]
  have hA : ∫ t in (0 : ℝ)..a, |t| * ni_jackK m t ≤ (m : ℝ) ^ 2 / 2 := by
    have h := intervalIntegral.integral_mono_on ha.le (hii 0 a)
      ((continuous_id.mul continuous_const).intervalIntegrable (μ := MeasureTheory.volume) 0 a)
      (g := fun t => t * (m : ℝ) ^ 4) fun t ht => by
        rw [abs_of_nonneg ht.1, ni_jackK_eq]
        have hF := ni_fej_abs_le m t
        have : ni_fej m t ^ 2 ≤ (m : ℝ) ^ 4 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hF 2
          rw [sq_abs] at this
          linarith [show ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 by ring]
        exact mul_le_mul_of_nonneg_left this ht.1
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const, integral_id]
    simp only [a]
    field_simp
    ring
  have hB : ∫ t in a..π, |t| * ni_jackK m t ≤ π ^ 4 * ((m : ℝ) ^ 2 / 2) := by
    have hcube : ContinuousOn (fun t : ℝ => π ^ 4 * (1 / t ^ 3)) (Set.uIcc a π) := by
      refine continuousOn_const.mul (continuousOn_const.div (continuousOn_pow 3) fun t ht => ?_)
      rw [Set.uIcc_of_le haπ] at ht
      have : 0 < t := lt_of_lt_of_le ha ht.1
      positivity
    have h := intervalIntegral.integral_mono_on haπ (hii a π) (hcube.intervalIntegrable)
      fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        have htπ : |t| ≤ π := by rw [abs_of_pos ht0]; exact ht.2
        rw [abs_of_pos ht0, ni_jackK_eq]
        obtain ⟨hF0, hF1⟩ := ni_fej_le (m := m) ht0.ne' htπ
        have hsq : ni_fej m t ^ 2 ≤ (π ^ 2 / t ^ 2) ^ 2 := pow_le_pow_left₀ hF0 hF1 2
        calc t * ni_fej m t ^ 2 ≤ t * (π ^ 2 / t ^ 2) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq ht0.le
          _ = π ^ 4 * (1 / t ^ 3) := by field_simp
    refine h.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hderiv : ∀ t ∈ Set.uIcc a π, HasDerivAt (fun t : ℝ => -1 / (2 * t ^ 2)) (1 / t ^ 3) t := by
      intro t ht
      rw [Set.uIcc_of_le haπ] at ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
      have := ((hasDerivAt_pow 2 t).const_mul 2).inv (by positivity)
      convert this.const_mul (-1) using 1
      · funext s; simp [div_eq_mul_inv]
      · field_simp; ring
    have hint : IntervalIntegrable (fun t : ℝ => 1 / t ^ 3) MeasureTheory.volume a π := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div (continuousOn_pow 3) fun t ht => ?_
      rw [Set.uIcc_of_le haπ] at ht
      have : 0 < t := lt_of_lt_of_le ha ht.1
      positivity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hval : -1 / (2 * π ^ 2) - -1 / (2 * a ^ 2) ≤ (m : ℝ) ^ 2 / 2 := by
      have : -1 / (2 * a ^ 2) = -((m : ℝ) ^ 2 / 2) := by simp only [a]; field_simp
      rw [this]
      have : 0 < 1 / (2 * π ^ 2) := by positivity
      have e : -1 / (2 * π ^ 2) = -(1 / (2 * π ^ 2)) := by ring
      linarith
    exact mul_le_mul_of_nonneg_left hval (by positivity)
  linarith

end Miao.NumericalMethods
