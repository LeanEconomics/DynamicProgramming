/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NIJackson

/-!
# Jackson's theorem (for Theorem 11.3.1)

Ingredient of the proof of Theorem 11.3.1 (Miao, p. 359, citing Rivlin 1990).

* `ni_conv_poly`: convolving an even `2π`-periodic continuous `g` with the Jackson kernel gives a
  polynomial of degree `≤ 2(m − 1)` in `cos θ`.
* `ni_jackson_lipschitz` (Jackson): an `M`-Lipschitz function on `[−1, 1]` is within
  `12(1 + π⁴)/π · M/n` of a polynomial of degree `≤ n` (`n ≥ 1`), uniformly on `[−1, 1]`.
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

/-- The convolution of an even, `2π`-periodic, continuous `g` with the Jackson kernel is a
polynomial of degree `≤ 2(m − 1)` in `cos θ`. -/
theorem ni_conv_poly (m : ℕ) (g : ℝ → ℝ) (hg : Continuous g) (hgeven : ∀ s, g (-s) = g s)
    (hgper : ∀ s, g (s + 2 * π) = g s) :
    ∃ p : ℝ[X], p.natDegree ≤ 2 * (m - 1) ∧
      ∀ θ, ∫ t in -π..π, ni_jackK m t * g (θ - t) = p.eval (cos θ) := by
  set D := 2 * (m - 1) + 1
  have hdegR : (ni_jackPoly m).degree < D := by
    refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le (ni_jackPoly_natDegree m)
  obtain ⟨c, hc⟩ := ni_cheb_expand (ni_jackPoly m) D hdegR
  set α : ℕ → ℝ := fun i => ∫ s in -π..π, cos (i * s) * g s
  refine ⟨∑ i ∈ Finset.range D, C (c i * α i) * T ℝ (i : ℤ), ?_, fun θ => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_T, Int.natAbs_natCast]
    have := Finset.mem_range.mp hi
    omega
  -- shift to `∫ K(θ − s) g(s) ds`
  have hshift : ∫ t in -π..π, ni_jackK m t * g (θ - t) =
      ∫ s in -π..π, ni_jackK m (θ - s) * g s := by
    have h1 := intervalIntegral.integral_comp_sub_left
      (fun s => ni_jackK m (θ - s) * g s) θ (a := -π) (b := π)
    simp only [sub_sub_cancel] at h1
    rw [h1]
    have hper : Function.Periodic (fun s => ni_jackK m (θ - s) * g s) (2 * π) := by
      intro s
      simp only
      rw [hgper, show θ - (s + 2 * π) = θ - s - 2 * π by ring]
      have := ni_jackK_periodic m (θ - s - 2 * π)
      rw [sub_add_cancel] at this
      rw [this]
    have h2 := hper.intervalIntegral_add_eq (θ - π) (-π)
    rw [show θ - π + 2 * π = θ - -π by ring, show -π + 2 * π = π by ring,
      show θ - π = θ - π by rfl] at h2
    rw [h2]
  rw [hshift]
  -- expand the kernel
  have hK : ∀ s, ni_jackK m (θ - s) * g s = ∑ i ∈ Finset.range D,
      ((c i * cos (i * θ)) * (cos (i * s) * g s) + (c i * sin (i * θ)) * (sin (i * s) * g s)) := by
    intro s
    rw [ni_jackK, hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ni_cheb_cos i (θ - s)
    rw [this, mul_sub, cos_sub]
    ring
  simp_rw [hK]
  have hcont1 : ∀ i : ℕ, Continuous fun s => cos (i * s) * g s := fun i =>
    (continuous_cos.comp (continuous_const.mul continuous_id)).mul hg
  have hcont2 : ∀ i : ℕ, Continuous fun s => sin (i * s) * g s := fun i =>
    (continuous_sin.comp (continuous_const.mul continuous_id)).mul hg
  rw [intervalIntegral.integral_finsetSum (f := fun i s =>
    (c i * cos (i * θ)) * (cos (i * s) * g s) + (c i * sin (i * θ)) * (sin (i * s) * g s))
    fun i _ => by apply Continuous.intervalIntegrable; fun_prop]
  -- the sine moments vanish by evenness of `g`
  have hβ : ∀ i : ℕ, ∫ s in -π..π, sin (i * s) * g s = 0 := by
    intro i
    have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
      (fun s => sin (i * s) * g s)
    simp only [neg_neg, mul_neg, sin_neg, hgeven, neg_mul] at h
    rw [intervalIntegral.integral_neg] at h
    linarith
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_add ((hcont1 i).const_mul _ |>.intervalIntegrable _ _)
    ((hcont2 i).const_mul _ |>.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hβ, eval_mul, eval_C, ni_cheb_cos]
  simp only [α]
  ring

/-- The constant of Jackson's theorem, `12(1 + π⁴)/π`. -/
noncomputable def ni_jacksonC : ℝ := 12 * (1 + π ^ 4) / π

theorem ni_jacksonC_pos : 0 < ni_jacksonC := by
  unfold ni_jacksonC; positivity

/-- **Jackson's theorem** for Lipschitz functions (used in the proof of Theorem 11.3.1, Miao,
p. 359): if `|f(x) − f(y)| ≤ M|x − y|` on `[−1, 1]` then for every `n ≥ 1` there is a polynomial
`p` of degree `≤ n` with `|f(x) − p(x)| ≤ 12(1 + π⁴)/π · M/n` on `[−1, 1]`. -/
theorem ni_jackson_lipschitz (f : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f x - f y| ≤ M * |x - y|)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ ni_jacksonC * M / n := by
  set g : ℝ → ℝ := fun θ => f (cos θ)
  have hcosI : ∀ θ, cos θ ∈ Set.Icc (-1 : ℝ) 1 := fun θ => ⟨neg_one_le_cos θ, cos_le_one θ⟩
  have hglip : ∀ a b, |g a - g b| ≤ M * |a - b| := fun a b =>
    (hf _ (hcosI a) _ (hcosI b)).trans (mul_le_mul_of_nonneg_left (abs_cos_sub_cos_le a b) hM)
  have hgc : Continuous g := by
    have : LipschitzWith (Real.toNNReal M) g := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM]
      exact hglip a b
    exact this.continuous
  have hgeven : ∀ s, g (-s) = g s := fun s => by simp [g, cos_neg]
  have hgper : ∀ s, g (s + 2 * π) = g s := fun s => by simp [g, cos_add_two_pi]
  set m := n / 2 + 1
  have hm : 1 ≤ m := by omega
  have hdeg : 2 * (m - 1) ≤ n := by
    have : m - 1 = n / 2 := by omega
    rw [this]; exact Nat.mul_div_le n 2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnm : (n : ℝ) < 2 * m := by
    have : n < 2 * m := by omega
    exact_mod_cast this
  set Z := ∫ t in -π..π, ni_jackK m t
  have hZ : π * (m : ℝ) ^ 3 / 6 ≤ Z := ni_jackK_mass_ge hm
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have hJ := ni_jackK_moment_le hm
  obtain ⟨p₀, hp₀, hconv⟩ := ni_conv_poly m g hgc hgeven hgper
  refine ⟨C (1 / Z) * p₀, (natDegree_C_mul_le _ _).trans (hp₀.trans hdeg), fun x hx => ?_⟩
  set θ := arccos x
  have hxθ : cos θ = x := cos_arccos hx.1 hx.2
  have hfx : f x = g θ := by simp only [g, hxθ]
  rw [eval_mul, eval_C, hfx, ← hxθ, ← hconv θ]
  have hKc := ni_jackK_continuous m
  have hint1 : IntervalIntegrable (fun t => ni_jackK m t * g (θ - t)) MeasureTheory.volume
      (-π) π := (hKc.mul (hgc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hint0 : IntervalIntegrable (fun t => ni_jackK m t * g θ) MeasureTheory.volume (-π) π :=
    (hKc.mul continuous_const).intervalIntegrable _ _
  have hdiff : g θ - 1 / Z * ∫ t in -π..π, ni_jackK m t * g (θ - t) =
      1 / Z * ∫ t in -π..π, ni_jackK m t * (g θ - g (θ - t)) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hint0 hint1, intervalIntegral.integral_mul_const]
    field_simp
    rfl
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Z)]
  have hpi : -π ≤ π := by linarith [pi_pos]
  have habs : |∫ t in -π..π, ni_jackK m t * (g θ - g (θ - t))| ≤
      M * ∫ t in -π..π, |t| * ni_jackK m t := by
    refine (intervalIntegral.abs_integral_le_integral_abs hpi).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi ?_ ?_ fun t _ => ?_
    · exact ((hKc.mul (continuous_const.sub (hgc.comp (continuous_const.sub
        continuous_id)))).abs).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_abs.mul hKc)).intervalIntegrable _ _
    · rw [abs_mul, abs_of_nonneg (ni_jackK_nonneg m t)]
      have := hglip θ (θ - t)
      rw [sub_sub_cancel] at this
      nlinarith [ni_jackK_nonneg m t]
  have hstep : 1 / Z * |∫ t in -π..π, ni_jackK m t * (g θ - g (θ - t))| ≤
      1 / Z * (M * ((1 + π ^ 4) * (m : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (habs.trans (mul_le_mul_of_nonneg_left hJ hM)) (by positivity)
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hZpos hn']
  unfold ni_jacksonC
  have hpi0 := pi_pos
  have key : M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n * π ≤ 12 * (1 + π ^ 4) * M * Z := by
    have h1 : M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n * π ≤
        M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * (2 * m) * π := by
      have : 0 ≤ M * ((1 + π ^ 4) * (m : ℝ) ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnm.le this) hpi0.le
    have h2 : M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * (2 * m) * π =
        12 * (1 + π ^ 4) * M * (π * (m : ℝ) ^ 3 / 6) := by ring
    have h3 : 12 * (1 + π ^ 4) * M * (π * (m : ℝ) ^ 3 / 6) ≤ 12 * (1 + π ^ 4) * M * Z :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    linarith
  calc M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n = M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n * π / π := by
        field_simp
    _ ≤ 12 * (1 + π ^ 4) * M * Z / π := by gcongr
    _ = 12 * (1 + π ^ 4) / π * M * Z := by ring

end Miao.NumericalMethods
