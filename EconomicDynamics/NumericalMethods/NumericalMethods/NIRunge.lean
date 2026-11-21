/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import NumericalMethods.NIExercise1

/-!
# Interpolation at uniformly spaced nodes need not converge (Miao, p. 360)

Miao, p. 360: "interpolation at uniformly spaced nodes does not necessarily converge as we use
more points". We prove it (`ni_uniform_interp_not_convergent`): there is a continuous `f` on
`[−1, 1]` whose polynomial interpolants at the uniform nodes `xₖ = −1 + 2k/N`, `k = 0, …, N`, do
not converge to `f` uniformly.

* `ni_uniform_basis_lower`: at `x* = −1 + 1/N`, `|ℓₖ(x*)| ≥ C(N, k)/(4N²)`, so the Lebesgue
  function satisfies `∑ₖ |ℓₖ(x*)| ≥ 2^N/(4N²)` (`ni_uniform_lebesgue_lower`).
* `ni_uniformInterp N`: the interpolation operator on `C([−1, 1])` as a continuous linear map,
  with `‖ni_uniformInterp N‖ ≥ 2^N/(4N²)` (`ni_uniformInterp_norm_ge`), using a piecewise
  linear test function.
* The uniform boundedness principle (`banach_steinhaus`) then gives the divergent `f`.
-/

open Polynomial Filter Topology

namespace Miao.NumericalMethods

/-- `∏_{j=0}^{N} |2j − 1| ≥ 2^N N!/(2N)` for `N ≥ 1`. -/
theorem ni_prod_odd_ge (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N * N.factorial / (2 * N) ≤ ∏ j ∈ Finset.range (N + 1), |2 * (j : ℝ) - 1| := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, zero_sub, abs_neg, abs_one,
    mul_one]
  have hpos : ∀ j : ℕ, |2 * ((j : ℝ) + 1) - 1| = 2 * j + 1 := fun j => by
    rw [abs_of_pos (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])]; ring
  simp_rw [hpos]
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    have e : (2 : ℝ) ^ (N + 1) * ((N + 1 : ℕ) * N.factorial : ℕ) / (2 * (N + 1 : ℕ)) =
        2 ^ N * N.factorial := by
      push_cast; field_simp; ring
    rw [e]
    have h2 : (2 : ℝ) ^ N * N.factorial ≤ 2 ^ N * N.factorial / (2 * N) * (2 * N + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) N]
    exact h2.trans (mul_le_mul_of_nonneg_right ih (by positivity))

/-- `∏_{j ≠ k, j ≤ N} |k − j| = k!(N − k)!`. -/
theorem ni_prod_dist_eq (N k : ℕ) (hk : k ≤ N) :
    ∏ j ∈ (Finset.range (N + 1)).erase k, |(k : ℝ) - j| =
      (k.factorial : ℝ) * (N - k).factorial := by
  set g : ℕ → ℝ := fun j => if j = k then 1 else |(k : ℝ) - j|
  have h1 : ∏ j ∈ (Finset.range (N + 1)).erase k, |(k : ℝ) - j| =
      ∏ j ∈ (Finset.range (N + 1)).erase k, g j :=
    Finset.prod_congr rfl fun j hj => by simp [g, Finset.ne_of_mem_erase hj]
  rw [h1, Finset.prod_erase _ (by simp [g]), ← Finset.prod_range_mul_prod_Ico g
    (show k ≤ N + 1 by omega), Finset.prod_eq_prod_Ico_succ_bot (show k < N + 1 by omega)]
  have hlow : ∏ j ∈ Finset.range k, g j = k.factorial := by
    rw [← Finset.prod_range_reflect, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [g, show k - 1 - j ≠ k by omega, ↓reduceIte]
    rw [abs_of_nonneg (by
      have : ((k - 1 - j : ℕ) : ℝ) ≤ k := by exact_mod_cast (show k - 1 - j ≤ k by omega)
      linarith)]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hhigh : ∏ j ∈ Finset.Ico (k + 1) (N + 1), g j = (N - k).factorial := by
    rw [Finset.prod_Ico_eq_prod_range, show N + 1 - (k + 1) = N - k by omega,
      ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [g, show k + 1 + j ≠ k by omega, ↓reduceIte]
    rw [abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
    push_cast
    ring
  rw [hlow, hhigh]
  simp [g]

/-- At `x* = −1 + 1/N`, the Lagrange basis for the uniform nodes satisfies
`|ℓₖ(x*)| ≥ C(N, k)/(4N²)`. -/
theorem ni_uniform_basis_lower (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    (N.choose k : ℝ) / (4 * N ^ 2) ≤
      |(Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval ((-1 : ℝ) + 1 / N)| := by
  set s := Finset.range (N + 1)
  set v := ni_uniformGrid N
  set xs : ℝ := -1 + 1 / N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff : ∀ j : ℕ, xs - v j = -(2 * (j : ℝ) - 1) / N := by
    intro j; simp only [xs, v, ni_uniformGrid]; field_simp; ring
  have hne : ∀ j : ℕ, xs ≠ v j := by
    intro j h
    have := hdiff j
    rw [h, sub_self] at this
    have h2 : 2 * (j : ℝ) - 1 = 0 := by
      have := this.symm
      rw [neg_div, neg_eq_zero, div_eq_zero_iff] at this
      exact this.resolve_right hN'.ne'
    have : (2 * j : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (j : ℝ)) = 1)
    omega
  have hks : k ∈ s := Finset.mem_range.mpr (by omega)
  rw [Lagrange.eval_basis_not_at_node hks (hne k), Lagrange.eval_nodal, Lagrange.nodalWeight,
    abs_mul, abs_mul, abs_inv, Finset.abs_prod, Finset.abs_prod]
  simp only [abs_inv, Finset.prod_inv_distrib]
  -- the three factors
  have hnum : ∏ j ∈ s, |xs - v j| = (∏ j ∈ s, |2 * (j : ℝ) - 1|) / (N : ℝ) ^ (N + 1) := by
    simp_rw [hdiff, abs_div, abs_neg, Nat.abs_cast]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : ∏ j ∈ s.erase k, |v k - v j| =
      (2 / N) ^ N * ((k.factorial : ℝ) * (N - k).factorial) := by
    have : ∀ j, |v k - v j| = 2 / N * |(k : ℝ) - j| := by
      intro j
      simp only [v, ni_uniformGrid]
      rw [show -1 + 2 * (k : ℝ) / N - (-1 + 2 * j / N) = 2 / N * (k - j) by ring, abs_mul,
        abs_of_pos (by positivity)]
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem hks,
      Finset.card_range, Nat.add_sub_cancel, ni_prod_dist_eq N k hk]
  have hxk : |xs - v k| = |2 * (k : ℝ) - 1| / N := by
    rw [hdiff, abs_div, abs_neg, Nat.abs_cast]
  rw [hnum, hden, hxk]
  have hodd := ni_prod_odd_ge N hN
  have hk1 : |2 * (k : ℝ) - 1| ≤ 2 * N := by
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hk0 : 0 < |2 * (k : ℝ) - 1| := by
    rw [abs_pos]
    intro h
    have : (2 * k : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (k : ℝ)) = 1)
    omega
  have hchoose : (N.choose k : ℝ) * (k.factorial * (N - k).factorial) = N.factorial := by
    rw [← mul_assoc]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hfk : (0 : ℝ) < k.factorial * (N - k).factorial := by
    have := k.factorial_pos; have := (N - k).factorial_pos; positivity
  set A := ∏ j ∈ s, |2 * (j : ℝ) - 1|
  set F : ℝ := k.factorial * (N - k).factorial
  -- the value equals `A / (|2k − 1| 2^N F)`
  have hval : A / (N : ℝ) ^ (N + 1) * (((2 / N) ^ N * F)⁻¹ * (|2 * (k : ℝ) - 1| / N)⁻¹) =
      A / (|2 * (k : ℝ) - 1| * 2 ^ N * F) := by
    rw [div_pow, pow_succ]
    field_simp
  rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : (2 : ℝ) ^ N * N.factorial / (2 * N) ≤ A := hodd
  rw [div_le_iff₀ (by positivity)] at hA
  have hNf : (N.choose k : ℝ) * F = N.factorial := hchoose
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hC : (0 : ℝ) ≤ N.choose k := Nat.cast_nonneg _
  have s1 : (N.choose k : ℝ) * (|2 * (k : ℝ) - 1| * 2 ^ N * F) ≤
      (N.choose k : ℝ) * (2 * N * 2 ^ N * F) := by
    apply mul_le_mul_of_nonneg_left _ hC
    have := mul_le_mul_of_nonneg_right hk1 (le_of_lt (mul_pos h2N hfk))
    linarith [this]
  have s2 : (N.choose k : ℝ) * (2 * N * 2 ^ N * F) = 2 * N * (2 ^ N * N.factorial) := by
    rw [← hNf]; ring
  nlinarith [s1, s2, hA]

/-- The Lebesgue function of the uniform nodes at `x* = −1 + 1/N` is at least `2^N/(4N²)`. -/
theorem ni_uniform_lebesgue_lower (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N / (4 * N ^ 2) ≤ ∑ k ∈ Finset.range (N + 1),
      |(Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval ((-1 : ℝ) + 1 / N)| := by
  have h : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) / (4 * N ^ 2) ≤
      ∑ k ∈ Finset.range (N + 1),
        |(Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval ((-1 : ℝ) + 1 / N)| :=
    Finset.sum_le_sum fun k hk =>
      ni_uniform_basis_lower N hN k (by have := Finset.mem_range.mp hk; omega)
  refine le_trans (le_of_eq ?_) h
  rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

theorem ni_uniformGrid_mem {N : ℕ} (hN : 1 ≤ N) {k : ℕ} (hk : k ≤ N) :
    ni_uniformGrid N k ∈ Set.Icc (-1 : ℝ) 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  unfold ni_uniformGrid
  constructor
  · have : 0 ≤ 2 * (k : ℝ) / N := by positivity
    linarith
  · have : 2 * (k : ℝ) / N ≤ 2 := by rw [div_le_iff₀ hN']; linarith
    linarith

/-- The polynomial interpolation operator at the uniform nodes `xₖ = −1 + 2k/N` on
`C([−1, 1])`, `f ↦ ∑ₖ f(xₖ) ℓₖ`, as a continuous linear map. -/
noncomputable def ni_uniformInterp (N : ℕ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  ∑ k ∈ Finset.range (N + 1),
    (ContinuousMap.evalCLM ℝ (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k))).smulRight
      ((Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).toContinuousMapOn
        (Set.Icc (-1 : ℝ) 1))

theorem ni_uniformInterp_apply (N : ℕ) (f : C(Set.Icc (-1 : ℝ) 1, ℝ)) (x : Set.Icc (-1 : ℝ) 1) :
    ni_uniformInterp N f x = ∑ k ∈ Finset.range (N + 1),
      f (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k)) *
        (Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval (x : ℝ) := by
  simp [ni_uniformInterp, ContinuousMap.sum_apply]

/-- `ni_uniformInterp N f` is the polynomial interpolating `f` at the uniform nodes. -/
theorem ni_uniformInterp_eq_interpolate (N : ℕ) (f : C(Set.Icc (-1 : ℝ) 1, ℝ))
    (x : Set.Icc (-1 : ℝ) 1) :
    ni_uniformInterp N f x = (Lagrange.interpolate (Finset.range (N + 1)) (ni_uniformGrid N)
      (fun k => f (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k)))).eval (x : ℝ) := by
  rw [ni_uniformInterp_apply, Lagrange.interpolate_apply, eval_finsetSum]
  simp

/-- On `[x₀, x_N]` the linear spline through values in `[−1, 1]` stays in `[−1, 1]`. -/
theorem ni_linSpline_abs_le {N : ℕ} (hN : 1 ≤ N) {x : ℕ → ℝ} (hx : StrictMono x) {y : ℕ → ℝ}
    (hy : ∀ k, |y k| ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (x 0) (x N)) :
    |ni_linSpline N x y t| ≤ 1 := by
  obtain ⟨j, hj, htj⟩ := ni_node_interval N hN t ht
  rw [ni_linSpline_piece hx y hj htj, ni_slope]
  have hlt : x j < x (j + 1) := hx (Nat.lt_succ_self j)
  set lam := (t - x j) / (x (j + 1) - x j)
  have hl0 : 0 ≤ lam := div_nonneg (by linarith [htj.1]) (by linarith)
  have hl1 : lam ≤ 1 := by rw [div_le_one (by linarith)]; linarith [htj.2]
  have e : y j + (y (j + 1) - y j) / (x (j + 1) - x j) * (t - x j) =
      (1 - lam) * y j + lam * y (j + 1) := by
    simp only [lam]; field_simp; ring
  rw [e]
  have h1 := abs_le.mp (hy j)
  have h2 := abs_le.mp (hy (j + 1))
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- `‖ni_uniformInterp N‖ ≥ 2^N/(4N²)` for `N ≥ 1`. -/
theorem ni_uniformInterp_norm_ge (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N / (4 * N ^ 2) ≤ ‖ni_uniformInterp N‖ := by
  set xs : ℝ := -1 + 1 / N
  set ℓ := fun k => (Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval xs
  set σ : ℕ → ℝ := fun k => if 0 ≤ ℓ k then 1 else -1
  have hmono := ni_uniformGrid_strictMono (show 0 < N by omega)
  obtain ⟨hlo, hhi⟩ := ni_uniformGrid_ends (show 0 < N by omega)
  have hspl := ni_linear_spline_exists (show 0 < N by omega) hmono σ
  have hcont : Continuous (ni_linSpline N (ni_uniformGrid N) σ) := by
    unfold ni_linSpline; fun_prop
  set φ : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun t => ni_linSpline N (ni_uniformGrid N) σ t, hcont.comp continuous_subtype_val⟩
  have hφ : ‖φ‖ ≤ 1 := by
    refine (ContinuousMap.norm_le _ zero_le_one).mpr fun t => ?_
    rw [Real.norm_eq_abs]
    refine ni_linSpline_abs_le hN hmono (fun k => ?_) ?_
    · simp only [σ]; split_ifs <;> simp
    · rw [hlo, hhi]; exact t.2
  have hxs : xs ∈ Set.Icc (-1 : ℝ) 1 := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    constructor
    · have : 0 ≤ 1 / (N : ℝ) := by positivity
      simp only [xs]; linarith
    · have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN'
      simp only [xs]; linarith
  have hval : ni_uniformInterp N φ ⟨xs, hxs⟩ = ∑ k ∈ Finset.range (N + 1), |ℓ k| := by
    rw [ni_uniformInterp_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
    have hproj : (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k) : ℝ) =
        ni_uniformGrid N k := by
      rw [Set.projIcc_of_mem _ (ni_uniformGrid_mem hN hkN)]
    have hφk : φ (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k)) = σ k := by
      change ni_linSpline N (ni_uniformGrid N) σ
        (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k) : ℝ) = σ k
      rw [hproj, hspl.2 k hkN]
    rw [hφk]
    change σ k * ℓ k = |ℓ k|
    simp only [σ]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have h1 : |ni_uniformInterp N φ ⟨xs, hxs⟩| ≤ ‖ni_uniformInterp N‖ := by
    calc |ni_uniformInterp N φ ⟨xs, hxs⟩| ≤ ‖ni_uniformInterp N φ‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖ni_uniformInterp N‖ * ‖φ‖ := (ni_uniformInterp N).le_opNorm φ
      _ ≤ ‖ni_uniformInterp N‖ * 1 :=
        mul_le_mul_of_nonneg_left hφ (ni_uniformInterp N).opNorm_nonneg
      _ = ‖ni_uniformInterp N‖ := mul_one _
  rw [hval, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at h1
  exact (ni_uniform_lebesgue_lower N hN).trans h1

/-- Miao, p. 360: interpolation at uniformly spaced nodes does not necessarily converge: there is
a continuous `f` on `[−1, 1]` such that its interpolating polynomials at the uniform nodes
`xₖ = −1 + 2k/N`, `k = 0, …, N`, do not converge to `f` uniformly as `N → ∞`. -/
theorem ni_uniform_interp_not_convergent :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      ¬ Tendsto (fun n : ℕ => ni_uniformInterp (n + 1) f) atTop (𝓝 f) := by
  by_contra hcon
  push Not at hcon
  have hbdd : ∀ f : C(Set.Icc (-1 : ℝ) 1, ℝ), ∃ C, ∀ n : ℕ, ‖ni_uniformInterp (n + 1) f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hcon f))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hbdd
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / (4 * (|C'| + 1)) := by positivity
  obtain ⟨N, hN2, hN1⟩ := ((ht.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop 1)).exists
  have hlow := ni_uniformInterp_norm_ge N hN1
  have hup := hC' (N - 1)
  rw [Nat.sub_add_cancel hN1] at hup
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hN2
  rw [div_le_iff₀ (by positivity)] at hlow
  have : (2 : ℝ) ^ N ≤ C' * (4 * N ^ 2) := by
    calc (2 : ℝ) ^ N ≤ ‖ni_uniformInterp N‖ * (4 * N ^ 2) := hlow
      _ ≤ C' * (4 * N ^ 2) := mul_le_mul_of_nonneg_right hup (by positivity)
  have hC'abs : C' ≤ |C'| := le_abs_self C'
  nlinarith [abs_nonneg C', sq_nonneg (N : ℝ)]

end Miao.NumericalMethods
