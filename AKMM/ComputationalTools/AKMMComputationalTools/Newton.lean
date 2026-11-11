/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Newton–Raphson, Newton's method for optimisation, and finite differences

AKMM, §10.2.2, pp. 265–266, §10.3.2–10.3.3, pp. 267–269.

* (10.2): `x̂ = x₀ − f(x₀)/f′(x₀)` is the root of the tangent line (`eq_10_2`), so the
  Newton–Raphson step is exact for affine `f` (`newton_affine_exact`).
* Local quadratic convergence: for `C²` `f` with `f(x*) = 0` and `f′(x*) ≠ 0` there are `δ > 0`
  and `C` with `|N(x) − x*| ≤ C|x − x*|²` and `|N(x) − x*| ≤ |x − x*|/2` on `|x − x*| < δ`
  (`newton_local_quadratic`), and from any such start the iterates converge to `x*`, at least
  geometrically and quadratically (`newton_converges`). The book only says that the method is
  faster "if `x₀` is close to the true solution"; Mathlib has no Newton convergence theorem for
  real functions, so this is proved here by the mean value inequality and the local Lipschitz
  property of `f′`.
* The central difference `(f(x+h) − f(x−h))/(2h) → f′(x)` as `h → 0` (`central_difference_tendsto`),
  exact for quadratics (`central_difference_quadratic`).
* (10.3): `x̂ = x₀ − F′(x₀)/F″(x₀)` is the critical point of the quadratic model of `F`, its
  maximiser when `F″(x₀) < 0` (`eq_10_3`, `eq_10_3_max`); the method is exact for quadratic `F`
  (`newtonOpt_quadratic_exact`); and Newton's method for `max F` is Newton–Raphson applied to
  `F′ = 0` (`newtonOpt_eq_newtonStep_deriv`, §10.3.3).
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- AKMM, (10.2) and step 2, p. 265–266: the Newton–Raphson step `x ↦ x − f(x)/f′(x)`. -/
noncomputable def newtonStep (f : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / deriv f x

/-- AKMM, (10.2), p. 265: when `f′(x₀) ≠ 0`, `x̂ = x₀ − f(x₀)/f′(x₀)` is the unique root of the
linear approximation `f(x₀) + f′(x₀)(x − x₀)`. -/
theorem eq_10_2 (f : ℝ → ℝ) {x₀ : ℝ} (hd : deriv f x₀ ≠ 0) (x : ℝ) :
    f x₀ + deriv f x₀ * (x - x₀) = 0 ↔ x = newtonStep f x₀ := by
  unfold newtonStep
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- AKMM, p. 265: "If `f(x)` is indeed linear, `x̂` delivers the solution in one step": for
`f(x) = cx + d` with `c ≠ 0`, `N(x₀) = −d/c` from every `x₀`, and `f(−d/c) = 0`. -/
theorem newton_affine_exact {c d : ℝ} (hc : c ≠ 0) (x₀ : ℝ) :
    newtonStep (fun x => c * x + d) x₀ = -d / c ∧ c * (-d / c) + d = 0 := by
  have hderiv : deriv (fun x => c * x + d) x₀ = c := by
    have := ((hasDerivAt_id x₀).const_mul c).add_const d
    simp only [id, mul_one] at this
    exact this.deriv
  refine ⟨?_, by field_simp; ring⟩
  unfold newtonStep
  rw [hderiv]
  field_simp
  ring

/-- AKMM, p. 266 (local quadratic convergence of Newton–Raphson, which the book describes as
"much faster than bisection" when "`x₀` is close to the true solution"): for `C²` `f` with a
simple root `x*` (`f(x*) = 0`, `f′(x*) ≠ 0`) there are `δ > 0` and `C ≥ 0` such that every
`x` with `|x − x*| < δ` has `|N(x) − x*| ≤ C|x − x*|²` and `|N(x) − x*| ≤ |x − x*|/2`. -/
theorem newton_local_quadratic {f : ℝ → ℝ} {xs : ℝ} (hf : ContDiff ℝ 2 f) (hroot : f xs = 0)
    (hd : deriv f xs ≠ 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ x, |x - xs| < δ →
      |newtonStep f x - xs| ≤ C * |x - xs| ^ 2 ∧ |newtonStep f x - xs| ≤ |x - xs| / 2 := by
  obtain ⟨hdiff, -, hd1⟩ := contDiff_succ_iff_deriv.1 (by exact hf : ContDiff ℝ (1 + 1) f)
  obtain ⟨K, t, ht, hK⟩ := (hd1.contDiffAt (x := xs)).exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ht
  set m := |deriv f xs| / 2 with hm_def
  have hm : 0 < m := by positivity
  obtain ⟨r2, hr2, hr2'⟩ := Metric.continuousAt_iff.1 hd1.continuous.continuousAt m hm
  set δ := min (min r r2) (m / (2 * ((K : ℝ) + 1))) with hδ_def
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hδ : 0 < δ := lt_min (lt_min hr hr2) (by positivity)
  refine ⟨δ, hδ, K / m, by positivity, fun x hx => ?_⟩
  have hxr : |x - xs| < r := hx.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hxr2 : |x - xs| < r2 := hx.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hxm : |x - xs| < m / (2 * ((K : ℝ) + 1)) := hx.trans_le (min_le_right _ _)
  -- the derivative stays away from zero
  have hfx : m < |deriv f x| := by
    have h1 := hr2' (by rw [Real.dist_eq]; exact hxr2)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (deriv f xs) (deriv f x)
    rw [abs_sub_comm] at h1
    linarith
  have hfx0 : deriv f x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hfx
    linarith
  -- the segment between `x` and `x*` lies in the Lipschitz neighbourhood
  set s := Set.uIcc x xs
  have hseg : ∀ y ∈ s, |y - x| ≤ |x - xs| ∧ y ∈ t := by
    intro y hy
    have hy' := Set.mem_uIcc.1 hy
    have h1 : |y - x| ≤ |x - xs| := by
      rcases hy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith
    have h2 : |y - xs| ≤ |x - xs| := by
      rcases hy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    refine ⟨h1, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact h2.trans_lt hxr
  have hxt : x ∈ t := (hseg x Set.left_mem_uIcc).2
  -- the mean value inequality for `g(y) = f(y) − f′(x) y`
  have hg : ∀ y ∈ s, HasDerivWithinAt (fun y => f y - deriv f x * y)
      (deriv f y - deriv f x) s y := by
    intro y _
    have h' : HasDerivAt (fun y => f y - deriv f x * y) (deriv f y - deriv f x * 1) y :=
      (hdiff y).hasDerivAt.sub ((hasDerivAt_id y).const_mul (deriv f x))
    rw [mul_one] at h'
    exact h'.hasDerivWithinAt
  have hbound : ∀ y ∈ s, ‖deriv f y - deriv f x‖ ≤ K * |x - xs| := by
    intro y hy
    obtain ⟨h1, h2⟩ := hseg y hy
    have := hK.dist_le_mul y h2 x hxt
    rw [Real.dist_eq, Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.trans (mul_le_mul_of_nonneg_left h1 hK0)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound (convex_uIcc x xs)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs, hroot] at hmvt
  have hkey : newtonStep f x - xs =
      (0 - deriv f x * xs - (f x - deriv f x * x)) / deriv f x := by
    unfold newtonStep
    field_simp
    ring
  have hmain : |newtonStep f x - xs| ≤ K / m * |x - xs| ^ 2 := by
    rw [hkey, abs_div]
    have hpos : 0 < |deriv f x| := by linarith
    rw [div_le_iff₀ hpos]
    have h3 : |xs - x| = |x - xs| := abs_sub_comm _ _
    rw [h3] at hmvt
    calc |0 - deriv f x * xs - (f x - deriv f x * x)| ≤ K * |x - xs| * |x - xs| := hmvt
      _ = K / m * |x - xs| ^ 2 * m := by field_simp
      _ ≤ K / m * |x - xs| ^ 2 * |deriv f x| := by
          apply mul_le_mul_of_nonneg_left hfx.le; positivity
  refine ⟨hmain, hmain.trans ?_⟩
  have habs : 0 ≤ |x - xs| := abs_nonneg _
  have hc : K / m * |x - xs| ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    have := mul_le_mul_of_nonneg_left hxm.le hK0
    calc (K : ℝ) * |x - xs| ≤ K * (m / (2 * (K + 1))) := this
      _ ≤ 1 / 2 * m := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  calc K / m * |x - xs| ^ 2 = (K / m * |x - xs|) * |x - xs| := by ring
    _ ≤ 1 / 2 * |x - xs| := mul_le_mul_of_nonneg_right hc habs
    _ = |x - xs| / 2 := by ring

/-- AKMM, p. 266, step 3 (iterating `x_{i+1} = N(x_i)`): from any start within `δ` of a simple
root of a `C²` function the Newton–Raphson iterates stay within `δ`, satisfy
`|x_n − x*| ≤ |x₀ − x*|/2ⁿ` and `|x_{n+1} − x*| ≤ C|x_n − x*|²`, and converge to `x*`. -/
theorem newton_converges {f : ℝ → ℝ} {xs : ℝ} (hf : ContDiff ℝ 2 f) (hroot : f xs = 0)
    (hd : deriv f xs ≠ 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ x₀, |x₀ - xs| < δ →
      (∀ n, |(newtonStep f)^[n] x₀ - xs| ≤ |x₀ - xs| / 2 ^ n) ∧
      (∀ n, |(newtonStep f)^[n + 1] x₀ - xs| ≤ C * |(newtonStep f)^[n] x₀ - xs| ^ 2) ∧
      Tendsto (fun n => (newtonStep f)^[n] x₀) atTop (𝓝 xs) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := newton_local_quadratic hf hroot hd
  refine ⟨δ, hδ, C, hC, fun x₀ hx₀ => ?_⟩
  have hgeo : ∀ n, |(newtonStep f)^[n] x₀ - xs| ≤ |x₀ - xs| / 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt : |(newtonStep f)^[n] x₀ - xs| < δ :=
        ih.trans_lt ((div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))).trans_lt hx₀)
      rw [Function.iterate_succ_apply']
      calc |newtonStep f ((newtonStep f)^[n] x₀) - xs| ≤ |(newtonStep f)^[n] x₀ - xs| / 2 :=
            (h _ hlt).2
        _ ≤ |x₀ - xs| / 2 ^ n / 2 := by gcongr
        _ = |x₀ - xs| / 2 ^ (n + 1) := by rw [pow_succ, div_div]
  refine ⟨hgeo, fun n => ?_, ?_⟩
  · have hlt : |(newtonStep f)^[n] x₀ - xs| < δ :=
      (hgeo n).trans_lt ((div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))).trans_lt hx₀)
    rw [Function.iterate_succ_apply']
    exact (h _ hlt).1
  · rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq]
    refine squeeze_zero (fun _ => abs_nonneg _) hgeo ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul |x₀ - xs|
    simpa [div_eq_mul_inv, inv_pow] using this

/-- AKMM, p. 266: the central finite-difference derivative
`(f(x + h) − f(x − h))/(2h)` tends to `f′(x)` as `h → 0` ("in principle, a smaller `h` would
provide a better approximation"). -/
theorem central_difference_tendsto {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    Tendsto (fun h => (f (x + h) - f (x - h)) / (2 * h)) (𝓝[≠] 0) (𝓝 (deriv f x)) := by
  have h1 := hasDerivAt_iff_tendsto_slope_zero.1 hf.hasDerivAt
  have hg : HasDerivAt (fun t => f (x - t)) (deriv f x * (-1)) 0 := by
    have h2 : HasDerivAt f (deriv f x) (x - id 0) := by simpa using hf.hasDerivAt
    exact h2.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_sub x)
  have h3 := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have h4 := (h1.sub h3).const_mul (1 / 2)
  have heq : (1 / 2 : ℝ) * (deriv f x - deriv f x * (-1)) = deriv f x := by ring
  rw [heq] at h4
  refine h4.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  have ht' : t ≠ 0 := ht
  simp only [smul_eq_mul, zero_add, sub_zero]
  field_simp
  ring

/-- AKMM, p. 266: the central difference is exact for quadratics: for
`f(x) = ax² + bx + c`, `(f(x + h) − f(x − h))/(2h) = 2ax + b = f′(x)` for every `h ≠ 0`. -/
theorem central_difference_quadratic (a b c x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ((a * (x + h) ^ 2 + b * (x + h) + c) - (a * (x - h) ^ 2 + b * (x - h) + c)) / (2 * h) =
      2 * a * x + b := by
  field_simp
  ring

/-- AKMM, (10.3) and step 2, p. 268: Newton's step for maximising `F`,
`x ↦ x − F′(x)/F″(x)`. -/
noncomputable def newtonOptStep (F : ℝ → ℝ) (x : ℝ) : ℝ := x - deriv F x / deriv (deriv F) x

/-- AKMM, §10.3.3, p. 269: "Newton's method for optimization is simply Newton–Raphson applied
to the first-order condition": the update for `max F` is the Newton–Raphson step for `F′`. -/
theorem newtonOpt_eq_newtonStep_deriv (F : ℝ → ℝ) : newtonOptStep F = newtonStep (deriv F) :=
  rfl

/-- AKMM, (10.3), p. 268: the quadratic model `q(x) = F(x₀) + F′(x₀)(x − x₀) + ½F″(x₀)(x − x₀)²`
satisfies `q(x) = q(x̂) + ½F″(x₀)(x − x̂)²` with `x̂ = x₀ − F′(x₀)/F″(x₀)`, so `x̂` is its
unique critical point ("taking the first-order condition … we obtain (10.3)"). -/
theorem eq_10_3 (F : ℝ → ℝ) {x₀ : ℝ} (hd : deriv (deriv F) x₀ ≠ 0) (x : ℝ) :
    F x₀ + deriv F x₀ * (x - x₀) + 1 / 2 * deriv (deriv F) x₀ * (x - x₀) ^ 2 =
      (F x₀ + deriv F x₀ * (newtonOptStep F x₀ - x₀) +
        1 / 2 * deriv (deriv F) x₀ * (newtonOptStep F x₀ - x₀) ^ 2) +
      1 / 2 * deriv (deriv F) x₀ * (x - newtonOptStep F x₀) ^ 2 := by
  unfold newtonOptStep
  field_simp
  ring

/-- AKMM, (10.3), p. 268: when `F″(x₀) < 0`, `x̂` maximises the quadratic model of `F`. -/
theorem eq_10_3_max (F : ℝ → ℝ) {x₀ : ℝ} (hd : deriv (deriv F) x₀ < 0) (x : ℝ) :
    F x₀ + deriv F x₀ * (x - x₀) + 1 / 2 * deriv (deriv F) x₀ * (x - x₀) ^ 2 ≤
      F x₀ + deriv F x₀ * (newtonOptStep F x₀ - x₀) +
        1 / 2 * deriv (deriv F) x₀ * (newtonOptStep F x₀ - x₀) ^ 2 := by
  rw [eq_10_3 F hd.ne x]
  have : 1 / 2 * deriv (deriv F) x₀ * (x - newtonOptStep F x₀) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- AKMM, p. 268: "If `F(x)` is indeed quadratic, `x̂` delivers the solution in one step": for
`F(x) = ax² + bx + c` with `a ≠ 0`, Newton's step from any `x₀` lands on `−b/(2a)`, where
`F′ = 0`. -/
theorem newtonOpt_quadratic_exact {a b c : ℝ} (ha : a ≠ 0) (x₀ : ℝ) :
    newtonOptStep (fun x => a * x ^ 2 + b * x + c) x₀ = -b / (2 * a) ∧
      deriv (fun x => a * x ^ 2 + b * x + c) (-b / (2 * a)) = 0 := by
  have hF : deriv (fun x => a * x ^ 2 + b * x + c) = fun x => 2 * a * x + b := by
    funext x
    have h1 : HasDerivAt (fun x => a * x ^ 2 + b * x + c) (a * (↑2 * x ^ (2 - 1)) + b * 1) x :=
      (((hasDerivAt_pow 2 x).const_mul a).add ((hasDerivAt_id x).const_mul b)).add_const c
    rw [h1.deriv]
    norm_num
    ring
  have hF2 : deriv (fun x => 2 * a * x + b) = fun _ => 2 * a := by
    funext x
    have := ((hasDerivAt_id x).const_mul (2 * a)).add_const b
    simp only [id, mul_one] at this
    exact this.deriv
  unfold newtonOptStep
  rw [hF, hF2]
  constructor
  · field_simp
    ring
  · field_simp
    ring

end AKMM.ComputationalTools
