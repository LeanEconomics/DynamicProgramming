/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.Static
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Richer static models and a first look at dynamics

AKMM, §12.3.2–12.3.3, pp. 335–341.

* **Home production.** At an interior optimum the two first-order conditions hold
  (`hp_focs`), and their ratio is (12.5), `g₂/g₁ = w/A` (`eq_12_5`). For the CES aggregator
  `g = [θc_m^η + (1 − θ)c_h^η]^{1/η}` the partial derivatives give
  `g₂/g₁ = ((1 − θ)/θ)(c_h/c_m)^{η−1}` (`hp_ces_partials`). With `I = 0`, (12.6) holds in the
  corrected form `ℓ_h/ℓ_m = ((1 − θ)/θ)^{1/(1−η)}(w/A)^{η/(η−1)}` (`eq_12_6`); the printed
  exponent `1/(η − 1)` on `(1 − θ)/θ` gives a different value unless `θ = 1/2`
  (`eq_12_6_printed_false`). For `0 < η < 1` the ratio is strictly decreasing in `w/A`
  (`hp_ratio_decreasing`).
* **Household labour supply.** At an interior optimum both members' first-order conditions hold
  (`hh_focs`), so `v′(ℓ_f)/v′(ℓ_m) = w_f/w_m` and `ℓ_f/ℓ_m = (w_f/w_m)^γ` (`hh_relative_hours`).
  The cross-wage elasticity of `ℓ_f` with respect to `w_m` is
  `−γσ(1 + γ)E_m/(c + γσ(E_f + E_m)) < 0`, `E_j = w_jℓ_j` (`hh_cross_wage`); and a lower `ℓ_m`
  raises `ℓ_f` (the added-worker effect, `hh_added_worker`, from `st_income_decreasing`).
* **Leisure in utility.** With `Ũ = u(c) + ṽ(ℓ̄ − ℓ)`, `ṽ(l) = l^{1−1/γ}/(1 − 1/γ)`, high
  non-labour income makes `ℓ = 0` optimal (`lt_corner`); the elasticity of disutility
  `ℓv′(ℓ)/v(ℓ) = 1 + 1/γ` is constant in the benchmark (`lt_benchmark_elasticity`), while that of
  `ṽ(ℓ̄ − ℓ)` is `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ)` and tends to `−∞` as `ℓ → ℓ̄` when `γ > 1` but to `+∞`
  when `γ < 1` (`lt_elasticity`, `lt_elasticity_limits`).
* **Two periods.** With `β(1 + r) = 1` the first-order conditions give `c₁ = c₂` and
  `log ℓ₁ − log ℓ₂ = γ(log w₁ − log w₂)` (`tp_frisch`). Footnote 8 is corrected:
  `log ℓ_t = −γ log ψ + γ log w_t − γσ log c_t` (`footnote_8`, `footnote_8_printed_false`).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-- Fermat's rule on `[0, ∞)`: a maximiser `x > 0` of `f` over `ℓ ≥ 0` where `f` has derivative
`f′` satisfies `f′ = 0`. -/
theorem ext_foc_of_max {f : ℝ → ℝ} {x f' : ℝ} (hx : 0 < x)
    (hmax : ∀ y, 0 ≤ y → f y ≤ f x) (hf : HasDerivAt f f' x) : f' = 0 := by
  refine IsLocalMax.hasDerivAt_eq_zero ?_ hf
  filter_upwards [lt_mem_nhds hx] with y hy using hmax y hy.le

/-! ### Home production -/

/-- AKMM, p. 336, **the first-order conditions of the home-production problem**
`max u(g(ℓ_m w + I, Aℓ_h)) − v(ℓ_m + ℓ_h)`: at a maximiser with `ℓ_m, ℓ_h > 0`,
`u′g₁w = v′` and `u′g₂A = v′`. -/
theorem hp_focs {u v : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {w I A lm lh u' v' g₁ g₂ : ℝ} (hlm : 0 < lm)
    (hlh : 0 < lh) (hu : HasDerivAt u u' (g (lm * w + I) (A * lh)))
    (hv : HasDerivAt v v' (lm + lh))
    (hg₁ : HasDerivAt (fun x => g x (A * lh)) g₁ (lm * w + I))
    (hg₂ : HasDerivAt (fun y => g (lm * w + I) y) g₂ (A * lh))
    (hmax : ∀ a b, 0 ≤ a → 0 ≤ b →
      u (g (a * w + I) (A * b)) - v (a + b) ≤ u (g (lm * w + I) (A * lh)) - v (lm + lh)) :
    u' * g₁ * w = v' ∧ u' * g₂ * A = v' := by
  constructor
  · have hd : HasDerivAt (fun a => u (g (a * w + I) (A * lh)) - v (a + lh))
        (u' * (g₁ * w) - v' * 1) lm := by
      have h1 := hu.comp lm (hg₁.comp lm ((hasDerivAt_mul_const w).add_const I))
      have h2 := hv.comp lm ((hasDerivAt_id lm).add_const lh)
      exact (h1.sub h2).congr_deriv (by simp)
    have := ext_foc_of_max hlm (fun a ha => hmax a lh ha hlh.le) hd
    linarith
  · have hd : HasDerivAt (fun b => u (g (lm * w + I) (A * b)) - v (lm + b))
        (u' * (g₂ * A) - v' * 1) lh := by
      have h1 := hu.comp lh (hg₂.comp lh (hasDerivAt_id lh |>.const_mul A))
      have h2 := hv.comp lh ((hasDerivAt_id lh).const_add lm)
      exact (h1.sub h2).congr_deriv (by simp)
    have := ext_foc_of_max hlh (fun b hb => hmax lm b hlm.le hb) hd
    linarith

/-- AKMM, (12.5), p. 336: dividing the two first-order conditions, `g₂/g₁ = w/A`
(`v′ ≠ 0`, `A ≠ 0`). -/
theorem eq_12_5 {u' v' g₁ g₂ w A : ℝ} (hv : v' ≠ 0) (hA : A ≠ 0) (h₁ : u' * g₁ * w = v')
    (h₂ : u' * g₂ * A = v') : g₂ / g₁ = w / A := by
  have hg₁ : g₁ ≠ 0 := by rintro rfl; simp at h₁; exact hv h₁.symm
  rw [div_eq_div_iff hg₁ hA]
  have : u' ≠ 0 := by rintro rfl; simp at h₁; exact hv h₁.symm
  apply mul_left_cancel₀ this
  linear_combination h₂ - h₁

/-- The CES aggregator `g(c_m, c_h) = [θc_m^η + (1 − θ)c_h^η]^{1/η}` (AKMM, p. 336). -/
noncomputable def cesG (θ η cm ch : ℝ) : ℝ := (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η)

/-- AKMM, p. 336: the partial derivatives of the CES aggregator,
`g₁ = θc_m^{η−1}X^{1/η−1}` and `g₂ = (1 − θ)c_h^{η−1}X^{1/η−1}` (`X = θc_m^η + (1 − θ)c_h^η`),
and their ratio `g₂/g₁ = ((1 − θ)/θ)(c_h/c_m)^{η−1}`. -/
theorem hp_ces_partials {θ η cm ch : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : η ≠ 0)
    (hcm : 0 < cm) (hch : 0 < ch) :
    HasDerivAt (fun x => cesG θ η x ch)
      (θ * cm ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1)) cm ∧
    HasDerivAt (fun y => cesG θ η cm y)
      ((1 - θ) * ch ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1)) ch ∧
    (1 - θ) * ch ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1) /
        (θ * cm ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1)) =
      (1 - θ) / θ * (ch / cm) ^ (η - 1) := by
  have hX : 0 < θ * cm ^ η + (1 - θ) * ch ^ η := by
    have : 0 < 1 - θ := by linarith
    positivity
  refine ⟨?_, ?_, ?_⟩
  · have hin : HasDerivAt (fun x => θ * x ^ η + (1 - θ) * ch ^ η) (θ * (η * cm ^ (η - 1))) cm :=
      ((Real.hasDerivAt_rpow_const (Or.inl hcm.ne')).const_mul θ).add_const _
    have := (Real.hasDerivAt_rpow_const (p := 1 / η) (Or.inl hX.ne')).comp cm hin
    refine this.congr_deriv ?_
    field_simp
  · have hin : HasDerivAt (fun y => θ * cm ^ η + (1 - θ) * y ^ η)
        ((1 - θ) * (η * ch ^ (η - 1))) ch :=
      ((Real.hasDerivAt_rpow_const (Or.inl hch.ne')).const_mul (1 - θ)).const_add _
    have := (Real.hasDerivAt_rpow_const (p := 1 / η) (Or.inl hX.ne')).comp ch hin
    refine this.congr_deriv ?_
    field_simp
  · have hXp : 0 < (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1) := Real.rpow_pos_of_pos hX _
    have hcmp : 0 < cm ^ (η - 1) := Real.rpow_pos_of_pos hcm _
    rw [Real.div_rpow hch.le hcm.le]
    field_simp

/-- AKMM, (12.6), p. 336, **corrected**: with `I = 0` (`c_m = wℓ_m`, `c_h = Aℓ_h`),
`((1 − θ)/θ)(Aℓ_h/(wℓ_m))^{η−1} = w/A` implies
`ℓ_h/ℓ_m = ((1 − θ)/θ)^{1/(1−η)}(w/A)^{η/(η−1)}`. -/
theorem eq_12_6 {θ η w A lm lh : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : η ≠ 1) (hw : 0 < w)
    (hA : 0 < A) (hlm : 0 < lm) (hlh : 0 < lh)
    (h : (1 - θ) / θ * (A * lh / (w * lm)) ^ (η - 1) = w / A) :
    lh / lm = ((1 - θ) / θ) ^ (1 / (1 - η)) * (w / A) ^ (η / (η - 1)) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hη1 : η - 1 ≠ 0 := sub_ne_zero.2 hη
  have hx : 0 < A * lh / (w * lm) := by positivity
  have hk : 0 < (1 - θ) / θ := by positivity
  have hx' : (A * lh / (w * lm)) ^ (η - 1) = (θ / (1 - θ)) * (w / A) := by
    rw [← h]; field_simp
  have hxe : A * lh / (w * lm) = ((θ / (1 - θ)) * (w / A)) ^ (1 / (η - 1)) := by
    rw [← hx', ← Real.rpow_mul hx.le, mul_one_div_cancel hη1, Real.rpow_one]
  have hratio : lh / lm = w / A * (A * lh / (w * lm)) := by field_simp
  rw [hratio, hxe, Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (θ / (1 - θ)) ^ (1 / (η - 1)) = ((1 - θ) / θ) ^ (1 / (1 - η)) := by
    rw [show θ / (1 - θ) = ((1 - θ) / θ)⁻¹ by field_simp, Real.inv_rpow hk.le,
      ← Real.rpow_neg hk.le]
    congr 1
    field_simp
    ring
  have h2 : w / A * (w / A) ^ (1 / (η - 1)) = (w / A) ^ (η / (η - 1)) := by
    have hwA : 0 < w / A := by positivity
    rw [show η / (η - 1) = 1 + 1 / (η - 1) by field_simp; ring, Real.rpow_add hwA,
      Real.rpow_one]
  rw [h1, ← h2]
  ring

/-- AKMM, (12.6), p. 336: **the printed constant is wrong**. The printed
`((1 − θ)/θ)^{1/(η−1)}(w/A)^{η/(η−1)}` equals the correct value of `eq_12_6` only when
`θ = 1/2` (for `0 < θ < 1`, `η ≠ 1`, `w, A > 0`). -/
theorem eq_12_6_printed_false {θ η w A : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : η ≠ 1)
    (hw : 0 < w) (hA : 0 < A) :
    ((1 - θ) / θ) ^ (1 / (η - 1)) * (w / A) ^ (η / (η - 1)) =
        ((1 - θ) / θ) ^ (1 / (1 - η)) * (w / A) ^ (η / (η - 1)) ↔ θ = 1 / 2 := by
  have hk : 0 < (1 - θ) / θ := div_pos (by linarith) hθ0
  have hz : 0 < (w / A) ^ (η / (η - 1)) := Real.rpow_pos_of_pos (by positivity) _
  rw [mul_left_inj' hz.ne']
  have hη1 : η - 1 ≠ 0 := sub_ne_zero.2 hη
  constructor
  · intro h
    have hl := congrArg Real.log h
    rw [Real.log_rpow hk, Real.log_rpow hk] at hl
    have e : 1 / (1 - η) = -(1 / (η - 1)) := by
      rw [show 1 - η = -(η - 1) by ring, div_neg]
    rw [e] at hl
    have : 1 / (η - 1) * Real.log ((1 - θ) / θ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (one_div_ne_zero hη1)
    · rcases Real.log_eq_zero.1 h' with h'' | h'' | h''
      · linarith [hk]
      · field_simp at h''; linarith
      · linarith [hk]
  · intro h
    subst h
    norm_num

/-- AKMM, p. 336: for `0 < η < 1` the exponent `η/(η − 1)` is negative, so `ℓ_h/ℓ_m` in (12.6)
is strictly decreasing in `w/A`. -/
theorem hp_ratio_decreasing {θ η x y : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hx : 0 < x) (hxy : x < y) :
    η / (η - 1) < 0 ∧ ((1 - θ) / θ) ^ (1 / (1 - η)) * y ^ (η / (η - 1)) <
      ((1 - θ) / θ) ^ (1 / (1 - η)) * x ^ (η / (η - 1)) := by
  have he : η / (η - 1) < 0 := div_neg_of_pos_of_neg hη0 (by linarith)
  refine ⟨he, mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx hxy he) ?_⟩
  exact Real.rpow_pos_of_pos (div_pos (by linarith) hθ0) _

/-! ### Household labour supply -/

/-- AKMM, p. 338, **the household's first-order conditions**: at a maximiser with
`ℓ_f, ℓ_m > 0` of `u(w_fℓ_f + w_mℓ_m + I) − v(ℓ_f) − v(ℓ_m)`,
`u′(c)w_f = v′(ℓ_f)` and `u′(c)w_m = v′(ℓ_m)`. -/
theorem hh_focs {u v : ℝ → ℝ} {wf wm I lf lm u' vf vm : ℝ} (hlf : 0 < lf) (hlm : 0 < lm)
    (hu : HasDerivAt u u' (wf * lf + wm * lm + I)) (hvf : HasDerivAt v vf lf)
    (hvm : HasDerivAt v vm lm)
    (hmax : ∀ a b, 0 ≤ a → 0 ≤ b →
      u (wf * a + wm * b + I) - v a - v b ≤ u (wf * lf + wm * lm + I) - v lf - v lm) :
    u' * wf = vf ∧ u' * wm = vm := by
  constructor
  · have hd : HasDerivAt (fun a => u (wf * a + wm * lm + I) - v a - v lm) (u' * wf - vf) lf := by
      have h1 := hu.comp lf ((((hasDerivAt_id lf).const_mul wf).add_const (wm * lm)).add_const I)
      exact ((h1.sub hvf).sub_const (v lm)).congr_deriv (by simp)
    have := ext_foc_of_max hlf (fun a ha => hmax a lm ha hlm.le) hd
    linarith
  · have hd : HasDerivAt (fun b => u (wf * lf + wm * b + I) - v lf - v b) (u' * wm - vm) lm := by
      have h1 := hu.comp lm ((((hasDerivAt_id lm).const_mul wm).const_add (wf * lf)).add_const I)
      exact ((h1.sub_const (v lf)).sub hvm).congr_deriv (by simp)
    have := ext_foc_of_max hlm (fun b hb => hmax lf b hlf.le hb) hd
    linarith

/-- AKMM, p. 338: dividing the first-order conditions, `v′(ℓ_f)/v′(ℓ_m) = w_f/w_m`; with
`v′(ℓ) = ψℓ^{1/γ}`, **relative hours** are `ℓ_f/ℓ_m = (w_f/w_m)^γ`. -/
theorem hh_relative_hours {ψ γ wf wm lf lm lam : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hwf : 0 < wf)
    (hwm : 0 < wm) (hlf : 0 < lf) (hlm : 0 < lm) (hlam : 0 < lam)
    (hf : lam * wf = ψ * lf ^ (1 / γ)) (hm : lam * wm = ψ * lm ^ (1 / γ)) :
    ψ * lf ^ (1 / γ) / (ψ * lm ^ (1 / γ)) = wf / wm ∧ lf / lm = (wf / wm) ^ γ := by
  have h1 : ψ * lf ^ (1 / γ) / (ψ * lm ^ (1 / γ)) = wf / wm := by
    rw [← hf, ← hm]; field_simp
  refine ⟨h1, ?_⟩
  have h2 : (lf / lm) ^ (1 / γ) = wf / wm := by
    rw [Real.div_rpow hlf.le hlm.le, ← h1]; field_simp
  rw [← h2, ← Real.rpow_mul (by positivity), one_div_mul_cancel hγ.ne', Real.rpow_one]

/-- AKMM, p. 338: **the cross-wage effect is negative**. Along `w_m(s) = w_me^s` with both
members' conditions (12.1)-type holding near `0` (`u = c^{1−σ}/(1 − σ)`, `σ > 0`), the
elasticity of `ℓ_f` with respect to `w_m` is `−γσ(1 + γ)E_m/(c + γσ(E_f + E_m)) < 0`,
`E_j = w_jℓ_j`, `c = E_f + E_m + I`. -/
theorem hh_cross_wage {ψ γ σ wf wm I lf' lm' : ℝ} {lf lm : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 < σ) (hwf : 0 < wf) (hwm : 0 < wm) (hlf : 0 < lf 0) (hlm : 0 < lm 0)
    (hc : 0 < wf * lf 0 + wm * lm 0 + I) (hdf : HasDerivAt lf lf' 0) (hdm : HasDerivAt lm lm' 0)
    (hff : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * lf s ^ (1 / γ) /
      (wf * lf s + (wm * Real.exp s * lm s + I)) ^ (-σ) = wf)
    (hfm : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * lm s ^ (1 / γ) /
      (wm * Real.exp s * lm s + (wf * lf s + I)) ^ (-σ) = wm * Real.exp s) :
    HasDerivAt (fun s => Real.log (lf s)) (-(γ * σ * (1 + γ) * (wm * lm 0)) /
      (wf * lf 0 + wm * lm 0 + I + γ * σ * (wf * lf 0 + wm * lm 0))) 0 ∧
    -(γ * σ * (1 + γ) * (wm * lm 0)) /
      (wf * lf 0 + wm * lm 0 + I + γ * σ * (wf * lf 0 + wm * lm 0)) < 0 := by
  have hEm : HasDerivAt (fun s => wm * Real.exp s * lm s + I) (wm * lm 0 + wm * lm') 0 := by
    have := ((st_exp_path wm).mul hdm).add_const I
    refine this.congr_deriv ?_
    rw [Real.exp_zero, mul_one]
  have hEf : HasDerivAt (fun s => wf * lf s + I) (wf * lf') 0 :=
    (hdf.const_mul wf).add_const I
  have hc1 : 0 < wf * lf 0 + (wm * Real.exp 0 * lm 0 + I) := by
    rw [Real.exp_zero, mul_one]; linarith
  have hc2 : 0 < wm * Real.exp 0 * lm 0 + (wf * lf 0 + I) := by
    rw [Real.exp_zero, mul_one]; linarith
  have hwm0 : 0 < wm * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hwm
  have kf := st_path_poly (w := fun _ => wf) (w' := 0) hψ hγ hwf hlf hc1
    (hasDerivAt_const _ _) hEm hdf hff
  have km := st_path_poly hψ hγ hwm0 hlm hc2 (st_exp_path wm) hEf hdm hfm
  simp only [Real.exp_zero, mul_one, zero_mul, zero_add, mul_zero] at kf km
  set c := wf * lf 0 + wm * lm 0 + I with hcdef
  have hf : c * lf' + γ * σ * lf 0 * (wf * lf' + (wm * lm 0 + wm * lm')) = 0 := by
    have h : wf * (c * lf' + γ * σ * lf 0 * (wf * lf' + (wm * lm 0 + wm * lm'))) = 0 := by
      rw [hcdef]; linear_combination kf
    exact (mul_eq_zero.1 h).resolve_left hwf.ne'
  have hm : c * lm' + γ * σ * lm 0 * (wm * lm 0 + wm * lm' + wf * lf') = γ * lm 0 * c := by
    have h : wm * (c * lm' + γ * σ * lm 0 * (wm * lm 0 + wm * lm' + wf * lf') -
        γ * lm 0 * c) = 0 := by
      rw [hcdef]; linear_combination km
    linarith [(mul_eq_zero.1 h).resolve_left hwm.ne']
  have hD : 0 < c + γ * σ * (wf * lf 0 + wm * lm 0) := by
    have : 0 ≤ γ * σ * (wf * lf 0 + wm * lm 0) := by positivity
    linarith
  have hgoal : c * (lf' * (c + γ * σ * (wf * lf 0 + wm * lm 0)) +
      γ * σ * (1 + γ) * (wm * lm 0) * lf 0) = 0 := by
    linear_combination (c + γ * σ * wm * lm 0) * hf - (γ * σ * wm * lf 0) * hm
  have hl : lf' = -(γ * σ * (1 + γ) * (wm * lm 0) * lf 0) /
      (c + γ * σ * (wf * lf 0 + wm * lm 0)) := by
    rw [eq_div_iff hD.ne']
    linarith [(mul_eq_zero.1 hgoal).resolve_left hc.ne']
  refine ⟨(hdf.log hlf.ne').congr_deriv ?_, div_neg_of_neg_of_pos ?_ hD⟩
  · rw [hl]; field_simp
  · have : 0 < γ * σ * (1 + γ) * (wm * lm 0) := by positivity
    linarith

/-- AKMM, p. 333 (the income effect): the solution of (12.1) is strictly decreasing in
non-labour income: if `ℓ₁` solves (12.1) at `I₁` and `ℓ₂` at `I₂ > I₁`, then `ℓ₂ < ℓ₁`. -/
theorem st_income_decreasing {ψ γ σ w I₁ I₂ l₁ l₂ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 < σ)
    (hw : 0 < w) (hl₁ : 0 < l₁) (hc₁ : 0 < w * l₁ + I₁)
    (hc₂ : 0 < w * l₂ + I₂) (hI : I₁ < I₂)
    (h₁ : ψ * l₁ ^ (1 / γ) / (w * l₁ + I₁) ^ (-σ) = w)
    (h₂ : ψ * l₂ ^ (1 / γ) / (w * l₂ + I₂) ^ (-σ) = w) : l₂ < l₁ := by
  rw [st_foc_form hc₁] at h₁
  rw [st_foc_form hc₂] at h₂
  by_contra hle
  have hle' : l₁ ≤ l₂ := not_lt.1 hle
  have a1 : l₁ ^ (1 / γ) ≤ l₂ ^ (1 / γ) := Real.rpow_le_rpow hl₁.le hle' (by positivity)
  have a2 : (w * l₁ + I₁) ^ σ < (w * l₂ + I₂) ^ σ :=
    Real.rpow_lt_rpow hc₁.le (by nlinarith) hσ
  have a3 : 0 < l₁ ^ (1 / γ) := Real.rpow_pos_of_pos hl₁ _
  have a4 : 0 < (w * l₂ + I₂) ^ σ := Real.rpow_pos_of_pos hc₂ _
  have : l₁ ^ (1 / γ) * (w * l₁ + I₁) ^ σ < l₂ ^ (1 / γ) * (w * l₂ + I₂) ^ σ :=
    calc l₁ ^ (1 / γ) * (w * l₁ + I₁) ^ σ < l₁ ^ (1 / γ) * (w * l₂ + I₂) ^ σ :=
          mul_lt_mul_of_pos_left a2 a3
      _ ≤ l₂ ^ (1 / γ) * (w * l₂ + I₂) ^ σ := mul_le_mul_of_nonneg_right a1 a4.le
  have := mul_lt_mul_of_pos_left this hψ
  rw [← mul_assoc, ← mul_assoc] at this
  linarith

/-- AKMM, p. 338, **the added-worker effect**: in the female member's condition the male's
earnings `w_mℓ_m` act as non-labour income, so an exogenous fall in `ℓ_m` raises `ℓ_f`. -/
theorem hh_added_worker {ψ γ σ wf wm I lm₁ lm₂ lf₁ lf₂ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 < σ) (hwf : 0 < wf) (hwm : 0 < wm) (hlm : lm₂ < lm₁) (hf₂ : 0 < lf₂)
    (hc₁ : 0 < wf * lf₁ + (wm * lm₁ + I)) (hc₂ : 0 < wf * lf₂ + (wm * lm₂ + I))
    (h₁ : ψ * lf₁ ^ (1 / γ) / (wf * lf₁ + (wm * lm₁ + I)) ^ (-σ) = wf)
    (h₂ : ψ * lf₂ ^ (1 / γ) / (wf * lf₂ + (wm * lm₂ + I)) ^ (-σ) = wf) : lf₁ < lf₂ :=
  st_income_decreasing hψ hγ hσ hwf hf₂ hc₂ hc₁ (by nlinarith) h₂ h₁

/-! ### Leisure in the utility function -/

/-- AKMM, p. 339: in the benchmark the elasticity of disutility `ℓv′(ℓ)/v(ℓ) = 1 + 1/γ` is
constant (`ℓ > 0`). -/
theorem lt_benchmark_elasticity {ψ γ l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hl : 0 < l) :
    l * (ψ * l ^ (1 / γ)) / disutil ψ γ l = 1 + 1 / γ := by
  unfold disutil
  have h : l * l ^ (1 / γ) = l ^ (1 + 1 / γ) := by
    rw [Real.rpow_add hl, Real.rpow_one]
  have hp : 0 < l ^ (1 + 1 / γ) := Real.rpow_pos_of_pos hl _
  have hg : 0 < 1 + 1 / γ := by positivity
  rw [show l * (ψ * l ^ (1 / γ)) = ψ * (l * l ^ (1 / γ)) by ring, h]
  field_simp

/-- AKMM, p. 339: `ṽ(l) = l^{1−1/γ}/(1 − 1/γ)` has `ṽ′(l) = l^{−1/γ}` (`l > 0`, `γ ≠ 1`). -/
theorem lt_vtilde_hasDerivAt {γ l : ℝ} (hγ : γ ≠ 1) (hγ0 : 0 < γ) (hl : 0 < l) :
    HasDerivAt (fun x => x ^ (1 - 1 / γ) / (1 - 1 / γ)) (l ^ (-(1 / γ))) l := by
  have hk : 1 - 1 / γ ≠ 0 := by
    intro h
    have : 1 / γ = 1 := by linarith
    exact hγ (by field_simp at this; linarith)
  have := (Real.hasDerivAt_rpow_const (p := 1 - 1 / γ) (Or.inl hl.ne')).div_const (1 - 1 / γ)
  refine this.congr_deriv ?_
  rw [show 1 - 1 / γ - 1 = -(1 / γ) by ring]
  field_simp

/-- AKMM, p. 339: **with utility of leisure, `ℓ = 0` can be optimal**. For
`Ũ = u(wℓ + I) + ṽ(ℓ̄ − ℓ)` with `I > 0`, if `wI^{−σ} ≤ ℓ̄^{−1/γ}` (non-labour income high
enough) then `ℓ = 0` maximises `Ũ` over `[0, ℓ̄)`. -/
theorem lt_corner {γ σ w I lbar : ℝ} (hγ : γ ≠ 1) (hγ0 : 0 < γ) (hσ : 0 < σ) (hw : 0 < w)
    (hI : 0 < I) (hlbar : 0 < lbar) (hhigh : w * I ^ (-σ) ≤ lbar ^ (-(1 / γ))) :
    ∀ l, 0 ≤ l → l < lbar →
      crraU σ (w * l + I) + (lbar - l) ^ (1 - 1 / γ) / (1 - 1 / γ) ≤
        crraU σ (w * 0 + I) + (lbar - 0) ^ (1 - 1 / γ) / (1 - 1 / γ) := by
  set f : ℝ → ℝ := fun l => crraU σ (w * l + I) + (lbar - l) ^ (1 - 1 / γ) / (1 - 1 / γ)
  have hder : ∀ l, 0 ≤ l → l < lbar →
      HasDerivAt f (w * (w * l + I) ^ (-σ) - (lbar - l) ^ (-(1 / γ))) l := by
    intro l hl0 hl1
    have hc : 0 < w * l + I := by positivity
    have h1 := (st_crraU_hasDerivAt (σ := σ) hc).comp l
      (((hasDerivAt_id l).const_mul w).add_const I)
    have h2 := (lt_vtilde_hasDerivAt hγ hγ0 (by linarith : 0 < lbar - l)).comp l
      ((hasDerivAt_id l).const_sub lbar)
    exact (h1.add h2).congr_deriv (by simp; ring)
  have hanti : AntitoneOn f (Set.Ico 0 lbar) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 lbar)
    · intro x hx
      exact (hder x hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (hder x hx.1.le hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hder x hx.1.le hx.2).deriv]
      have a1 : (w * x + I) ^ (-σ) ≤ I ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hI (by nlinarith [hx.1]) (by linarith)
      have a2 : lbar ^ (-(1 / γ)) ≤ (lbar - x) ^ (-(1 / γ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.2]) (by linarith [hx.1])
          (by have : 0 < 1 / γ := by positivity
              linarith)
      have : w * (w * x + I) ^ (-σ) ≤ w * I ^ (-σ) := mul_le_mul_of_nonneg_left a1 hw.le
      linarith
  intro l hl0 hl1
  exact hanti ⟨le_rfl, hlbar⟩ ⟨hl0, hl1⟩ hl0

/-- AKMM, p. 339: the elasticity of `ṽ(ℓ̄ − ℓ)` with respect to time worked,
`−ℓṽ′(ℓ̄ − ℓ)/ṽ(ℓ̄ − ℓ)`, equals `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ)` (`ℓ < ℓ̄`, `γ ≠ 1`); it is not
constant. -/
theorem lt_elasticity {γ l lbar : ℝ} (hγ : γ ≠ 1) (hγ0 : 0 < γ) (hl : l < lbar) :
    -l * (lbar - l) ^ (-(1 / γ)) / ((lbar - l) ^ (1 - 1 / γ) / (1 - 1 / γ)) =
      -(1 - 1 / γ) * l / (lbar - l) := by
  have hx : 0 < lbar - l := by linarith
  have hk : 1 - 1 / γ ≠ 0 := by
    intro h
    have : 1 / γ = 1 := by linarith
    exact hγ (by field_simp at this; linarith)
  have h : (lbar - l) ^ (1 - 1 / γ) = (lbar - l) * (lbar - l) ^ (-(1 / γ)) := by
    rw [show 1 - 1 / γ = 1 + -(1 / γ) by ring, Real.rpow_add hx, Real.rpow_one]
  have hp : 0 < (lbar - l) ^ (-(1 / γ)) := Real.rpow_pos_of_pos hx _
  rw [h]
  field_simp

/-- AKMM, p. 339, **corrected**: "This value approaches minus infinity as `ℓ` approaches `ℓ̄`".
As `ℓ → ℓ̄⁻`, `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ) → −∞` when `γ > 1`, but `→ +∞` when `γ < 1` (then
`ṽ < 0`); in both cases it is unbounded. -/
theorem lt_elasticity_limits {γ lbar : ℝ} (hlbar : 0 < lbar) :
    (1 < γ → Tendsto (fun l => -(1 - 1 / γ) * l / (lbar - l)) (𝓝[<] lbar) atBot) ∧
      (0 < γ → γ < 1 → Tendsto (fun l => -(1 - 1 / γ) * l / (lbar - l)) (𝓝[<] lbar) atTop) := by
  have hbase : Tendsto (fun l => l * (lbar - l)⁻¹) (𝓝[<] lbar) atTop := by
    have h1 : Tendsto (fun l : ℝ => l) (𝓝[<] lbar) (𝓝 lbar) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 : Tendsto (fun l : ℝ => lbar - l) (𝓝[<] lbar) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun l : ℝ => lbar - l) (𝓝 lbar) (𝓝 (lbar - lbar)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      · filter_upwards [self_mem_nhdsWithin] with l hl
        exact sub_pos.2 (Set.mem_Iio.1 hl)
    exact h1.pos_mul_atTop hlbar (tendsto_inv_nhdsGT_zero.comp h2)
  have heq : ∀ l, -(1 - 1 / γ) * l / (lbar - l) = -(1 - 1 / γ) * (l * (lbar - l)⁻¹) :=
    fun l => by rw [div_eq_mul_inv]; ring
  constructor
  · intro hγ
    have hk : -(1 - 1 / γ) < 0 := by
      have : 1 / γ < 1 := by rw [div_lt_one (by linarith)]; exact hγ
      linarith
    simp only [heq]
    exact hbase.const_mul_atTop_of_neg hk
  · intro hγ0 hγ1
    have hk : 0 < -(1 - 1 / γ) := by
      have : 1 < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
      linarith
    simp only [heq]
    exact hbase.const_mul_atTop hk

/-! ### A two-period model -/

/-- AKMM, p. 341, **the Frisch elasticity in two periods**: with `β = 1/(1 + r)`, the
first-order conditions `c₁^{−σ} = λ = c₂^{−σ}`, `ψℓ_t^{1/γ} = λw_t` give `c₁ = c₂`,
`(ℓ₁/ℓ₂)^{1/γ} = w₁/w₂` and `log ℓ₁ − log ℓ₂ = γ(log w₁ − log w₂)`. -/
theorem tp_frisch {ψ γ σ lam c₁ c₂ l₁ l₂ w₁ w₂ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : σ ≠ 0)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (h₁ : c₁ ^ (-σ) = lam) (h₂ : c₂ ^ (-σ) = lam) (h₃ : ψ * l₁ ^ (1 / γ) = lam * w₁)
    (h₄ : ψ * l₂ ^ (1 / γ) = lam * w₂) :
    c₁ = c₂ ∧ (l₁ / l₂) ^ (1 / γ) = w₁ / w₂ ∧
      Real.log l₁ - Real.log l₂ = γ * (Real.log w₁ - Real.log w₂) := by
  have hlam : 0 < lam := by rw [← h₁]; exact Real.rpow_pos_of_pos hc₁ _
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg Real.log (h₁.trans h₂.symm)
    rw [Real.log_rpow hc₁, Real.log_rpow hc₂] at this
    have hl : Real.log c₁ = Real.log c₂ := by
      have := mul_left_cancel₀ (neg_ne_zero.2 hσ) this
      exact this
    exact Real.log_injOn_pos hc₁ hc₂ hl
  · rw [Real.div_rpow hl₁.le hl₂.le]
    have e₁ : l₁ ^ (1 / γ) = lam * w₁ / ψ := by rw [← h₃]; field_simp
    have e₂ : l₂ ^ (1 / γ) = lam * w₂ / ψ := by rw [← h₄]; field_simp
    rw [e₁, e₂]; field_simp
  · have e₁ := congrArg Real.log h₃
    have e₂ := congrArg Real.log h₄
    rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₁ _).ne', Real.log_rpow hl₁,
      Real.log_mul hlam.ne' hw₁.ne'] at e₁
    rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₂ _).ne', Real.log_rpow hl₂,
      Real.log_mul hlam.ne' hw₂.ne'] at e₂
    have : 1 / γ * (Real.log l₁ - Real.log l₂) = Real.log w₁ - Real.log w₂ := by linarith
    rw [← this]
    field_simp

/-- AKMM, footnote 8, p. 341, **corrected**: from `c_t^{−σ} = λ` and `ψℓ_t^{1/γ} = λw_t`,
`log ℓ_t = −γ log ψ + γ log w_t − γσ log c_t`. -/
theorem footnote_8 {ψ γ σ lam c l w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hc : 0 < c) (hl : 0 < l)
    (hw : 0 < w) (h₁ : c ^ (-σ) = lam) (h₂ : ψ * l ^ (1 / γ) = lam * w) :
    Real.log l = -γ * Real.log ψ + γ * Real.log w - γ * σ * Real.log c := by
  have hlam : 0 < lam := by rw [← h₁]; exact Real.rpow_pos_of_pos hc _
  have e := congrArg Real.log h₂
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl,
    Real.log_mul hlam.ne' hw.ne', ← h₁, Real.log_rpow hc] at e
  have : Real.log l = γ * (1 / γ * Real.log l) := by field_simp
  rw [this]
  have : 1 / γ * Real.log l = -σ * Real.log c + Real.log w - Real.log ψ := by linarith
  rw [this]
  ring

/-- AKMM, footnote 8, p. 341: **the printed equation is false**. The printed
`log ℓ_t = γ/ψ + γ log w_t + γ(1 − σ) log c_t` fails at `ψ = γ = σ = w = 1`, `c = e`,
`λ = e^{−1}`, `ℓ = e^{−1}`, where both first-order conditions hold. -/
theorem footnote_8_printed_false :
    Real.exp 1 ^ (-(1 : ℝ)) = Real.exp (-1) ∧
      1 * Real.exp (-1) ^ (1 / (1 : ℝ)) = Real.exp (-1) * 1 ∧
      Real.log (Real.exp (-1)) ≠
        1 / 1 + 1 * Real.log 1 + 1 * (1 - 1) * Real.log (Real.exp 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_neg_one, Real.exp_neg]
  · simp
  · rw [Real.log_exp]; norm_num

end AKMM.LaborSupply
