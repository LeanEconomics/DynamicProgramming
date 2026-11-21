/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The introduction to Chapter 20: limits of time-additive expected utility

Miao, Part IV introduction (p. 673) and the introduction to Chapter 20, pp. 675–677. The Part IV
introduction is a description of the topics of Chapters 20–22 and contains no mathematical
claim. The chapter introduction lists four shortcomings of time-additive expected utility; the
three that the text derives are formalised.

* `ku_intro_partial`, `ku_intro_mrs_const`: for `U(c) = ∑_{t<T} βᵗu(c_t)` the partial derivative
  in `c_s` is `βˢu'(c_s)`, so at constant consumption the marginal rate of substitution between
  consecutive dates is `1/β`, whatever the level of consumption (p. 675).
* `ku_intro_knife_edge`, `ku_intro_growth`: with a fixed gross interest rate `R` the Euler
  equation `u'(c_t) = βRu'(c_{t+1})` admits a constant path only if `βR = 1`; for `βR > 1` and
  strictly concave `u` consumption grows without bound being reached (p. 675).
* `ku_intro_rra`, `ku_intro_eis`: for power utility `u(c) = c^{1−γ}/(1 − γ)` the coefficient of
  relative risk aversion is `γ` and `log MRS_{0,1} = γ log(c₁/c₀) − log β`, so the elasticity of
  intertemporal substitution `d log(c₁/c₀)/d log MRS_{0,1}` is `1/γ` (p. 676).
* `ku_intro_timing`: in the two-period coin example (p. 676) early and late resolution give the
  same expected utility.
-/

namespace Miao.RecursiveUtility

open Filter Topology

/-- Miao, p. 675: for the time-additive utility `U(c) = ∑_{t<T} βᵗu(c_t)` the partial derivative
in `c_s`, `s < T`, is `βˢu'(c_s)`. -/
theorem ku_intro_partial {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (β : ℝ) (T : ℕ)
    (c : ℕ → ℝ) {s : ℕ} (hs : s < T) :
    HasDerivAt (fun x => ∑ t ∈ Finset.range T, β ^ t * u (Function.update c s x t))
      (β ^ s * u' (c s)) (c s) := by
  have h : ∀ t ∈ Finset.range T, HasDerivAt (fun x => β ^ t * u (Function.update c s x t))
      (if t = s then β ^ s * u' (c s) else 0) (c s) := by
    intro t _
    by_cases hts : t = s
    · subst hts
      simp only [Function.update_self, ↓reduceIte]
      exact (hu (c t)).const_mul _
    · simp only [Function.update_of_ne hts, hts, ↓reduceIte]
      exact hasDerivAt_const _ _
  have h2 := HasDerivAt.fun_sum h
  rw [Finset.sum_ite_eq' (Finset.range T) s] at h2
  simpa [hs] using h2

/-- Miao, p. 675: at constant consumption `c_s = c_{s+1} = x` the marginal rate of substitution
`β^s u'(x)/(β^{s+1} u'(x))` between consecutive dates is `1/β`, independent of `x`. -/
theorem ku_intro_mrs_const {β ux : ℝ} (hβ : β ≠ 0) (hux : ux ≠ 0) (s : ℕ) :
    β ^ s * ux / (β ^ (s + 1) * ux) = 1 / β := by
  rw [pow_succ]
  field_simp

/-- Miao, p. 675: with a fixed gross interest rate `R`, a constant consumption path satisfies the
Euler equation `u'(c_t) = βRu'(c_{t+1})` iff `βR = 1` (the knife-edge case), when `u' > 0`. -/
theorem ku_intro_knife_edge {β R ux : ℝ} (hux : 0 < ux) : ux = β * R * ux ↔ β * R = 1 := by
  constructor
  · intro h
    have : (β * R - 1) * ux = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hux.ne'
  · intro h
    rw [h, one_mul]

/-- Miao, p. 675: if `βR > 1`, `u'` is positive and strictly decreasing, then the Euler equation
`u'(c_t) = βRu'(c_{t+1})` forces `c_{t+1} > c_t`: the consumer keeps saving. -/
theorem ku_intro_growth {u' : ℝ → ℝ} (hpos : ∀ x, 0 < u' x) (hanti : StrictAnti u') {β R : ℝ}
    (hβR : 1 < β * R) {c₀ c₁ : ℝ} (heu : u' c₀ = β * R * u' c₁) : c₀ < c₁ := by
  by_contra h
  have h1 : u' c₀ ≤ u' c₁ := hanti.antitone (not_lt.1 h)
  have h2 := hpos c₁
  nlinarith

/-- Miao, p. 676: for power utility `u(c) = c^{1−γ}/(1 − γ)`, `c > 0`, `γ ≠ 1`, the derivatives
are `u'(c) = c^{−γ}` and `u''(c) = −γc^{−γ−1}`, and the coefficient of relative risk aversion
`−cu''(c)/u'(c)` equals `γ`. -/
theorem ku_intro_rra {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun x => x ^ (1 - γ) / (1 - γ)) (c ^ (-γ)) c ∧
      HasDerivAt (fun x => x ^ (-γ)) (-γ * c ^ (-γ - 1)) c ∧
      -c * (-γ * c ^ (-γ - 1)) / c ^ (-γ) = γ := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  refine ⟨?_, ?_, ?_⟩
  · have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
    convert this using 1
    rw [show (1 : ℝ) - γ - 1 = -γ by ring]
    field_simp
  · exact Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  · have e : c ^ (-γ - 1) = c ^ (-γ) * c⁻¹ := by
      rw [Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv]
    have hcg : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc _
    rw [e]
    field_simp

/-- Miao, p. 676: for `U = u(c₀) + βu(c₁)` with power utility, the marginal rate of substitution
`MRS_{0,1} = u'(c₀)/(βu'(c₁)) = c₀^{−γ}/(βc₁^{−γ})` satisfies
`log MRS_{0,1} = γ log(c₁/c₀) − log β`; hence `log(c₁/c₀) = (log MRS_{0,1} + log β)/γ` and the
elasticity of intertemporal substitution is `1/γ`, the inverse of the coefficient of relative
risk aversion. -/
theorem ku_intro_eis {β γ c₀ c₁ : ℝ} (hβ : 0 < β) (hγ : γ ≠ 0) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))) = γ * Real.log (c₁ / c₀) - Real.log β ∧
      HasDerivAt (fun m => (m + Real.log β) / γ) (1 / γ)
        (Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ)))) ∧
      (Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))) + Real.log β) / γ = Real.log (c₁ / c₀) := by
  have h0 : 0 < c₀ ^ (-γ) := Real.rpow_pos_of_pos hc₀ _
  have h1 : 0 < c₁ ^ (-γ) := Real.rpow_pos_of_pos hc₁ _
  have hlog : Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))) = γ * Real.log (c₁ / c₀) - Real.log β := by
    rw [Real.log_div h0.ne' (by positivity), Real.log_mul hβ.ne' h1.ne', Real.log_rpow hc₀,
      Real.log_rpow hc₁, Real.log_div hc₁.ne' hc₀.ne']
    ring
  refine ⟨hlog, ?_, ?_⟩
  · have := ((hasDerivAt_id (Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))))).add_const
      (Real.log β)).div_const γ
    simpa using this
  · rw [hlog]
    field_simp
    ring

/-- Miao, p. 676: the coin example. Flipping the coin at date 0 (consumption `(c₀, c₁¹)` or
`(c₀, c₁²)`) and flipping it at date 1 give the same time-additive expected utility
`u(c₀) + β(u(c₁¹) + u(c₁²))/2`. -/
theorem ku_intro_timing (u : ℝ → ℝ) (β c₀ c₁₁ c₁₂ : ℝ) :
    (1 / 2) * (u c₀ + β * u c₁₁) + (1 / 2) * (u c₀ + β * u c₁₂) =
      u c₀ + β * ((1 / 2) * u c₁₁ + (1 / 2) * u c₁₂) := by
  ring

end Miao.RecursiveUtility
