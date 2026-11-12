/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.ExcessCost
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Figure 15.6: the labour tax and the two types' consumption along (15.14)

AKMM, §15.3.2, Figure 15.6, Panels A–C, p. 450.

No consumption tax, no transfers, `G = gy`, and the labour tax adjusts by (15.14). Write
`ρ = (1 − β)/β`, `c = ρ + δ`, `s = α(1 − τ_k)/(ρ + δ(1 − τ_k))` (`lrS`), `s₀ = α/c` its value at
`τ_k = 0`, `m = (1 − τ_ℓ)(1 − α) = 1 − g − cs` (`inc_m_eq`) and `e = α(1 + φ)/(1 − α)`, so that
`y = m^φs^e` (15.13), `c_w = my = m^{1+φ}s^e` (`fig156Cw`) and `c_k = ρsy = ρm^φs^{1+e}`
(`fig156Ck`). All results hold for every `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` (and the
stated ranges of `g`), not only at the figure's calibration.

* **Panel A.** `τ_ℓ` is strictly decreasing in `τ_k` on `τ_k < 1` (`fig156_tauL_strictAntiOn`),
  concave (`fig156_tauL_concaveOn`), strictly concave when `δ > 0`
  (`fig156_tauL_strictConcaveOn`); it equals `g/(1 − α)` at `τ_k = 0` and `(g − α)/(1 − α)` at
  `τ_k = 1` (`fig156_tauL_endpoints`), and for `0 < g < α` it changes sign exactly at
  `τ_k = g(ρ + δ)/(ρα + gδ) ∈ (0, 1)` (`fig156_tauL_neg_iff`).
* **The one-variable lemma.** `h(s) = (K − cs)^a s^b` (`fig156Hump`) is strictly increasing on
  `(0, s̄]` and strictly decreasing on `[s̄, K/c)`, `s̄ = bK/((a + b)c)`
  (`fig156_hump_strictMonoOn`, `fig156_hump_strictAntiOn`); `s(τ_k) = Ks₀` exactly at
  `τ_k = (1 − K)(ρ + δ)/(ρ + δ(1 − K))` (`fig156_s_eq`).
* **Panel B: `c_w` is hump-shaped.** For `0 < g < 1 − α` (`τ_ℓ(0) < 1`), `c_w` is strictly
  increasing on `[0, τ_w]` and strictly decreasing on `[τ_w, 1)`, with
  `τ_w = g(ρ + δ)/(ρ + δg) ∈ (0, 1)` (`fig156_cw_hump`); the peak is a strict global maximum on
  `[0, 1)` (`fig156_cw_isMaxOn`) and is where `τ_ℓ = g`, i.e. labour and capital income are taxed
  at the same average rate `g` (`fig156_cw_peak_tauL`).
* **Panel C: `c_k` is maximal at `τ_k = 0` iff `g ≤ (1 − α)/(1 + αφ)`.** Under this condition
  `c_k` is strictly decreasing on `[0, 1)` (`fig156_ck_strictAntiOn`). For
  `(1 − α)/(1 + αφ) < g < 1 − α` it is hump-shaped instead, rising on `[0, τ_c]` and falling on
  `[τ_c, 1)`, `τ_c = (1 − K)(ρ + δ)/(ρ + δ(1 − K)) ∈ (0, 1)`, `K = (1 + αφ)(1 − g)/((1 + φ)α)`
  (`fig156_ck_hump`), so `c_k(τ_c) > c_k(0)`. Hence the exact statement
  (`fig156_ck_max_at_zero_iff`). The book's claim holds at its parameters (`g = .2` is below
  `.67/1.33`), but not in general: at the parameters of the counterexample to the minimality of
  the excess cost (`inc_excess_cost_not_min_at_zero`: `α = 1/2`, `β = 2/3`, `δ = 1/10`, `φ = 1`,
  `g = 2/5 > 1/3`), `c_k(1/5) > c_k(0)` (`fig156_ck_not_max_at_zero`).

Departures: the book states the claims at its calibration; the hump of `c_w` needs `g > 0` and
`τ_ℓ(0) < 1`, and the maximality of `c_k` at `τ_k = 0` needs `g ≤ (1 − α)/(1 + αφ)` (correction
8 in `docs/corrections.md`).
-/

namespace AKMM.FiscalPolicy

open Real Set

/-! ### Panel A: the labour tax along (15.14) -/

/-- AKMM, p. 450, Figure 15.6, Panel A: along (15.14), `τ_ℓ = (g − α + (ρ + δ)s)/(1 − α)`. -/
theorem fig156_tauL_eq {α β δ g τk : ℝ} (hα : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hτk : τk < 1) :
    incTauL α β δ g τk = (g - α + (lrRho β + δ) * lrS α β δ τk) / (1 - α) := by
  have h := inc_m_eq (g := g) hα hβ0 hβ1 hδ hτk
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold incM at h
  rw [eq_div_iff h1]
  linear_combination (-1 : ℝ) * h

/-- AKMM, p. 450, Figure 15.6, Panel A: the budget-balancing labour tax is strictly decreasing
in the capital tax on `τ_k < 1`. -/
theorem fig156_tauL_strictAntiOn {α β δ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : StrictAntiOn (incTauL α β δ g) (Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ ha hb hab
  rw [fig156_tauL_eq hα1 hβ0 hβ1 hδ ha, fig156_tauL_eq hα1 hβ0 hβ1 hδ hb]
  have h1 : 0 < 1 - α := by linarith
  apply div_lt_div_of_pos_right _ h1
  nlinarith

/-- The convexity gap of `τ ↦ τ/(ρ + δ − δτ)`: for `E(τ) = ρ + δ − δτ`,
`a f(x) + b f(y) − f(ax + by) = (ρ + δ)abδ(x − y)²/(E(x)E(y)E(ax + by))` when `a + b = 1`. -/
theorem fig156_gap {ρ δ a b x y : ℝ} (hab : a + b = 1) (hx : ρ + δ - δ * x ≠ 0)
    (hy : ρ + δ - δ * y ≠ 0) (hz : ρ + δ - δ * (a * x + b * y) ≠ 0) :
    a * (x / (ρ + δ - δ * x)) + b * (y / (ρ + δ - δ * y)) -
        (a * x + b * y) / (ρ + δ - δ * (a * x + b * y)) =
      (ρ + δ) * a * b * δ * (x - y) ^ 2 /
        ((ρ + δ - δ * x) * (ρ + δ - δ * y) * (ρ + δ - δ * (a * x + b * y))) := by
  obtain rfl : b = 1 - a := by linarith
  rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ hx hy, div_sub_div _ _ (mul_ne_zero hx hy) hz,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hx hy) hz) (mul_ne_zero (mul_ne_zero hx hy) hz)]
  ring

/-- `τ_ℓ` in terms of `f(τ) = τ/(ρ + δ − δτ)`: `τ_ℓ = (g − ραf(τ))/(1 − α)`. -/
theorem fig156_tauL_f {α β δ g τk : ℝ} :
    incTauL α β δ g τk =
      (g - lrRho β * α * (τk / (lrRho β + δ - δ * τk))) / (1 - α) := by
  unfold incTauL incBud
  congr 1
  rw [show lrRho β + (1 - τk) * δ = lrRho β + δ - δ * τk by ring]
  ring

/-- AKMM, p. 450, Figure 15.6, Panel A: `τ_ℓ` is concave in `τ_k` on `τ_k < 1` (for `δ ≥ 0`;
it is affine when `δ = 0`). -/
theorem fig156_tauL_concaveOn {α β δ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : ConcaveOn ℝ (Iio 1) (incTauL α β δ g) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  refine ⟨convex_Iio 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : x < 1 := hx
  have hy' : y < 1 := hy
  have hz' : a * x + b * y < 1 := by
    have := (convex_Iio (1 : ℝ)) hx hy ha hb hab
    simpa [smul_eq_mul] using this
  have hE : ∀ t : ℝ, t < 1 → 0 < lrRho β + δ - δ * t := fun t ht => by nlinarith
  have hEx := hE x hx'
  have hEy := hE y hy'
  have hEz := hE _ hz'
  have hgap := fig156_gap (ρ := lrRho β) (δ := δ) hab hEx.ne' hEy.ne' hEz.ne'
  have hnn : 0 ≤ (lrRho β + δ) * a * b * δ * (x - y) ^ 2 /
      ((lrRho β + δ - δ * x) * (lrRho β + δ - δ * y) * (lrRho β + δ - δ * (a * x + b * y))) := by
    have : 0 ≤ lrRho β + δ := by linarith
    positivity
  simp only [smul_eq_mul]
  rw [fig156_tauL_f, fig156_tauL_f, fig156_tauL_f]
  have h1 : 0 < 1 - α := by linarith
  rw [← sub_nonneg]
  have e : (g - lrRho β * α * ((a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y)))) / (1 - α) -
      (a * ((g - lrRho β * α * (x / (lrRho β + δ - δ * x))) / (1 - α)) +
        b * ((g - lrRho β * α * (y / (lrRho β + δ - δ * y))) / (1 - α))) =
      lrRho β * α / (1 - α) * (a * (x / (lrRho β + δ - δ * x)) + b * (y / (lrRho β + δ - δ * y))
        - (a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y))) := by
    obtain rfl : b = 1 - a := by linarith
    field_simp
    ring
  rw [e, hgap]
  positivity

/-- AKMM, p. 450, Figure 15.6, Panel A: for `δ > 0`, `τ_ℓ` is strictly concave in `τ_k` on
`τ_k < 1`, as the panel shows. -/
theorem fig156_tauL_strictConcaveOn {α β δ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 < δ) : StrictConcaveOn ℝ (Iio 1) (incTauL α β δ g) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  refine ⟨convex_Iio 1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hx' : x < 1 := hx
  have hy' : y < 1 := hy
  have hz' : a * x + b * y < 1 := by
    have := (convex_Iio (1 : ℝ)) hx hy ha.le hb.le hab
    simpa [smul_eq_mul] using this
  have hE : ∀ t : ℝ, t < 1 → 0 < lrRho β + δ - δ * t := fun t ht => by nlinarith
  have hEx := hE x hx'
  have hEy := hE y hy'
  have hEz := hE _ hz'
  have hgap := fig156_gap (ρ := lrRho β) (δ := δ) hab hEx.ne' hEy.ne' hEz.ne'
  have hxy2 : 0 < (x - y) ^ 2 := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  have hpos : 0 < (lrRho β + δ) * a * b * δ * (x - y) ^ 2 /
      ((lrRho β + δ - δ * x) * (lrRho β + δ - δ * y) * (lrRho β + δ - δ * (a * x + b * y))) := by
    have : 0 < lrRho β + δ := by linarith
    positivity
  simp only [smul_eq_mul]
  rw [fig156_tauL_f, fig156_tauL_f, fig156_tauL_f]
  have h1 : 0 < 1 - α := by linarith
  rw [← sub_pos]
  have e : (g - lrRho β * α * ((a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y)))) / (1 - α) -
      (a * ((g - lrRho β * α * (x / (lrRho β + δ - δ * x))) / (1 - α)) +
        b * ((g - lrRho β * α * (y / (lrRho β + δ - δ * y))) / (1 - α))) =
      lrRho β * α / (1 - α) * (a * (x / (lrRho β + δ - δ * x)) + b * (y / (lrRho β + δ - δ * y))
        - (a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y))) := by
    obtain rfl : b = 1 - a := by linarith
    field_simp
    ring
  rw [e, hgap]
  positivity

/-- AKMM, p. 450, Figure 15.6, Panel A: the endpoints, `τ_ℓ = g/(1 − α)` at `τ_k = 0` and
`τ_ℓ = (g − α)/(1 − α)` at `τ_k = 1` (negative iff `g < α`, as in the panel). -/
theorem fig156_tauL_endpoints {α β δ g : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    incTauL α β δ g 0 = g / (1 - α) ∧ incTauL α β δ g 1 = (g - α) / (1 - α) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  unfold incTauL incBud
  constructor
  · simp
  · congr 1
    rw [show lrRho β + (1 - 1) * δ = lrRho β by ring]
    field_simp

/-- AKMM, p. 450, Figure 15.6, Panel A: for `0 < g < α`, the labour tax turns into a subsidy
exactly beyond `τ̂ = g(ρ + δ)/(ρα + gδ) ∈ (0, 1)`: on `τ_k < 1`, `τ_ℓ < 0 ↔ τ_k > τ̂` and
`τ_ℓ = 0 ↔ τ_k = τ̂`. -/
theorem fig156_tauL_neg_iff {α β δ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hg0 : 0 < g) (hgα : g < α) (hτk : τk < 1) :
    0 < g * (lrRho β + δ) / (lrRho β * α + g * δ) ∧
      g * (lrRho β + δ) / (lrRho β * α + g * δ) < 1 ∧
      (incTauL α β δ g τk < 0 ↔ g * (lrRho β + δ) / (lrRho β * α + g * δ) < τk) ∧
      (incTauL α β δ g τk = 0 ↔ τk = g * (lrRho β + δ) / (lrRho β * α + g * δ)) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hD : 0 < lrRho β * α + g * δ := by positivity
  have hE : 0 < lrRho β + δ - δ * τk := by nlinarith
  have h1 : 0 < 1 - α := by linarith
  rw [fig156_tauL_f]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_one hD]
    nlinarith
  · rw [div_neg_iff, div_lt_iff₀ hD]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · rw [sub_neg, mul_div_assoc', lt_div_iff₀ hE] at h
        nlinarith
    · intro h
      refine Or.inr ⟨?_, h1⟩
      rw [sub_neg, mul_div_assoc', lt_div_iff₀ hE]
      nlinarith
  · rw [div_eq_zero_iff, sub_eq_zero, mul_div_assoc', eq_div_iff hE.ne']
    constructor
    · rintro (h | h)
      · rw [eq_div_iff hD.ne']
        linarith
      · linarith
    · intro h
      left
      rw [eq_div_iff hD.ne'] at h
      linarith

/-! ### The one-variable hump -/

/-- `h(s) = (K − cs)^a s^b`, the common form of `c_w` and `c_k` as functions of `s`. -/
noncomputable def fig156Hump (K c a b s : ℝ) : ℝ := (K - c * s) ^ a * s ^ b

/-- The derivative of `h(s) = (K − cs)^a s^b` at `s > 0` with `K − cs > 0`:
`h(s)(b/s − ac/(K − cs))`. -/
theorem fig156_hump_hasDerivAt {K c a b s : ℝ} (hs : 0 < s) (hm : 0 < K - c * s) :
    HasDerivAt (fig156Hump K c a b)
      ((K - c * s) ^ a * s ^ b * (b / s - a * c / (K - c * s))) s := by
  have h1 : HasDerivAt (fun x => K - c * x) (-c) s := by
    simpa using ((hasDerivAt_id s).const_mul c).const_sub K
  have h2 := (h1.rpow_const (p := a) (Or.inl hm.ne')).mul
    (Real.hasDerivAt_rpow_const (p := b) (Or.inl hs.ne'))
  refine h2.congr_deriv ?_
  rw [Real.rpow_sub_one hm.ne', Real.rpow_sub_one hs.ne']
  field_simp
  ring

/-- `h(s) = (K − cs)^a s^b` (`a, b, c > 0`) is strictly increasing on `(0, bK/((a + b)c)]`. -/
theorem fig156_hump_strictMonoOn {K c a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hK : 0 < K) : StrictMonoOn (fig156Hump K c a b) (Ioc 0 (b * K / ((a + b) * c))) := by
  have hab : 0 < (a + b) * c := by positivity
  have hm : ∀ x ∈ Ioc 0 (b * K / ((a + b) * c)), 0 < K - c * x := by
    intro x hx
    have h := (le_div_iff₀ hab).mp hx.2
    nlinarith [hx.1]
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro x hx
    exact (fig156_hump_hasDerivAt hx.1 (hm x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hmx := hm x (Ioo_subset_Ioc_self hx)
    rw [(fig156_hump_hasDerivAt hx.1 hmx).deriv]
    have hlt := (lt_div_iff₀ hab).mp hx.2
    have hx0 := hx.1
    apply mul_pos (mul_pos (Real.rpow_pos_of_pos hmx _) (Real.rpow_pos_of_pos hx0 _))
    rw [div_sub_div _ _ hx0.ne' hmx.ne']
    apply div_pos _ (mul_pos hx0 hmx)
    nlinarith

/-- `h(s) = (K − cs)^a s^b` (`a, b, c > 0`) is strictly decreasing on `[bK/((a + b)c), K/c)`. -/
theorem fig156_hump_strictAntiOn {K c a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hK : 0 < K) : StrictAntiOn (fig156Hump K c a b) (Ico (b * K / ((a + b) * c)) (K / c)) := by
  have hab : 0 < (a + b) * c := by positivity
  have hpos : ∀ x ∈ Ico (b * K / ((a + b) * c)) (K / c), 0 < x ∧ 0 < K - c * x := by
    intro x hx
    have h0 : 0 < b * K / ((a + b) * c) := by positivity
    refine ⟨by linarith [hx.1], ?_⟩
    have := (lt_div_iff₀ hc).mp hx.2
    linarith
  apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
  · intro x hx
    have h := hpos x hx
    exact (fig156_hump_hasDerivAt h.1 h.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have h := hpos x (Ioo_subset_Ico_self hx)
    rw [(fig156_hump_hasDerivAt h.1 h.2).deriv]
    have hlt := (div_lt_iff₀ hab).mp hx.1
    apply mul_neg_of_pos_of_neg
      (mul_pos (Real.rpow_pos_of_pos h.2 _) (Real.rpow_pos_of_pos h.1 _))
    rw [div_sub_div _ _ h.1.ne' h.2.ne']
    apply div_neg_of_neg_of_pos _ (mul_pos h.1 h.2)
    nlinarith

/-! ### `s` along the capital tax -/

/-- `s(0) = s₀ = α/(ρ + δ)`. -/
theorem fig156_s0 {α β δ : ℝ} : lrS α β δ 0 = α / (lrRho β + δ) := by
  unfold lrS
  simp

/-- `s(τ_k) = Ks₀` at `τ_k = (1 − K)(ρ + δ)/(ρ + δ(1 − K))`, which lies in `(0, 1)` when
`0 < K < 1` (and `(-∞, 1)` for `0 < K`). -/
theorem fig156_s_eq {α β δ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hK0 : 0 < K)
    (hK1 : K < 1) :
    lrS α β δ ((1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K))) = K * lrS α β δ 0 ∧
      0 < (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) ∧
      (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) < 1 := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hD : 0 < lrRho β + δ * (1 - K) := by
    have : 0 ≤ δ * (1 - K) := mul_nonneg hδ (by linarith)
    linarith
  have hc : 0 < lrRho β + δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [fig156_s0]
    unfold lrS
    have e : 1 - (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) =
        lrRho β * K / (lrRho β + δ * (1 - K)) := by
      rw [eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
      ring
    rw [e]
    field_simp
    ring
  · have : 0 < 1 - K := by linarith
    positivity
  · rw [div_lt_one hD]
    nlinarith

/-- `0 < s(τ_k) ≤ s₀` for `0 ≤ τ_k < 1`, strictly below for `τ_k > 0`. -/
theorem fig156_s_bounds {α β δ τk : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hτ0 : 0 ≤ τk) (hτ1 : τk < 1) : 0 < lrS α β δ τk ∧ lrS α β δ τk ≤ lrS α β δ 0 := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  refine ⟨?_, ?_⟩
  · have : 0 < 1 - τk := by linarith
    unfold lrS
    positivity
  · exact (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ).antitoneOn (Set.mem_Iio.mpr one_pos)
      (Set.mem_Iio.mpr hτ1) hτ0

/-- Transfer of a hump in `s` to a hump in `τ_k`: if `h` is strictly increasing on `(0, ŝ]` and
strictly decreasing on `[ŝ, U)`, with `s₀ < U` and `s(τ̂) = ŝ`, `0 ≤ τ̂ < 1`, then `h ∘ s` is
strictly increasing on `[0, τ̂]` and strictly decreasing on `[τ̂, 1)`. -/
theorem fig156_comp_hump {α β δ U τh : ℝ} {h : ℝ → ℝ} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hU : lrS α β δ 0 < U) (hτh0 : 0 ≤ τh) (hτh1 : τh < 1)
    (hinc : StrictMonoOn h (Ioc 0 (lrS α β δ τh)))
    (hdec : StrictAntiOn h (Ico (lrS α β δ τh) U)) :
    StrictMonoOn (fun τ => h (lrS α β δ τ)) (Icc 0 τh) ∧
      StrictAntiOn (fun τ => h (lrS α β δ τ)) (Ico τh 1) := by
  have hanti := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ
  constructor
  · intro x hx y hy hxy
    have hx1 : x < 1 := by linarith [hx.2]
    have hy1 : y < 1 := by linarith [hy.2]
    have hsx := fig156_s_bounds hα0 hβ0 hβ1 hδ hx.1 hx1
    have hsy := fig156_s_bounds hα0 hβ0 hβ1 hδ hy.1 hy1
    have hlt : lrS α β δ y < lrS α β δ x := hanti hx1 hy1 hxy
    have hyh : lrS α β δ τh ≤ lrS α β δ y :=
      hanti.antitoneOn (Set.mem_Iio.mpr hy1) (Set.mem_Iio.mpr hτh1) hy.2
    exact hdec ⟨hyh, by linarith⟩ ⟨by linarith, by linarith⟩ hlt
  · intro x hx y hy hxy
    have hx1 : x < 1 := hx.2
    have hy1 : y < 1 := hy.2
    have hsy := fig156_s_bounds hα0 hβ0 hβ1 hδ (by linarith [hy.1]) hy1
    have hlt : lrS α β δ y < lrS α β δ x := hanti hx1 hy1 hxy
    have hxh : lrS α β δ x ≤ lrS α β δ τh :=
      hanti.antitoneOn (Set.mem_Iio.mpr hτh1) (Set.mem_Iio.mpr hx1) hx.1
    exact hinc ⟨hsy.1, by linarith⟩ ⟨by linarith, hxh⟩ hlt

/-! ### Panel B: workers' consumption -/

/-- Workers' consumption along (15.14), `c_w = my` (AKMM, p. 449, `τ_c = 0`). -/
noncomputable def fig156Cw (α β δ φ g τk : ℝ) : ℝ :=
  incM α β δ g τk * incOutput α φ (incM α β δ g τk) (lrS α β δ τk)

/-- Capitalists' consumption along (15.14), `c_k = ρsy` (AKMM, p. 449, `τ_c = 0`). -/
noncomputable def fig156Ck (α β δ φ g τk : ℝ) : ℝ :=
  lrRho β * lrS α β δ τk * incOutput α φ (incM α β δ g τk) (lrS α β δ τk)

/-- `c_w = h(s)` with `K = 1 − g`, `c = ρ + δ`, `a = 1 + φ`, `b = e`, for `0 ≤ τ_k < 1` and
`g < 1 − α`. -/
theorem fig156_cw_eq {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hg : g < 1 - α) (hτ0 : 0 ≤ τk) (hτ1 : τk < 1) :
    fig156Cw α β δ φ g τk =
      fig156Hump (1 - g) (lrRho β + δ) (1 + φ) (α * (1 + φ) / (1 - α)) (lrS α β δ τk) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs := fig156_s_bounds hα0 hβ0 hβ1 hδ hτ0 hτ1
  have hm := inc_m_eq (g := g) hα1 hβ0 hβ1 hδ hτ1
  have hmpos : 0 < 1 - g - (lrRho β + δ) * lrS α β δ τk := by
    rw [fig156_s0] at hs
    have := (le_div_iff₀ (show 0 < lrRho β + δ by linarith)).mp hs.2
    nlinarith
  unfold fig156Cw fig156Hump incOutput
  rw [hm, ← mul_assoc, Real.rpow_add hmpos, Real.rpow_one]

/-- `c_k = ρh(s)` with `K = 1 − g`, `c = ρ + δ`, `a = φ`, `b = 1 + e`, for `0 ≤ τ_k < 1` and
`g < 1 − α`. -/
theorem fig156_ck_eq {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hτ0 : 0 ≤ τk) (hτ1 : τk < 1) :
    fig156Ck α β δ φ g τk = lrRho β *
      fig156Hump (1 - g) (lrRho β + δ) φ (1 + α * (1 + φ) / (1 - α)) (lrS α β δ τk) := by
  have hs := fig156_s_bounds hα0 hβ0 hβ1 hδ hτ0 hτ1
  have hm := inc_m_eq (g := g) hα1 hβ0 hβ1 hδ hτ1
  unfold fig156Ck fig156Hump incOutput
  rw [hm, Real.rpow_add hs.1, Real.rpow_one]
  ring

/-- **Figure 15.6, Panel B** (AKMM, p. 450: "consumption of workers is a hump-shaped function of
`τ_k`"). For `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` and `0 < g < 1 − α` (`τ_ℓ(0) < 1`),
`τ_w = g(ρ + δ)/(ρ + δg)` lies in `(0, 1)`, and `c_w` is strictly increasing on `[0, τ_w]` and
strictly decreasing on `[τ_w, 1)`. -/
theorem fig156_cw_hump {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg0 : 0 < g) (hg : g < 1 - α) :
    0 < g * (lrRho β + δ) / (lrRho β + δ * g) ∧ g * (lrRho β + δ) / (lrRho β + δ * g) < 1 ∧
      StrictMonoOn (fig156Cw α β δ φ g) (Icc 0 (g * (lrRho β + δ) / (lrRho β + δ * g))) ∧
      StrictAntiOn (fig156Cw α β δ φ g) (Ico (g * (lrRho β + δ) / (lrRho β + δ * g)) 1) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨hsτ, hτ0, hτ1⟩ := fig156_s_eq (α := α) hβ0 hβ1 hδ (K := 1 - g) (by linarith)
    (by linarith)
  have eτ : (1 - (1 - g)) * (lrRho β + δ) / (lrRho β + δ * (1 - (1 - g))) =
      g * (lrRho β + δ) / (lrRho β + δ * g) := by ring_nf
  rw [eτ] at hsτ hτ0 hτ1
  set τw := g * (lrRho β + δ) / (lrRho β + δ * g)
  have hb : 0 < α * (1 + φ) / (1 - α) := by positivity
  -- the peak of `h` in `s`
  have hpeak : α * (1 + φ) / (1 - α) * (1 - g) / ((1 + φ + α * (1 + φ) / (1 - α)) *
      (lrRho β + δ)) = lrS α β δ τw := by
    rw [hsτ, fig156_s0]
    field_simp
    ring
  have hU : lrS α β δ 0 < (1 - g) / (lrRho β + δ) := by
    rw [fig156_s0]
    exact div_lt_div_of_pos_right (by linarith) hc
  have hinc := fig156_hump_strictMonoOn (by linarith : (0 : ℝ) < 1 + φ) hb hc
    (by linarith : (0 : ℝ) < 1 - g)
  have hdec := fig156_hump_strictAntiOn (by linarith : (0 : ℝ) < 1 + φ) hb hc
    (by linarith : (0 : ℝ) < 1 - g)
  rw [hpeak] at hinc hdec
  obtain ⟨hA, hB⟩ := fig156_comp_hump hα0 hβ0 hβ1 hδ hU hτ0.le hτ1 hinc hdec
  refine ⟨hτ0, hτ1, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg hx.1 (by linarith [hx.2]),
      fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg hy.1 (by linarith [hy.2])]
    exact hA hx hy hxy
  · intro x hx y hy hxy
    rw [fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg (by linarith [hx.1]) hx.2,
      fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg (by linarith [hy.1]) hy.2]
    exact hB hx hy hxy

/-- **Figure 15.6, Panel B**, the peak: under the hypotheses of `fig156_cw_hump`, `c_w` attains
its strict maximum over `[0, 1)` at `τ_w = g(ρ + δ)/(ρ + δg)`. -/
theorem fig156_cw_isMaxOn {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg0 : 0 < g) (hg : g < 1 - α) (hτ0 : 0 ≤ τk)
    (hτ1 : τk < 1) (hne : τk ≠ g * (lrRho β + δ) / (lrRho β + δ * g)) :
    fig156Cw α β δ φ g τk < fig156Cw α β δ φ g (g * (lrRho β + δ) / (lrRho β + δ * g)) := by
  obtain ⟨h0, h1, hA, hB⟩ := fig156_cw_hump hα0 hα1 hβ0 hβ1 hδ hφ hg0 hg
  rcases lt_or_gt_of_ne hne with h | h
  · exact hA ⟨hτ0, h.le⟩ ⟨h0.le, le_rfl⟩ h
  · exact hB ⟨le_rfl, h1⟩ ⟨h.le, hτ1⟩ h

/-- **Figure 15.6, Panel B**, where the peak is: at `τ_w = g(ρ + δ)/(ρ + δg)` the budget-balancing
labour tax (15.14) equals `g`, so the capital-tax revenue `τ_k(r − δ)k = gy − g(1 − α)y = gαy`:
labour income and capital income are taxed at the same average rate `g`. -/
theorem fig156_cw_peak_tauL {α β δ g : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hg0 : 0 < g) (hg1 : g < 1) :
    incTauL α β δ g (g * (lrRho β + δ) / (lrRho β + δ * g)) = g ∧
      incBud α β δ (g * (lrRho β + δ) / (lrRho β + δ * g)) = g * α := by
  obtain ⟨hsτ, _, hτ1⟩ := fig156_s_eq (α := α) hβ0 hβ1 hδ (K := 1 - g) (by linarith)
    (by linarith)
  have eτ : (1 - (1 - g)) * (lrRho β + δ) / (lrRho β + δ * (1 - (1 - g))) =
      g * (lrRho β + δ) / (lrRho β + δ * g) := by ring_nf
  rw [eτ] at hsτ hτ1
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : (1 - α) ≠ 0 := by linarith
  have hT : incTauL α β δ g (g * (lrRho β + δ) / (lrRho β + δ * g)) = g := by
    rw [fig156_tauL_eq hα1 hβ0 hβ1 hδ hτ1, hsτ, fig156_s0]
    field_simp
    ring
  refine ⟨hT, ?_⟩
  unfold incTauL at hT
  rw [div_eq_iff h1α] at hT
  linarith

/-! ### Panel C: capitalists' consumption -/

/-- **Figure 15.6, Panel C**, the book's claim under its exact condition (AKMM, p. 450: "When
`τ_k` is restricted to be non-negative, steady-state consumption of capitalists is maximized at
`τ_k = 0`"). For `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` and `g ≤ (1 − α)/(1 + αφ)`, `c_k`
is strictly decreasing on `[0, 1)`. -/
theorem fig156_ck_strictAntiOn {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg : g ≤ (1 - α) / (1 + α * φ)) :
    StrictAntiOn (fig156Ck α β δ φ g) (Ico 0 1) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαφ : 0 < 1 + α * φ := by positivity
  have hg' : g * (1 + α * φ) ≤ 1 - α := (le_div_iff₀ hαφ).mp hg
  have hgl : g < 1 - α := by nlinarith [mul_pos hα0 hφ]
  have hb : 0 < 1 + α * (1 + φ) / (1 - α) := by positivity
  have hinc := fig156_hump_strictMonoOn hφ hb hc (by linarith : (0 : ℝ) < 1 - g)
  have hpk : lrS α β δ 0 ≤ (1 + α * (1 + φ) / (1 - α)) * (1 - g) /
      ((φ + (1 + α * (1 + φ) / (1 - α))) * (lrRho β + δ)) := by
    rw [fig156_s0]
    have e : (1 + α * (1 + φ) / (1 - α)) * (1 - g) /
        ((φ + (1 + α * (1 + φ) / (1 - α))) * (lrRho β + δ)) =
        (1 + α * φ) * (1 - g) / ((1 + φ) * (lrRho β + δ)) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hc (by positivity)]
    nlinarith
  intro x hx y hy hxy
  rw [fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hx.1 hx.2, fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hy.1 hy.2]
  have hsx := fig156_s_bounds hα0 hβ0 hβ1 hδ hx.1 hx.2
  have hsy := fig156_s_bounds hα0 hβ0 hβ1 hδ hy.1 hy.2
  have hlt := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ hx.2 hy.2 hxy
  exact mul_lt_mul_of_pos_left (hinc ⟨hsy.1, by linarith⟩ ⟨hsx.1, by linarith⟩ hlt) hρ

/-- **Figure 15.6, Panel C, the other case** (correcting AKMM, p. 450). For
`(1 − α)/(1 + αφ) < g < 1 − α`, put `K = (1 + αφ)(1 − g)/((1 + φ)α) ∈ (0, 1)` and
`τ_c = (1 − K)(ρ + δ)/(ρ + δ(1 − K)) ∈ (0, 1)`: `c_k` is strictly increasing on `[0, τ_c]` and
strictly decreasing on `[τ_c, 1)`, so it is maximal at `τ_c > 0`, not at `0`. -/
theorem fig156_ck_hump {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg0 : (1 - α) / (1 + α * φ) < g)
    (hg : g < 1 - α) :
    let K := (1 + α * φ) * (1 - g) / ((1 + φ) * α)
    0 < K ∧ K < 1 ∧
      0 < (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) ∧
      (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) < 1 ∧
      StrictMonoOn (fig156Ck α β δ φ g)
        (Icc 0 ((1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)))) ∧
      StrictAntiOn (fig156Ck α β δ φ g)
        (Ico ((1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K))) 1) := by
  intro K
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαφ : 0 < 1 + α * φ := by positivity
  have hg' : 1 - α < g * (1 + α * φ) := (div_lt_iff₀ hαφ).mp hg0
  have hK0 : 0 < K := by
    have : 0 < 1 - g := by linarith
    positivity
  have hK1 : K < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hsτ, hτ0, hτ1⟩ := fig156_s_eq (α := α) hβ0 hβ1 hδ hK0 hK1
  set τc := (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K))
  have hb : 0 < 1 + α * (1 + φ) / (1 - α) := by positivity
  have hpeak : (1 + α * (1 + φ) / (1 - α)) * (1 - g) /
      ((φ + (1 + α * (1 + φ) / (1 - α))) * (lrRho β + δ)) = lrS α β δ τc := by
    rw [hsτ, fig156_s0]
    simp only [K]
    field_simp
    ring
  have hU : lrS α β δ 0 < (1 - g) / (lrRho β + δ) := by
    rw [fig156_s0]
    exact div_lt_div_of_pos_right (by linarith) hc
  have hinc := fig156_hump_strictMonoOn hφ hb hc (by linarith : (0 : ℝ) < 1 - g)
  have hdec := fig156_hump_strictAntiOn hφ hb hc (by linarith : (0 : ℝ) < 1 - g)
  rw [hpeak] at hinc hdec
  obtain ⟨hA, hB⟩ := fig156_comp_hump hα0 hβ0 hβ1 hδ hU hτ0.le hτ1 hinc hdec
  refine ⟨hK0, hK1, hτ0, hτ1, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hx.1 (by linarith [hx.2]),
      fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hy.1 (by linarith [hy.2])]
    exact mul_lt_mul_of_pos_left (hA hx hy hxy) hρ
  · intro x hx y hy hxy
    rw [fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ (by linarith [hx.1]) hx.2,
      fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ (by linarith [hy.1]) hy.2]
    exact mul_lt_mul_of_pos_left (hB hx hy hxy) hρ

/-- **Figure 15.6, Panel C, the exact statement** (correcting AKMM, p. 450). For `0 < α < 1`,
`0 < β < 1`, `δ ≥ 0`, `φ > 0` and `g < 1 − α` (so that `τ_ℓ(0) < 1`), capitalists' consumption
on `0 ≤ τ_k < 1` is maximal at `τ_k = 0` if and only if `g ≤ (1 − α)/(1 + αφ)`, i.e.
`τ_ℓ(0) = g/(1 − α) ≤ 1/(1 + αφ)`. -/
theorem fig156_ck_max_at_zero_iff {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg : g < 1 - α) :
    (∀ τk ∈ Ico (0 : ℝ) 1, fig156Ck α β δ φ g τk ≤ fig156Ck α β δ φ g 0) ↔
      g ≤ (1 - α) / (1 + α * φ) := by
  constructor
  · intro h
    by_contra hc
    replace hc := not_le.mp hc
    obtain ⟨_, _, hτ0, hτ1, hA, _⟩ := fig156_ck_hump hα0 hα1 hβ0 hβ1 hδ hφ hc hg
    have := hA ⟨le_rfl, hτ0.le⟩ ⟨hτ0.le, le_rfl⟩ hτ0
    linarith [h _ ⟨hτ0.le, hτ1⟩]
  · intro hg' τk hτ
    exact (fig156_ck_strictAntiOn hα0 hα1 hβ0 hβ1 hδ hφ hg').antitoneOn ⟨le_rfl, one_pos⟩ hτ
      hτ.1

/-- **Counterexample to "consumption of capitalists is maximized at `τ_k = 0`"** (AKMM, p. 450),
at the parameters of `inc_excess_cost_not_min_at_zero`: `α = 1/2`, `β = 2/3` (`ρ = 1/2`),
`δ = 1/10`, `φ = 1`, `g = 2/5` (> `(1 − α)/(1 + αφ) = 1/3`, `τ_ℓ < 1`). Then `c_k = 25/864` at
`τ_k = 0` and `21600/707281 > 25/864` at `τ_k = 1/5`. -/
theorem fig156_ck_not_max_at_zero :
    fig156Ck (1 / 2) (2 / 3) (1 / 10) 1 (2 / 5) 0 = 25 / 864 ∧
      fig156Ck (1 / 2) (2 / 3) (1 / 10) 1 (2 / 5) (1 / 5) = 21600 / 707281 ∧
      (25 / 864 : ℝ) < 21600 / 707281 := by
  have e : ((1 : ℝ) / 2) * (1 + 1) / (1 - 1 / 2) = 2 := by norm_num
  refine ⟨?_, ?_, by norm_num⟩ <;>
    simp only [fig156Ck, incOutput, incM, incTauL, incBud, lrS, lrRho, e, Real.rpow_one,
      Real.rpow_two] <;> norm_num

end AKMM.FiscalPolicy
