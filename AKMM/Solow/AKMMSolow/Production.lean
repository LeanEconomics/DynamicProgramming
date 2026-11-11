/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Solow1956.Growth.GeneralSolowExamples

/-!
# The aggregate production function of the Solow model

AKMM, §3.1, pp. 71–73. The book's Assumptions 1–6 on `F(K, L)` (strictly increasing, strictly
quasiconcave, constant returns, `F(0, L) = 0`, the Inada conditions) and footnote 1 (smoothness)
are the structure `SolowAssumptions`. From them we derive the properties of the intensive form
`f(k) = F(k, 1)` that the chapter uses (p. 73: "strictly increasing and strictly concave"):
`f(0) = 0`, `f` strictly increasing, `f` **strictly concave** (from strict quasiconcavity and
constant returns, `solow_intensive_strictConcave`), `f' > 0`, and the Inada limits. Together they
are EconomicGrowth's `Solow1956.Neoclassical.Technology f` (`solow_technology`), so all the
dynamics of that library apply to the book's model. Constant returns gives the intensive form
`F(K, E) = E f(K/E)` (`solow_intensive_form`).

The Cobb–Douglas function `K^α L^{1−α}` satisfies every assumption (p. 73,
`solow_cobbDouglas_assumptions`), which is also the concrete instance of the structure.

**Departures.** (i) Assumption 1 asks `F` to be strictly increasing in `L` everywhere, which
contradicts Assumption 4 at `K = 0` (`solow_assumption1_conflicts_assumption4`); we ask for
monotonicity in `L` at `K > 0` only. (ii) On p. 74 diminishing returns are attributed to
"Assumption 2" alone; strict quasiconcavity alone does not give them: `F = K²L²` is strictly
increasing and strictly quasiconcave with `F(0, L) = 0`, but `f(k) = k²` is not concave
(`solow_assumption2_alone_counterexample`). Constant returns (Assumption 3) is needed as well.
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical

/-- AKMM, Assumption 2, p. 72: strict quasiconcavity of `F` on the positive orthant, i.e. every
interior point of a segment between two distinct input bundles produces strictly more than the
less productive endpoint (strictly convex isoquants). -/
def StrictQuasiconcavePos (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ K₁ L₁ K₂ L₂ θ : ℝ, 0 < K₁ → 0 < L₁ → 0 < K₂ → 0 < L₂ → (K₁ ≠ K₂ ∨ L₁ ≠ L₂) →
    0 < θ → θ < 1 →
      min (F K₁ L₁) (F K₂ L₂) < F (θ * K₁ + (1 - θ) * K₂) (θ * L₁ + (1 - θ) * L₂)

/-- AKMM, Assumptions 1–6 and footnote 1, p. 72: the aggregate production function `F(K, L)`.
Monotonicity in `L` is asked at `K > 0` (see the module docstring); smoothness is asked of
`K ↦ F(K, L)`, as the book uses it. -/
structure SolowAssumptions (F : ℝ → ℝ → ℝ) : Prop where
  mono_capital : ∀ L, 0 < L → StrictMonoOn (fun K => F K L) (Set.Ici 0)
  mono_labour : ∀ K, 0 < K → StrictMonoOn (F K) (Set.Ioi 0)
  quasiconcave : StrictQuasiconcavePos F
  crs : ∀ c K L, 0 < c → 0 ≤ K → 0 < L → F (c * K) (c * L) = c * F K L
  zero_capital : ∀ L, 0 < L → F 0 L = 0
  continuous : ∀ L, 0 < L → ContinuousOn (fun K => F K L) (Set.Ici 0)
  differentiable : ∀ L K, 0 < L → 0 < K → DifferentiableAt ℝ (fun K => F K L) K
  derivative_continuous : ∀ L, 0 < L → ContinuousOn (deriv (fun K => F K L)) (Set.Ioi 0)
  inada_zero : ∀ L, 0 < L → Tendsto (deriv (fun K => F K L)) (𝓝[>] 0) atTop
  inada_top : ∀ L, 0 < L → Tendsto (deriv (fun K => F K L)) atTop (𝓝 0)

/-- AKMM, (3.1), p. 72: the intensive form `f(k) = F(k, 1)`. -/
def intensive (F : ℝ → ℝ → ℝ) : ℝ → ℝ := fun k => F k 1

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, p. 79 (and p. 72): constant returns gives `F(K, E) = E f(K/E)` for `E > 0`. -/
theorem solow_intensive_form (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 < E) :
    F K E = E * intensive F (K / E) := by
  have h := hF.crs E (K / E) 1 hE (div_nonneg hK hE.le) one_pos
  rw [mul_div_cancel₀ K (ne_of_gt hE), mul_one] at h
  exact h

/-- AKMM, (3.1), p. 72: `f(0) = 0` (Assumption 4). -/
theorem solow_intensive_zero (hF : SolowAssumptions F) : intensive F 0 = 0 :=
  hF.zero_capital 1 one_pos

/-- AKMM, p. 73: `f` is strictly increasing (Assumption 1). -/
theorem solow_intensive_strictMono (hF : SolowAssumptions F) :
    StrictMonoOn (intensive F) (Set.Ici 0) :=
  hF.mono_capital 1 one_pos

/-- AKMM, p. 73: output is positive at positive capital. -/
theorem solow_intensive_pos (hF : SolowAssumptions F) {k : ℝ} (hk : 0 < k) :
    0 < intensive F k := by
  have h := solow_intensive_strictMono hF (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hk.le) hk
  rw [solow_intensive_zero hF] at h
  exact h

/-- AKMM, p. 73 ("the right-hand side is strictly increasing and strictly concave"): strict
quasiconcavity (Assumption 2) and constant returns (Assumption 3), with Assumptions 1 and 4, make
`f = F(·, 1)` strictly concave on `[0, ∞)`. For `x, y > 0` the bundles `(x, 1)/f(x)` and
`(y, 1)/f(y)` lie on the unit isoquant; strict quasiconcavity at the right convex combination
and constant returns give `f(ax + by) > a f(x) + b f(y)`. An endpoint at zero uses strict
monotonicity in labour. -/
theorem solow_intensive_strictConcave (hF : SolowAssumptions F) :
    StrictConcaveOn ℝ (Set.Ici 0) (intensive F) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [smul_eq_mul]
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hf0 := solow_intensive_zero hF
  -- an endpoint at zero
  have hend : ∀ z c : ℝ, 0 < z → 0 < c → c < 1 → c * intensive F z < intensive F (c * z) := by
    intro z c hz hc hc1
    have h1 := hF.crs c z 1 hc hz.le one_pos
    rw [mul_one] at h1
    have h2 := hF.mono_labour (c * z) (mul_pos hc hz) (Set.mem_Ioi.mpr hc)
      (Set.mem_Ioi.mpr one_pos) hc1
    simp only [intensive]
    rw [← h1]
    exact h2
  rcases hx0.eq_or_lt with hx' | hxpos
  · subst hx'
    have hypos : 0 < y := lt_of_le_of_ne hy0 hxy
    simp only [hf0, mul_zero, zero_add]
    exact hend y b hypos hb (by linarith)
  rcases hy0.eq_or_lt with hy' | hypos
  · subst hy'
    simp only [hf0, mul_zero, add_zero]
    exact hend x a hxpos ha (by linarith)
  -- both endpoints positive
  set y1 := intensive F x with hy1
  set y2 := intensive F y with hy2
  have hy1p : 0 < y1 := solow_intensive_pos hF hxpos
  have hy2p : 0 < y2 := solow_intensive_pos hF hypos
  set Yb := a * y1 + b * y2 with hYb
  have hYbp : 0 < Yb := by positivity
  have hunit : ∀ z w : ℝ, 0 < z → w = intensive F z → F (z / w) (1 / w) = 1 := by
    intro z w hz hw
    have hwp : 0 < w := hw ▸ solow_intensive_pos hF hz
    have h := hF.crs (1 / w) z 1 (by positivity) hz.le one_pos
    rw [show 1 / w * z = z / w by ring, mul_one] at h
    rw [h]
    change 1 / w * intensive F z = 1
    rw [← hw]
    field_simp
  have hθ : 0 < a * y1 / Yb := by positivity
  have hθ1 : a * y1 / Yb < 1 := by
    rw [div_lt_one hYbp]
    have := mul_pos hb hy2p
    linarith
  have hne : x / y1 ≠ y / y2 ∨ 1 / y1 ≠ 1 / y2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hy12 : y1 = y2 := by
      have := h2
      field_simp at this
      linarith
    rw [hy12] at h1
    exact hxy (by field_simp at h1; linarith)
  have key := hF.quasiconcave (x / y1) (1 / y1) (y / y2) (1 / y2) (a * y1 / Yb)
    (by positivity) (by positivity) (by positivity) (by positivity) hne hθ hθ1
  rw [hunit x y1 hxpos rfl, hunit y y2 hypos rfl, min_self] at key
  have e1 : a * y1 / Yb * (x / y1) + (1 - a * y1 / Yb) * (y / y2) = 1 / Yb * (a * x + b * y) := by
    field_simp
    rw [hYb]
    ring
  have e2 : a * y1 / Yb * (1 / y1) + (1 - a * y1 / Yb) * (1 / y2) = 1 / Yb * 1 := by
    field_simp
    rw [hYb]
    linear_combination y2 * hab
  rw [e1, e2, hF.crs (1 / Yb) (a * x + b * y) 1 (by positivity) (by positivity) one_pos] at key
  have := (lt_div_iff₀ hYbp).mp (by rw [one_div_mul_eq_div] at key; exact key)
  simp only [intensive] at this ⊢
  linarith

/-- AKMM, p. 73: the marginal product `f'(k)` is positive at `k > 0` (a strictly concave,
strictly increasing differentiable function has positive slope). -/
theorem solow_intensive_deriv_pos (hF : SolowAssumptions F) {k : ℝ} (hk : 0 < k) :
    0 < deriv (intensive F) k := by
  have hd : DifferentiableAt ℝ (intensive F) k := hF.differentiable 1 k one_pos hk
  have hs := (solow_intensive_strictConcave hF).concaveOn.slope_le_deriv
    (Set.mem_Ici.mpr hk.le) (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ k + 1))
    (by linarith : k < k + 1) hd
  have hm := solow_intensive_strictMono hF (Set.mem_Ici.mpr hk.le)
    (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ k + 1)) (by linarith : k < k + 1)
  rw [slope_def_field, show k + 1 - k = 1 by ring, div_one] at hs
  linarith

/-- AKMM, §3.1, pp. 72–73: Assumptions 1–6 make the intensive form a neoclassical technology in
the sense of EconomicGrowth (`Solow1956.Neoclassical.Technology`): continuous on `[0, ∞)`,
`f(0) = 0`, `C¹` on `(0, ∞)`, strictly concave, `f' > 0`, and the Inada limits. -/
theorem solow_technology (hF : SolowAssumptions F) : Technology (intensive F) where
  continuous := hF.continuous 1 one_pos
  zero := solow_intensive_zero hF
  differentiable := fun k hk => hF.differentiable 1 k one_pos hk
  derivative_continuous := hF.derivative_continuous 1 one_pos
  concave := solow_intensive_strictConcave hF
  marginal_positive := fun _ hk => solow_intensive_deriv_pos hF hk
  inada_zero := hF.inada_zero 1 one_pos
  inada_top := hF.inada_top 1 one_pos

/-- A product of powers `K^a L^b` with `a, b > 0` is strictly quasiconcave on the positive
orthant: its logarithm `a log K + b log L` is strictly concave there. -/
theorem solow_rpow_strictQuasiconcave {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictQuasiconcavePos (fun K L => K ^ a * L ^ b) := by
  intro K₁ L₁ K₂ L₂ θ hK₁ hL₁ hK₂ hL₂ hne hθ hθ1
  have hθ' : 0 < 1 - θ := by linarith
  have hsum : θ + (1 - θ) = 1 := by ring
  have hM : 0 < θ * K₁ + (1 - θ) * K₂ := by positivity
  have hN : 0 < θ * L₁ + (1 - θ) * L₂ := by positivity
  have hexp : ∀ K L : ℝ, 0 < K → 0 < L →
      K ^ a * L ^ b = Real.exp (Real.log K * a + Real.log L * b) := by
    intro K L hK hL
    rw [Real.rpow_def_of_pos hK, Real.rpow_def_of_pos hL, ← Real.exp_add]
  have hlog := strictConcaveOn_log_Ioi
  have cK : θ * Real.log K₁ + (1 - θ) * Real.log K₂ ≤ Real.log (θ * K₁ + (1 - θ) * K₂) := by
    have := hlog.concaveOn.2 (Set.mem_Ioi.mpr hK₁) (Set.mem_Ioi.mpr hK₂) hθ.le hθ'.le hsum
    simpa only [smul_eq_mul] using this
  have cL : θ * Real.log L₁ + (1 - θ) * Real.log L₂ ≤ Real.log (θ * L₁ + (1 - θ) * L₂) := by
    have := hlog.concaveOn.2 (Set.mem_Ioi.mpr hL₁) (Set.mem_Ioi.mpr hL₂) hθ.le hθ'.le hsum
    simpa only [smul_eq_mul] using this
  set u1 := Real.log K₁ * a + Real.log L₁ * b
  set u2 := Real.log K₂ * a + Real.log L₂ * b
  have hstrict : θ * u1 + (1 - θ) * u2 <
      Real.log (θ * K₁ + (1 - θ) * K₂) * a + Real.log (θ * L₁ + (1 - θ) * L₂) * b := by
    rcases hne with hK | hL
    · have sK := hlog.2 (Set.mem_Ioi.mpr hK₁) (Set.mem_Ioi.mpr hK₂) hK hθ hθ' hsum
      simp only [smul_eq_mul] at sK
      have := mul_lt_mul_of_pos_right sK ha
      have := mul_le_mul_of_nonneg_right cL hb.le
      simp only [u1, u2]
      nlinarith
    · have sL := hlog.2 (Set.mem_Ioi.mpr hL₁) (Set.mem_Ioi.mpr hL₂) hL hθ hθ' hsum
      simp only [smul_eq_mul] at sL
      have := mul_lt_mul_of_pos_right sL hb
      have := mul_le_mul_of_nonneg_right cK ha.le
      simp only [u1, u2]
      nlinarith
  simp only
  rw [hexp K₁ L₁ hK₁ hL₁, hexp K₂ L₂ hK₂ hL₂, hexp _ _ hM hN]
  rcases le_total u1 u2 with h12 | h21
  · calc min (Real.exp u1) (Real.exp u2) ≤ Real.exp u1 := min_le_left _ _
      _ ≤ Real.exp (θ * u1 + (1 - θ) * u2) := Real.exp_le_exp.mpr (by nlinarith)
      _ < _ := Real.exp_lt_exp.mpr hstrict
  · calc min (Real.exp u1) (Real.exp u2) ≤ Real.exp u2 := min_le_right _ _
      _ ≤ Real.exp (θ * u1 + (1 - θ) * u2) := Real.exp_le_exp.mpr (by nlinarith)
      _ < _ := Real.exp_lt_exp.mpr hstrict

/-- The derivative of `K ↦ K^α c` is `(K ↦ K^α)' · c` at `K > 0`. -/
theorem solow_deriv_rpow_mul_const {α c K : ℝ} (hK : 0 < K) :
    deriv (fun K : ℝ => K ^ α * c) K = deriv (fun K : ℝ => K ^ α) K * c :=
  deriv_mul_const (Real.differentiableAt_rpow_const_of_ne α (ne_of_gt hK)) c

/-- AKMM, p. 73: the Cobb–Douglas function `F(K, L) = K^α L^{1−α}`, `0 < α < 1`, "satisfies all
assumptions we need, including the Inada conditions". -/
theorem solow_cobbDouglas_assumptions {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    SolowAssumptions (fun K L => K ^ α * L ^ (1 - α)) := by
  have hT := technology_rpow hα hα1
  have h1α : 0 < 1 - α := by linarith
  have hev : ∀ L : ℝ, ∀ l : Filter ℝ, (∀ᶠ K in l, 0 < K) →
      deriv (fun K : ℝ => K ^ α) * (fun _ => L ^ (1 - α)) =ᶠ[l]
        deriv (fun K : ℝ => K ^ α * L ^ (1 - α)) := by
    intro L l hl
    filter_upwards [hl] with K hK
    exact (solow_deriv_rpow_mul_const hK).symm
  refine ⟨?_, ?_, solow_rpow_strictQuasiconcave hα h1α, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL x hx y hy hxy
    exact mul_lt_mul_of_pos_right (Real.rpow_lt_rpow hx hxy hα) (Real.rpow_pos_of_pos hL _)
  · intro K hK x hx y hy hxy
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hx) hxy h1α)
      (Real.rpow_pos_of_pos hK _)
  · intro c K L hc hK hL
    rw [Real.mul_rpow hc.le hK, Real.mul_rpow hc.le hL.le]
    have : c ^ α * c ^ (1 - α) = c := by
      rw [← Real.rpow_add hc, show α + (1 - α) = 1 by ring, Real.rpow_one]
    calc c ^ α * K ^ α * (c ^ (1 - α) * L ^ (1 - α))
        = (c ^ α * c ^ (1 - α)) * (K ^ α * L ^ (1 - α)) := by ring
      _ = c * (K ^ α * L ^ (1 - α)) := by rw [this]
  · intro L _
    simp [Real.zero_rpow (ne_of_gt hα)]
  · intro L _
    exact hT.continuous.mul continuousOn_const
  · intro L K _ hK
    exact (hT.differentiable K hK).mul_const _
  · intro L _
    refine (hT.derivative_continuous.mul (continuousOn_const (c := L ^ (1 - α)))).congr ?_
    intro K hK
    exact solow_deriv_rpow_mul_const hK
  · intro L hL
    exact (hT.inada_zero.atTop_mul_const (Real.rpow_pos_of_pos hL _)).congr'
      (hev L _ self_mem_nhdsWithin)
  · intro L _
    have h := hT.inada_top.mul_const (L ^ (1 - α))
    rw [zero_mul] at h
    exact h.congr' (hev L _ (eventually_gt_atTop 0))

/-- AKMM, p. 73: for Cobb–Douglas, `f(k) = k^α`. -/
theorem solow_intensive_cobbDouglas (α : ℝ) :
    intensive (fun K L => K ^ α * L ^ (1 - α)) = fun k => k ^ α := by
  funext k
  simp [intensive]

/-- AKMM, Assumptions 1 and 4, p. 72, as printed: no function is strictly increasing in `L` at
`K = 0` and also satisfies `F(0, L) = 0`; monotonicity in `L` can hold only for `K > 0`. -/
theorem solow_assumption1_conflicts_assumption4 :
    ¬ ∃ F : ℝ → ℝ → ℝ, StrictMonoOn (F 0) (Set.Ioi 0) ∧ ∀ L, 0 < L → F 0 L = 0 := by
  rintro ⟨F, hmono, hzero⟩
  have h := hmono (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr two_pos) one_lt_two
  rw [hzero 1 one_pos, hzero 2 two_pos] at h
  exact lt_irrefl _ h

/-- AKMM, p. 74 ("decreasing returns to capital (Assumption 2 above)"), corrected: strict
quasiconcavity does not by itself give diminishing returns. `F(K, L) = K²L²` is strictly
increasing in each input, strictly quasiconcave and has `F(0, L) = 0`, but `f(k) = F(k, 1) = k²`
is not concave. Constant returns (Assumption 3) is what rules this out. -/
theorem solow_assumption2_alone_counterexample :
    StrictQuasiconcavePos (fun K L : ℝ => K ^ (2 : ℝ) * L ^ (2 : ℝ)) ∧
      (∀ L : ℝ, 0 < L → StrictMonoOn (fun K : ℝ => K ^ (2 : ℝ) * L ^ (2 : ℝ)) (Set.Ici 0)) ∧
      (∀ K : ℝ, 0 < K → StrictMonoOn (fun L : ℝ => K ^ (2 : ℝ) * L ^ (2 : ℝ)) (Set.Ioi 0)) ∧
      (∀ L : ℝ, (0 : ℝ) ^ (2 : ℝ) * L ^ (2 : ℝ) = 0) ∧
      ¬ ConcaveOn ℝ (Set.Ici 0) (intensive (fun K L : ℝ => K ^ (2 : ℝ) * L ^ (2 : ℝ))) := by
  refine ⟨solow_rpow_strictQuasiconcave two_pos two_pos, ?_, ?_, ?_, ?_⟩
  · intro L hL x hx y hy hxy
    exact mul_lt_mul_of_pos_right (Real.rpow_lt_rpow hx hxy two_pos) (Real.rpow_pos_of_pos hL _)
  · intro K hK x hx y hy hxy
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hx) hxy two_pos)
      (Real.rpow_pos_of_pos hK _)
  · intro L
    simp
  · intro hc
    have h := hc.2 (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 2))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [intensive, smul_eq_mul, Real.rpow_two] at h
    norm_num at h

end AKMM.Solow
