import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Solow1956.Growth.GeneralSolowExamples
import DiscreteTime.SolowComparative
import DiscreteTime.SolowSwanDynamics
import Mathlib.Analysis.SpecificLimits.Basic
import DiscreteTime.GeneralSolowApplications
import DiscreteTime.SolowConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Intervals
import UzawaModern.Growth.Uzawa
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic Solow model: steady state and dynamics

AKMM, §3.1–3.1.1, pp. 72–75. No technological progress or population growth: `L = 1` and
`k_{t+1} = (1 − δ)k_t + s f(k_t)` (3.5). This is EconomicGrowth's discrete-time Solow map
`Solow1956.DiscreteTime.next f s δ 1`, so the steady state and the global dynamics are imported:

* (3.5) from (3.1)–(3.4) (`eq_3_5`) and its growth-rate form (`solow_growth_rate_form`);
* the steady state `δk̄ = s f(k̄)` exists and is unique (`solow_steady_existsUnique`, from
  `Solow1956.DiscreteTime.existsUnique_steadyState`), also under the book's weaker boundary
  conditions `lim_{k→0} f' > δ/s`, `lim_{k→∞} f' < δ/s` (`solow_steady_existsUnique_weak`,
  new; no Inada and no monotonicity needed), with global monotone convergence under those weak
  conditions when `f` is increasing (`solow_global_convergence_weak`, from
  `Solow1956.DiscreteTime.Map.attracting_orbit`);
* global monotone convergence from every `k₀ > 0` (`solow_global_convergence`) and the two steps
  of the book's proof (`solow_convergence_proof_steps`);
* `f(k)/k` is decreasing (`solow_average_product_strictAnti`);
* Cobb–Douglas: `k̄ = (s/δ)^{1/(1−α)}` (3.6) (`eq_3_6`), `ȳ = (s/δ)^{α/(1−α)}`
  (`solow_cobbDouglas_output`), comparative statics in `s` and `δ`
  (`solow_steady_strictMono_saving`, `solow_steady_strictAnti_depreciation`), and
  `k̄/ȳ = s/δ` (`solow_capital_output_ratio`, `solow_capital_output_ratio_mono`).
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, §3.1, p. 72: with `0 < s`, `0 < δ < 1` the basic model has EconomicGrowth's parameter
conditions with no growth (`γ = 1`). -/
theorem solow_params_basic {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Params s δ 1 :=
  ⟨hs, hδ1.le, one_pos, by linarith⟩

/-- AKMM, (3.5), p. 73: production (3.1), accumulation (3.2), the resource constraint (3.3) and
constant saving (3.4) give the fundamental equation `k_{t+1} = (1 − δ)k_t + s f(k_t)`, which is
EconomicGrowth's map with `γ = 1`; consumption is `c_t = (1 − s) y_t`. -/
theorem eq_3_5 {f : ℝ → ℝ} {s δ : ℝ} {k y c i : ℕ → ℝ} (hy : ∀ t, y t = f (k t))
    (hk : ∀ t, k (t + 1) = i t + (1 - δ) * k t) (hc : ∀ t, y t = c t + i t)
    (hi : ∀ t, i t = s * y t) (t : ℕ) :
    k (t + 1) = (1 - δ) * k t + s * f (k t) ∧ k (t + 1) = next f s δ 1 (k t) ∧
      c t = (1 - s) * y t := by
  have h1 : k (t + 1) = (1 - δ) * k t + s * f (k t) := by rw [hk, hi, hy]; ring
  refine ⟨h1, by rw [next_acemoglu, h1]; ring, ?_⟩
  have := hc t
  rw [hi] at this
  linarith

/-- AKMM, p. 75: the fundamental equation in growth-rate form,
`(k_{t+1} − k_t)/k_t = s f(k_t)/k_t − δ`. -/
theorem solow_growth_rate_form {f : ℝ → ℝ} {s δ : ℝ} {k : ℕ → ℝ} {t : ℕ} (hk : k t ≠ 0)
    (hsucc : k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (k (t + 1) - k t) / k t = s * f (k t) / k t - δ := by
  rw [hsucc]
  field_simp
  ring

/-- AKMM, p. 73: a constant path `k_t = k̄` solves (3.5) exactly when `δ k̄ = s f(k̄)`. -/
theorem solow_fixed_iff {f : ℝ → ℝ} {s δ k : ℝ} : next f s δ 1 k = k ↔ δ * k = s * f k := by
  rw [next_acemoglu]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 73: under Assumptions 1–6 a strictly positive steady state `δk̄ = s f(k̄)` exists and
is unique (EconomicGrowth's `existsUnique_steadyState`, Acemoglu Proposition 2.2). -/
theorem solow_steady_existsUnique (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) : ∃! k : ℝ, 0 < k ∧ δ * k = s * intensive F k := by
  simpa only [solow_fixed_iff] using
    existsUnique_steadyState (solow_technology hF) (solow_params_basic hs hδ hδ1)

/-- AKMM, p. 73: the steady state `k̄` (EconomicGrowth's `steady` at `γ = 1`) is positive and
solves `δ k̄ = s f(k̄)`. -/
theorem solow_steady_spec (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    0 < steady (solow_technology hF) s δ 1 ∧
      δ * steady (solow_technology hF) s δ 1 =
        s * intensive F (steady (solow_technology hF) s δ 1) := by
  obtain ⟨h1, h2⟩ := steady_spec (solow_technology hF) (solow_params_basic hs hδ hδ1)
  exact ⟨h1, solow_fixed_iff.mp h2⟩

/-- AKMM, p. 74: global and monotone convergence. Every path of (3.5) from `k₀ > 0` stays
positive; it is strictly increasing and below `k̄` if `k₀ < k̄`, strictly decreasing and above
`k̄` if `k₀ > k̄`, constant if `k₀ = k̄`; it stays between `k₀` and `k̄` and converges to `k̄`
(EconomicGrowth's `IsPath.orbit`, Acemoglu Proposition 2.5). -/
theorem solow_global_convergence (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * intensive F (k t)) :
    (∀ t, 0 < k t) ∧
      (k 0 < steady (solow_technology hF) s δ 1 →
        StrictMono k ∧ ∀ t, k t < steady (solow_technology hF) s δ 1) ∧
      (steady (solow_technology hF) s δ 1 < k 0 →
        StrictAnti k ∧ ∀ t, steady (solow_technology hF) s δ 1 < k t) ∧
      (k 0 = steady (solow_technology hF) s δ 1 → ∀ t, k t = steady (solow_technology hF) s δ 1) ∧
      (∀ t, min (k 0) (steady (solow_technology hF) s δ 1) ≤ k t ∧
        k t ≤ max (k 0) (steady (solow_technology hF) s δ 1)) ∧
      Tendsto k atTop (𝓝 (steady (solow_technology hF) s δ 1)) :=
  IsPath.orbit (solow_technology hF) (solow_params_basic hs hδ hδ1)
    ⟨h0, fun t => by rw [hk, next_acemoglu]; ring⟩

/-- AKMM, p. 74, the proof of convergence: if `0 < k_t < k̄` then (i) `k_{t+1} > k_t`, because
`s f(k_t) > δ k_t`, and (ii) `k_{t+1} < k̄`, because the right side of (3.5) is increasing. -/
theorem solow_convergence_proof_steps (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) {k : ℝ} (hk : 0 < k) (hlt : k < steady (solow_technology hF) s δ 1) :
    δ * k < s * intensive F k ∧ k < (1 - δ) * k + s * intensive F k ∧
      (1 - δ) * k + s * intensive F k < steady (solow_technology hF) s δ 1 := by
  have P := solow_params_basic hs hδ hδ1
  have h := solow_technology hF
  have h1 := next_gt_self h P hk hlt
  have hfix := (steady_spec h P).2
  have h2 := next_strictMono h P (Set.mem_Ici.mpr hk.le)
    (Set.mem_Ici.mpr (steady_spec h P).1.le) hlt
  rw [hfix] at h2
  rw [next_acemoglu] at h1 h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- AKMM, p. 75: `f(0) = 0` and diminishing returns make the average product `f(k)/k` strictly
decreasing (EconomicGrowth's `Technology.average_strictAnti`). -/
theorem solow_average_product_strictAnti (hF : SolowAssumptions F) :
    StrictAntiOn (fun k => intensive F k / k) (Set.Ioi 0) :=
  (solow_technology hF).average_strictAnti

/-- AKMM, (3.6), p. 73: with `f(k) = k^α`, `k̄ = (s/δ)^{1/(1−α)}`; it is the steady state of
EconomicGrowth's map (`Solow1956.DiscreteTime.CobbDouglas.steady_eq`) and the unique positive
solution of `δ k = s k^α`. -/
theorem eq_3_6 {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) :
    steady (technology_rpow hα hα1) s δ 1 = (s / δ) ^ (1 / (1 - α)) ∧
      δ * (s / δ) ^ (1 / (1 - α)) = s * ((s / δ) ^ (1 / (1 - α))) ^ α := by
  have h := CobbDouglas.steady_eq hα hα1 (solow_params_basic hs hδ hδ1)
  rw [show (1 : ℝ) - 1 + δ = δ by ring] at h
  have heq : steady (technology_rpow hα hα1) s δ 1 = (s / δ) ^ (1 / (1 - α)) := by
    rw [h, Solow1956.SolowSwan.CobbDouglas.steadyState, one_div]
  refine ⟨heq, ?_⟩
  have := solow_fixed_iff.mp (steady_spec (technology_rpow hα hα1) (solow_params_basic hs hδ hδ1)).2
  rw [heq] at this
  exact this

/-- AKMM, p. 74: with Cobb–Douglas production, steady-state output is
`ȳ = k̄^α = (s/δ)^{α/(1−α)}`. -/
theorem solow_cobbDouglas_output {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    steady (technology_rpow hα hα1) s δ 1 ^ α = (s / δ) ^ (α / (1 - α)) := by
  rw [(eq_3_6 hα hα1 hs hδ hδ1).1, ← Real.rpow_mul (div_pos hs hδ).le]
  congr 1
  ring

/-- AKMM, p. 74: the steady state capital stock and output are strictly increasing in the saving
rate (EconomicGrowth's `steady_strictMono_saving`); stated for every `f` satisfying Assumptions
1–6, which includes the book's Cobb–Douglas case. -/
theorem solow_steady_strictMono_saving (hF : SolowAssumptions F) {s₁ s₂ δ : ℝ} (hs₁ : 0 < s₁)
    (hs : s₁ < s₂) (hδ : 0 < δ) :
    steady (solow_technology hF) s₁ δ 1 < steady (solow_technology hF) s₂ δ 1 ∧
      intensive F (steady (solow_technology hF) s₁ δ 1) <
        intensive F (steady (solow_technology hF) s₂ δ 1) := by
  have hm : (0 : ℝ) < 1 - 1 + δ := by linarith
  have h := steady_strictMono_saving (solow_technology hF) hm (Set.mem_Ioi.mpr hs₁)
    (Set.mem_Ioi.mpr (hs₁.trans hs)) hs
  refine ⟨h, solow_intensive_strictMono hF ?_ ?_ h⟩
  · exact Set.mem_Ici.mpr (steadyCapital_spec (solow_technology hF) hs₁ hm).1.le
  · exact Set.mem_Ici.mpr (steadyCapital_spec (solow_technology hF) (hs₁.trans hs) hm).1.le

/-- AKMM, p. 74: the steady state capital stock and output are strictly decreasing in the
depreciation rate (EconomicGrowth's `steady_strictAnti_depreciation`). -/
theorem solow_steady_strictAnti_depreciation (hF : SolowAssumptions F) {s δ₁ δ₂ : ℝ}
    (hs : 0 < s) (hδ₁ : 0 < δ₁) (hδ : δ₁ < δ₂) :
    steady (solow_technology hF) s δ₂ 1 < steady (solow_technology hF) s δ₁ 1 ∧
      intensive F (steady (solow_technology hF) s δ₂ 1) <
        intensive F (steady (solow_technology hF) s δ₁ 1) := by
  have hm : (0 : ℝ) < 1 - 1 + δ₁ := by linarith
  have h := steady_strictAnti_depreciation (solow_technology hF) hs hm hδ
  refine ⟨h, solow_intensive_strictMono hF ?_ ?_ h⟩
  · exact Set.mem_Ici.mpr
      (steadyCapital_spec (solow_technology hF) hs (by linarith : (0 : ℝ) < 1 - 1 + δ₂)).1.le
  · exact Set.mem_Ici.mpr (steadyCapital_spec (solow_technology hF) hs hm).1.le

/-- AKMM, p. 75: the steady-state capital–output ratio is `k̄/ȳ = s/δ` (stated in the book for
Cobb–Douglas; it holds for every technology since `δ k̄ = s f(k̄)`). -/
theorem solow_capital_output_ratio (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    steady (solow_technology hF) s δ 1 / intensive F (steady (solow_technology hF) s δ 1) =
      s / δ := by
  obtain ⟨hk, he⟩ := solow_steady_spec hF hs hδ hδ1
  have hy := solow_intensive_pos hF hk
  rw [div_eq_div_iff (ne_of_gt hy) (ne_of_gt hδ)]
  linarith

/-- AKMM, p. 75: "in the long run `k_t/y_t` is larger when `s` is larger and when `δ` is
smaller". -/
theorem solow_capital_output_ratio_mono (hF : SolowAssumptions F) {s₁ s₂ δ₁ δ₂ : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hδ₂ : 0 < δ₂) (hδ : δ₂ ≤ δ₁) (hδ1 : δ₁ < 1) :
    steady (solow_technology hF) s₁ δ₁ 1 / intensive F (steady (solow_technology hF) s₁ δ₁ 1) ≤
      steady (solow_technology hF) s₂ δ₂ 1 /
        intensive F (steady (solow_technology hF) s₂ δ₂ 1) := by
  rw [solow_capital_output_ratio hF hs₁ (hδ₂.trans_le hδ) hδ1,
    solow_capital_output_ratio hF (hs₁.trans_le hs) hδ₂ (hδ.trans_lt hδ1)]
  exact div_le_div₀ (hs₁.trans_le hs).le hs hδ₂ hδ

/-- The average product of a strictly concave `f` with `f(0) = 0` is strictly decreasing. -/
theorem solow_average_strictAnti_of_concave {f : ℝ → ℝ} (h0 : f 0 = 0)
    (hcc : StrictConcaveOn ℝ (Set.Ici 0) f) : StrictAntiOn (fun k => f k / k) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h := hcc.2 (Set.mem_Ici.mpr hb'.le) (Set.mem_Ici.mpr (le_refl 0)) (ne_of_gt hb')
    (div_pos ha' hb') (sub_pos.mpr ((div_lt_one hb').mpr hab)) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, h0] at h
  rw [div_mul_cancel₀ a (ne_of_gt hb')] at h
  simp only
  rw [div_lt_div_iff₀ hb' ha']
  have h2 : a * f b < f a * b := by
    have := mul_lt_mul_of_pos_right h hb'
    rwa [show a / b * f b * b = a * f b by field_simp] at this
  linarith

/-- AKMM, p. 73: "the Inada conditions are stronger than necessary: they can be replaced by
weaker versions `lim_{k→0} F₁(k, 1) > δ/s` and `lim_{k→∞} F₁(k, 1) < δ/s`". For a continuous,
strictly concave `f` with `f(0) = 0`, differentiable on `(0, ∞)`, with `f' > δ/s` near zero and
`f' < δ/s` for large `k` (implied by the two limit conditions), the steady state `δk = s f(k)`,
`k > 0`, exists and is unique. -/
theorem solow_steady_existsUnique_weak {f : ℝ → ℝ} {s δ : ℝ} (hs : 0 < s)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hcc : StrictConcaveOn ℝ (Set.Ici 0) f) (hlow : ∀ᶠ k in 𝓝[>] 0, δ / s < deriv f k)
    (hhigh : ∀ᶠ k in atTop, deriv f k < δ / s) :
    ∃! k : ℝ, 0 < k ∧ δ * k = s * f k := by
  -- a point near zero where investment exceeds depreciation
  have hz : ∀ᶠ k in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨a, ha, hfa⟩ := (hz.and hlow).exists
  have hga : δ * a < s * f a := by
    have hsl := hcc.concaveOn.deriv_le_slope (Set.mem_Ici.mpr (le_refl 0))
      (Set.mem_Ici.mpr ha.le) ha (hd a ha)
    rw [slope_def_field, h0, sub_zero, sub_zero, le_div_iff₀ ha] at hsl
    have := (div_lt_iff₀ hs).mp hfa
    nlinarith
  -- a large point where depreciation exceeds investment
  obtain ⟨b, hfb, hab⟩ := (hhigh.and (eventually_ge_atTop (a + 1))).exists
  have hb : 0 < b := by linarith
  set c := δ - s * deriv f b with hcdef
  have hcpos : 0 < c := by have := (lt_div_iff₀ hs).mp hfb; linarith
  set K := max (b + 1) ((s * f b - s * deriv f b * b) / c + 1) with hK
  have hbK : b < K := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hgK : s * f K - δ * K ≤ 0 := by
    have hsl := hcc.concaveOn.slope_le_deriv (Set.mem_Ici.mpr hb.le)
      (Set.mem_Ici.mpr (hb.trans hbK).le) hbK (hd b hb)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hbK)] at hsl
    have h2 : (s * f b - s * deriv f b * b) / c + 1 ≤ K := le_max_right _ _
    have h3 : s * f b - s * deriv f b * b ≤ c * K := by
      have := (div_le_iff₀ hcpos).mp (by linarith : (s * f b - s * deriv f b * b) / c ≤ K)
      linarith
    have h4 := mul_le_mul_of_nonneg_left hsl hs.le
    nlinarith
  have haK : a ≤ K := by linarith
  have hcont : ContinuousOn (fun k => s * f k - δ * k) (Set.Icc a K) :=
    ((hc.mono (fun x hx => Set.mem_Ici.mpr (ha.le.trans hx.1))).const_mul s).sub
      (continuousOn_id.const_mul δ)
  obtain ⟨k, hk, hk0⟩ := intermediate_value_Icc' haK hcont
    ⟨hgK, by change 0 ≤ s * f a - δ * a; linarith⟩
  have hk0' : s * f k - δ * k = 0 := hk0
  have hkpos : 0 < k := ha.trans_le hk.1
  refine ⟨k, ⟨hkpos, by linarith⟩, ?_⟩
  rintro y ⟨hy, hye⟩
  have hanti := solow_average_strictAnti_of_concave h0 hcc
  apply hanti.injOn (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hkpos)
  change f y / y = f k / k
  rw [div_eq_div_iff (ne_of_gt hy) (ne_of_gt hkpos)]
  have e1 : s * (f y * k) = δ * y * k := by rw [← mul_assoc, ← hye]
  have e2 : s * (f k * y) = δ * k * y := by
    rw [← mul_assoc, show s * f k = δ * k by linarith]
  have : s * (f y * k) = s * (f k * y) := by rw [e1, e2]; ring
  exact mul_left_cancel₀ (ne_of_gt hs) this

/-- AKMM, p. 74, under the weak boundary conditions of p. 73: if moreover `f` is strictly
increasing and `0 < δ ≤ 1`, every path of (3.5) from `k₀ > 0` converges monotonically to the
unique steady state (EconomicGrowth's `Map.attracting_orbit`, which needs no derivative). -/
theorem solow_global_convergence_weak {f : ℝ → ℝ} {s δ ks : ℝ} (hs : 0 < s) (hδ1 : δ ≤ 1)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hmono : StrictMonoOn f (Set.Ici 0))
    (hcc : StrictConcaveOn ℝ (Set.Ici 0) f) (hks : 0 < ks) (hfix : δ * ks = s * f ks)
    {k : ℕ → ℝ} (hk0 : 0 < k 0) (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (∀ t, 0 < k t) ∧ (k 0 < ks → StrictMono k ∧ ∀ t, k t < ks) ∧
      (ks < k 0 → StrictAnti k ∧ ∀ t, ks < k t) ∧ Tendsto k atTop (𝓝 ks) := by
  have hanti := solow_average_strictAnti_of_concave h0 hcc
  have hav : f ks / ks = δ / s := by
    rw [div_eq_div_iff (ne_of_gt hks) (ne_of_gt hs)]; linarith
  have hgm : StrictMonoOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have h1 := mul_lt_mul_of_pos_left (hmono (Set.mem_Ici.mpr (le_of_lt hx))
      (Set.mem_Ici.mpr (le_of_lt hy)) hxy) hs
    have h2 := mul_le_mul_of_nonneg_left hxy.le (sub_nonneg.mpr hδ1)
    simp only
    linarith
  have hgc : ContinuousOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) :=
    (continuousOn_id.const_mul (1 - δ)).add
      ((hc.mono (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))).const_mul s)
  have hbelow : ∀ y, 0 < y → y < ks → y < (1 - δ) * y + s * f y := by
    intro y hy hlt
    have h := hanti (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hks) hlt
    simp only at h
    rw [hav, div_lt_div_iff₀ hs hy] at h
    linarith
  have habove : ∀ y, ks < y → (1 - δ) * y + s * f y < y := by
    intro y hlt
    have h := hanti (Set.mem_Ioi.mpr hks) (Set.mem_Ioi.mpr (hks.trans hlt)) hlt
    simp only at h
    rw [hav, div_lt_div_iff₀ (hks.trans hlt) hs] at h
    linarith
  obtain ⟨hpos, hlow, hhigh, _, _, hlim⟩ := Map.attracting_orbit hgm hgc hks
    (by linarith) hbelow habove hk0 hk
  exact ⟨hpos, hlow, hhigh, hlim⟩

end AKMM.Solow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Other kinds of dynamics: endogenous growth, poverty traps, local stability

AKMM, §3.1.1, "Other kinds of dynamics", pp. 75–78 (the boxes on endogenous growth, poverty
traps, and non-monotonic dynamics and chaos), for the basic map `k ↦ (1 − δ)k + s f(k)`.

* **Endogenous growth** (p. 75): if `F₁(k, 1) > δ/s` everywhere there is no positive steady state
  and capital rises forever (`solow_endogenous_no_steady_state`); if `F₁(k, 1) ≥ c > δ/s`
  uniformly, capital grows at least geometrically and diverges (`solow_endogenous_growth`). In the
  `AK` case two countries keep a constant percentage gap (`solow_ak_constant_gap`); with
  `Y = AK + BL` (footnote 2) labour stops mattering asymptotically (`solow_ak_plus_labour`).
* **Poverty traps** (pp. 76–77): with an increasing map, of two adjacent steady states at least
  one is not locally attracting (`solow_poverty_trap_unstable`).
* **Non-monotonic dynamics** (p. 77): a decreasing map makes the path jump across the steady
  state (`solow_decreasing_map_overshoots`); footnote a, local stability when the slope at the
  steady state is below one in absolute value (`solow_local_stability`, with the geometric bound).
  This is the scalar fixed-point result of Miao's `DifferenceEquations`, proved here directly.

The chaos claim is narrative and is not formalised.
-/

namespace AKMM.Solow

open Filter Topology

/-- AKMM, p. 75 (endogenous growth): if the marginal product exceeds `δ/s` at every `k > 0`, then
`s f(k) > δ k` for every `k > 0`: there is no steady state with `k̄ > 0`, and every path of (3.5)
from `k₀ > 0` is strictly increasing ("`k_t` keeps growing larger over time"). -/
theorem solow_endogenous_no_steady_state {f : ℝ → ℝ} {s δ : ℝ} (hs : 0 < s)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hmp : ∀ k, 0 < k → δ / s < deriv f k) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (∀ x, 0 < x → δ * x < s * f x) ∧ (∀ x, 0 < x → δ * x ≠ s * f x) ∧ StrictMono k := by
  have hg : StrictMonoOn (fun x => s * f x - δ * x) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (f := fun x => s * f x - δ * x) (convex_Ici 0)
      ((hc.const_mul s).sub (continuousOn_id.const_mul δ))
    intro x hx
    rw [interior_Ici] at hx
    have hx' : (0 : ℝ) < x := hx
    have hD : HasDerivAt (fun x => s * f x - δ * x) (s * deriv f x - δ) x := by
      have := ((hd x hx').hasDerivAt.const_mul s).sub ((hasDerivAt_id' x).const_mul δ)
      rwa [mul_one] at this
    rw [hD.deriv]
    have := (div_lt_iff₀ hs).mp (hmp x hx')
    linarith
  have hpos : ∀ x, 0 < x → δ * x < s * f x := by
    intro x hx
    have := hg (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx.le) hx
    simp only [h0, mul_zero, sub_zero] at this
    linarith
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ u ih => rw [hk u]; have := hpos _ ih; linarith
  refine ⟨hpos, fun x hx => ne_of_lt (hpos x hx), strictMono_nat_of_lt_succ fun t => ?_⟩
  rw [hk t]
  have := hpos _ (hkpos t)
  linarith

/-- AKMM, p. 75 (endogenous growth, "`F₁(k, 1)` uniformly above `δ/s`"): if `f'(k) ≥ c` for all
`k > 0` with `c > δ/s`, then `f(k) ≥ c k`, every path of (3.5) satisfies
`k_t ≥ (1 − δ + s c)^t k₀` with `1 − δ + s c > 1`, and `k_t → ∞`: unbounded growth "by itself". -/
theorem solow_endogenous_growth {f : ℝ → ℝ} {s δ c : ℝ} (hs : 0 < s)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hcs : δ / s < c) (hmp : ∀ k, 0 < k → c ≤ deriv f k) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (∀ x, 0 ≤ x → c * x ≤ f x) ∧ 1 < 1 - δ + s * c ∧
      (∀ t, (1 - δ + s * c) ^ t * k 0 ≤ k t) ∧ Tendsto k atTop atTop := by
  have hg : MonotoneOn (fun x => f x - c * x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (f := fun x => f x - c * x) (convex_Ici 0)
      (hc.sub (continuousOn_id.const_mul c))
    · intro x hx
      rw [interior_Ici] at hx
      exact ((hd x hx).sub ((differentiableAt_id).const_mul c)).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : (0 : ℝ) < x := hx
      have hD : HasDerivAt (fun x => f x - c * x) (deriv f x - c) x := by
        have := (hd x hx').hasDerivAt.sub ((hasDerivAt_id' x).const_mul c)
        rwa [mul_one] at this
      rw [hD.deriv]
      linarith [hmp x hx']
  have hlin : ∀ x, 0 ≤ x → c * x ≤ f x := by
    intro x hx
    have := hg (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx) hx
    simp only [h0, mul_zero, sub_zero] at this
    linarith
  have hfac : 1 < 1 - δ + s * c := by
    have := (div_lt_iff₀ hs).mp hcs
    linarith
  have hbound : ∀ t, (1 - δ + s * c) ^ t * k 0 ≤ k t := by
    intro t
    induction t with
    | zero => simp
    | succ u ih =>
      have hku : 0 ≤ k u := le_trans (mul_nonneg (pow_nonneg (by linarith) _) hk0.le) ih
      rw [hk u, pow_succ]
      have := mul_le_mul_of_nonneg_left (hlin _ hku) hs.le
      have h2 : (1 - δ + s * c) * ((1 - δ + s * c) ^ u * k 0) ≤ (1 - δ + s * c) * k u :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      nlinarith
  refine ⟨hlin, hfac, hbound, ?_⟩
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hfac).atTop_mul_const hk0
  exact tendsto_atTop_mono hbound hpow

/-- AKMM, p. 76 (endogenous growth with `y = A k`): two identical countries starting from
different capital stocks stay forever different, with a constant percentage gap: `k_t/k'_t` is
constant. -/
theorem solow_ak_constant_gap {s δ A : ℝ} {k k' : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * (A * k t))
    (hk' : ∀ t, k' (t + 1) = (1 - δ) * k' t + s * (A * k' t))
    (hfac : 0 < 1 - δ + s * A) (h0 : 0 < k' 0) (t : ℕ) :
    k t / k' t = k 0 / k' 0 := by
  have e : ∀ (x : ℕ → ℝ), (∀ t, x (t + 1) = (1 - δ) * x t + s * (A * x t)) →
      ∀ t, x t = (1 - δ + s * A) ^ t * x 0 := by
    intro x hx t
    induction t with
    | zero => simp
    | succ u ih => rw [hx u, ih, pow_succ]; ring
  rw [e k hk t, e k' hk' t]
  have : 0 < (1 - δ + s * A) ^ t := pow_pos hfac t
  field_simp

/-- AKMM, footnote 2, p. 75: with `Y = AK + BL` (constant returns) and `A > δ/s`, capital per
worker diverges and the labour term stops mattering: the capital term's share `Ak_t/f(k_t)` of
output tends to one. -/
theorem solow_ak_plus_labour {s δ A B : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hA : δ / s < A) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * (A * k t + B)) :
    Tendsto k atTop atTop ∧ Tendsto (fun t => A * k t / (A * k t + B)) atTop (𝓝 1) := by
  have hApos : 0 < A := lt_of_le_of_lt (div_nonneg hδ hs.le) hA
  -- the affine technology has `f' = A`; we work with `f(k) = A k + B` on `k ≥ 0`
  have hfac : 1 < 1 - δ + s * A := by have := (div_lt_iff₀ hs).mp hA; linarith
  have hbound : ∀ t, (1 - δ + s * A) ^ t * k 0 ≤ k t := by
    intro t
    induction t with
    | zero => simp
    | succ u ih =>
      rw [hk u, pow_succ]
      have h2 : (1 - δ + s * A) * ((1 - δ + s * A) ^ u * k 0) ≤ (1 - δ + s * A) * k u :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have := mul_nonneg hs.le hB
      nlinarith
  have hdiv : Tendsto k atTop atTop :=
    tendsto_atTop_mono hbound ((tendsto_pow_atTop_atTop_of_one_lt hfac).atTop_mul_const hk0)
  refine ⟨hdiv, ?_⟩
  have hinv : Tendsto (fun t => B / (A * k t)) atTop (𝓝 0) :=
    (hdiv.const_mul_atTop hApos).const_div_atTop B
  have hlim := (hinv.const_add 1).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  rw [add_zero, inv_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdiv.eventually_gt_atTop 0] with t ht
  have : 0 < A * k t := mul_pos hApos ht
  field_simp

/-- AKMM, pp. 76–77 (poverty traps): a steady state `k̄` of a map `g` is locally attracting if
every path started close enough to it converges to it. -/
def SolowLocallyAttracting (g : ℝ → ℝ) (kbar : ℝ) : Prop :=
  ∃ ε > 0, ∀ x₀, |x₀ - kbar| < ε → Tendsto (fun t => g^[t] x₀) atTop (𝓝 kbar)

/-- AKMM, p. 77 (poverty traps): "at least one of the steady states will then not be stable".
For a continuous increasing map with adjacent steady states `k̄₁ < k̄₂` (no steady state
between them), `k̄₁` and `k̄₂` are not both locally attracting: between them the map lies on one
side of the diagonal, and paths started there move away from one of the two. -/
theorem solow_poverty_trap_unstable {g : ℝ → ℝ} {k₁ k₂ : ℝ} (hlt : k₁ < k₂)
    (hc : ContinuousOn g (Set.Icc k₁ k₂)) (hmono : MonotoneOn g (Set.Icc k₁ k₂))
    (h₁ : g k₁ = k₁) (h₂ : g k₂ = k₂) (hnone : ∀ x, k₁ < x → x < k₂ → g x ≠ x) :
    ¬ (SolowLocallyAttracting g k₁ ∧ SolowLocallyAttracting g k₂) := by
  rintro ⟨⟨ε₁, hε₁, hat₁⟩, ⟨ε₂, hε₂, hat₂⟩⟩
  -- the sign of `g x - x` is constant on `(k₁, k₂)`
  have hsign : (∀ x, k₁ < x → x < k₂ → x < g x) ∨ (∀ x, k₁ < x → x < k₂ → g x < x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, ha1, ha2, hga⟩, ⟨b, hb1, hb2, hgb⟩⟩ := hcon
    have hga' : g a < a := lt_of_le_of_ne hga (hnone a ha1 ha2)
    have hgb' : b < g b := lt_of_le_of_ne hgb (fun h => hnone b hb1 hb2 h.symm)
    have hcc : ContinuousOn (fun x => g x - x) (Set.Ioo k₁ k₂) :=
      (hc.mono Set.Ioo_subset_Icc_self).sub continuousOn_id
    have hiv := isPreconnected_Ioo.intermediate_value (Set.mem_Ioo.mpr ⟨ha1, ha2⟩)
      (Set.mem_Ioo.mpr ⟨hb1, hb2⟩) hcc
    obtain ⟨x, hx, hx0⟩ := hiv (Set.mem_Icc.mpr ⟨(by linarith : g a - a ≤ 0),
      (by linarith : (0 : ℝ) ≤ g b - b)⟩)
    have hx0' : g x - x = 0 := hx0
    exact hnone x hx.1 hx.2 (by linarith)
  rcases hsign with hup | hdown
  · -- paths just above `k₁` rise: `k₁` is not attracting
    set x₀ := k₁ + min ε₁ (k₂ - k₁) / 2 with hx₀
    have hm : 0 < min ε₁ (k₂ - k₁) := lt_min hε₁ (by linarith)
    have hx1 : k₁ < x₀ := by linarith
    have hx2 : x₀ ≤ k₂ := by have := min_le_right ε₁ (k₂ - k₁); linarith
    have hstay : ∀ t, x₀ ≤ g^[t] x₀ ∧ g^[t] x₀ ≤ k₂ := by
      intro t
      induction t with
      | zero => exact ⟨le_rfl, hx2⟩
      | succ u ih =>
        rw [Function.iterate_succ_apply']
        have hmem : g^[u] x₀ ∈ Set.Icc k₁ k₂ := ⟨by linarith [ih.1], ih.2⟩
        refine ⟨?_, ?_⟩
        · rcases ih.2.lt_or_eq with hl | he
          · exact ih.1.trans (hup _ (by linarith [ih.1]) hl).le
          · rw [he, h₂]; exact hx2
        · rw [← h₂]; exact hmono hmem (Set.right_mem_Icc.mpr hlt.le) ih.2
    have hlim := hat₁ x₀ (by
      rw [abs_of_pos (by linarith)]
      have := min_le_left ε₁ (k₂ - k₁)
      linarith)
    have := ge_of_tendsto hlim (Eventually.of_forall fun t => (hstay t).1)
    linarith
  · -- paths just below `k₂` fall: `k₂` is not attracting
    set x₀ := k₂ - min ε₂ (k₂ - k₁) / 2 with hx₀
    have hm : 0 < min ε₂ (k₂ - k₁) := lt_min hε₂ (by linarith)
    have hx2 : x₀ < k₂ := by linarith
    have hx1 : k₁ ≤ x₀ := by have := min_le_right ε₂ (k₂ - k₁); linarith
    have hstay : ∀ t, k₁ ≤ g^[t] x₀ ∧ g^[t] x₀ ≤ x₀ := by
      intro t
      induction t with
      | zero => exact ⟨hx1, le_rfl⟩
      | succ u ih =>
        rw [Function.iterate_succ_apply']
        have hmem : g^[u] x₀ ∈ Set.Icc k₁ k₂ := ⟨ih.1, by linarith [ih.2]⟩
        refine ⟨?_, ?_⟩
        · rw [← h₁]; exact hmono (Set.left_mem_Icc.mpr hlt.le) hmem ih.1
        · rcases ih.1.lt_or_eq with hl | he
          · exact (hdown _ hl (by linarith [ih.2])).le.trans ih.2
          · rw [← he, h₁]; exact hx1
    have hlim := hat₂ x₀ (by
      rw [abs_of_neg (by linarith)]
      have := min_le_left ε₂ (k₂ - k₁)
      linarith)
    have := le_of_tendsto hlim (Eventually.of_forall fun t => (hstay t).2)
    linarith

/-- AKMM, p. 77 (non-monotonic dynamics): when the right side of (3.5) is decreasing, the path
jumps across the steady state, so convergence, if any, is not monotonic. -/
theorem solow_decreasing_map_overshoots {g : ℝ → ℝ} {kbar x : ℝ} (hanti : StrictAnti g)
    (hfix : g kbar = kbar) : (x < kbar → kbar < g x) ∧ (kbar < x → g x < kbar) :=
  ⟨fun h => hfix ▸ hanti h, fun h => hfix ▸ hanti h⟩

/-- AKMM, footnote a, p. 78: "locally stable dynamics will occur if the slope at the steady state
is less than 1 in absolute value". If `g(k̄) = k̄` and `|g'(k̄)| < 1`, there are `ε > 0` and
`ρ < 1` with `|g^t(x₀) − k̄| ≤ ρ^t |x₀ − k̄|` whenever `|x₀ − k̄| < ε`; in particular every such
path converges to `k̄`. -/
theorem solow_local_stability {g : ℝ → ℝ} {kbar g' : ℝ} (hg : HasDerivAt g g' kbar)
    (hfix : g kbar = kbar) (hslope : |g'| < 1) :
    ∃ ε > 0, ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x₀, |x₀ - kbar| < ε →
      (∀ t, |g^[t] x₀ - kbar| ≤ ρ ^ t * |x₀ - kbar|) ∧
        Tendsto (fun t => g^[t] x₀) atTop (𝓝 kbar) := by
  set c := (1 - |g'|) / 2 with hcdef
  have hc : 0 < c := by linarith
  have hlo := (hasDerivAt_iff_isLittleO.mp hg).def hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set ρ := |g'| + c with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  have hstep : ∀ x, |x - kbar| < ε → |g x - kbar| ≤ ρ * |x - kbar| := by
    intro x hx
    have h := hball (by rw [Real.dist_eq]; exact hx)
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have htri : |g x - kbar| ≤ |g x - kbar - (x - kbar) * g'| + |(x - kbar) * g'| := by
      have := abs_add_le (g x - kbar - (x - kbar) * g') ((x - kbar) * g')
      rwa [sub_add_cancel] at this
    rw [abs_mul] at htri
    nlinarith [abs_nonneg (x - kbar)]
  refine ⟨ε, hε, ρ, hρ0, hρ1, fun x₀ hx₀ => ?_⟩
  have hbound : ∀ t, |g^[t] x₀ - kbar| ≤ ρ ^ t * |x₀ - kbar| := by
    intro t
    induction t with
    | zero => simp
    | succ u ih =>
      rw [Function.iterate_succ_apply']
      have hin : |g^[u] x₀ - kbar| < ε := by
        calc |g^[u] x₀ - kbar| ≤ ρ ^ u * |x₀ - kbar| := ih
          _ ≤ 1 * |x₀ - kbar| := mul_le_mul_of_nonneg_right
              (pow_le_one₀ hρ0 hρ1.le) (abs_nonneg _)
          _ < ε := by rw [one_mul]; exact hx₀
      calc |g (g^[u] x₀) - kbar| ≤ ρ * |g^[u] x₀ - kbar| := hstep _ hin
        _ ≤ ρ * (ρ ^ u * |x₀ - kbar|) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (u + 1) * |x₀ - kbar| := by ring
  refine ⟨hbound, ?_⟩
  have hpow : Tendsto (fun t => ρ ^ t * |x₀ - kbar|) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const |x₀ - kbar|
    rwa [zero_mul] at this
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun t => dist_nonneg) (fun t => by rw [Real.dist_eq]; exact hbound t) hpow

end AKMM.Solow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The growing economy, balanced growth, and factor prices

AKMM, §3.2–3.3, pp. 78–81. Labour-augmenting technology `A_{t+1} = (1 + γ)A_t` and labour
`L_{t+1} = (1 + n)L_t`; capital per efficiency unit `k̃_t = K_t/(A_t L_t)` follows (3.7),
`(1 + γ)(1 + n) k̃_{t+1} = (1 − δ)k̃_t + s f(k̃_t)`, which is EconomicGrowth's map
`Solow1956.DiscreteTime.next f s δ ((1 + γ)(1 + n))`.

* (3.7) from the aggregate equations (`eq_3_7`, via EconomicGrowth's
  `capitalPerEffectiveWorker_succ`); the balanced-growth `k̃̄` exists uniquely
  (`solow_bgp_existsUnique`); Cobb–Douglas closed form (3.8) (`eq_3_8`); every path of (3.7)
  converges monotonically (`solow_detrended_convergence`); `γ` and `n` act like depreciation
  (`solow_bgp_strictAnti_growth`).
* Untransforming: `Y/(AL) = f(k̃)`, `y = Y/L = A f(k̃)`, `K/Y = k̃/f(k̃)`
  (`solow_untransform`); from
  the aggregate equations `k̃_t`, `Y_t/(A_tL_t)` and `K_t/Y_t` converge
  (`solow_aggregate_convergence`).
* Growth rates (p. 80): on the balanced path income per capita grows at `γ`
  (`solow_bgp_income_growth`); in general its growth rate is `(1 + γ) f(k̃_{t+1})/f(k̃_t) − 1`
  (`solow_income_growth_identity`), above `γ` below the balanced path and below `γ` above it
  (`solow_transition_growth`), and it converges to `γ` (`solow_income_growth_tendsto`); `y_t/A_t`
  converges to `f(k̃̄)` (`solow_income_long_run`).
* Factor prices (§3.3, p. 81): `r = F₁(K, AL) = f'(k̃)` (`solow_rental_rate`),
  `w = F₂(K, AL) = f(k̃) − k̃ f'(k̃)` (`solow_wage_rate`; EconomicGrowth's `wage`), Euler's theorem
  `Y = K F₁ + AL F₂` (`solow_euler`), the shares (`solow_factor_shares`), their constancy on the
  balanced path and their convergence along any path (`solow_factor_prices_bgp`,
  `solow_factor_prices_tendsto`), and Cobb–Douglas shares `α`, `1 − α` everywhere
  (`solow_cobbDouglas_shares`).
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, §3.2, p. 78: with `0 < s`, `0 < δ < 1` and nonnegative growth rates `γ, n` of
technology and labour, the detrended model has EconomicGrowth's parameter conditions with gross
effective-labour growth `(1 + γ)(1 + n)`. -/
theorem solow_params_growth {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ)
    (hn : 0 ≤ n) : Params s δ ((1 + γ) * (1 + n)) :=
  ⟨hs, hδ1.le, by positivity, by nlinarith [mul_nonneg hγ hn]⟩

/-- AKMM, (3.7), p. 79: aggregate accumulation `K_{t+1} = (1 − δ)K_t + s F(K_t, A_t L_t)` with
`A_{t+1} = (1 + γ)A_t`, `L_{t+1} = (1 + n)L_t` and constant returns gives
`(1 + γ)(1 + n) k̃_{t+1} = (1 − δ)k̃_t + s f(k̃_t)` for `k̃_t = K_t/(A_t L_t)`; this is
EconomicGrowth's map (`capitalPerEffectiveWorker_succ`). -/
theorem eq_3_7 (hF : SolowAssumptions F) {s δ γ n : ℝ} {K A L : ℕ → ℝ} {t : ℕ}
    (hG : 0 < (1 + γ) * (1 + n)) (hA : A (t + 1) = (1 + γ) * A t)
    (hL : L (t + 1) = (1 + n) * L t) (hApos : 0 < A t) (hLpos : 0 < L t) (hK0 : 0 ≤ K t)
    (hK : K (t + 1) = (1 - δ) * K t + s * F (K t) (A t * L t)) :
    K (t + 1) / (A (t + 1) * L (t + 1)) =
        next (intensive F) s δ ((1 + γ) * (1 + n)) (K t / (A t * L t)) ∧
      (1 + γ) * (1 + n) * (K (t + 1) / (A (t + 1) * L (t + 1))) =
        (1 - δ) * (K t / (A t * L t)) + s * intensive F (K t / (A t * L t)) := by
  have hE : 0 < A t * L t := mul_pos hApos hLpos
  have h1 : K (t + 1) / (A (t + 1) * L (t + 1)) =
      next (intensive F) s δ ((1 + γ) * (1 + n)) (K t / (A t * L t)) :=
    capitalPerEffectiveWorker_succ (E := fun u => A u * L u)
      (Y := fun u => F (K u) (A u * L u)) hG hE (by rw [hK]; ring)
      (by rw [hA, hL]; ring) (solow_intensive_form hF hK0 hE)
  refine ⟨h1, ?_⟩
  rw [h1]
  unfold next
  set G := (1 + γ) * (1 + n)
  field_simp
  ring

/-- AKMM, p. 79: a constant path `k̃_t = k̃̄` solves (3.7) exactly when
`(1 + γ)(1 + n) k̃̄ = (1 − δ)k̃̄ + s f(k̃̄)`. -/
theorem solow_fixed_iff_growth {f : ℝ → ℝ} {s δ G k : ℝ} (hG : 0 < G) :
    next f s δ G k = k ↔ G * k = (1 - δ) * k + s * f k := by
  unfold next
  rw [div_eq_iff (ne_of_gt hG)]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 79: the balanced-growth value `k̃̄ > 0` with
`(1 + γ)(1 + n) k̃̄ = (1 − δ)k̃̄ + s f(k̃̄)` exists and is unique (EconomicGrowth's
`existsUnique_steadyState`). -/
theorem solow_bgp_existsUnique (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    ∃! k : ℝ, 0 < k ∧ (1 + γ) * (1 + n) * k = (1 - δ) * k + s * intensive F k := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  simpa only [solow_fixed_iff_growth P.growth_pos] using
    existsUnique_steadyState (solow_technology hF) P

/-- AKMM, (3.8), p. 79: with `f(k) = k^α`, `k̃̄ = (s/((1 + γ)(1 + n) + δ − 1))^{1/(1−α)}`
(EconomicGrowth's `CobbDouglas.steady_eq`). -/
theorem eq_3_8 {α s δ γ n : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)) =
      (s / ((1 + γ) * (1 + n) + δ - 1)) ^ (1 / (1 - α)) := by
  rw [CobbDouglas.steady_eq hα hα1 (solow_params_growth hs hδ hδ1 hγ hn),
    Solow1956.SolowSwan.CobbDouglas.steadyState, one_div]
  congr 2
  ring

/-- AKMM, p. 79: starting from any `k̃₀ > 0`, the path of (3.7) converges monotonically to `k̃̄`
(EconomicGrowth's `IsPath.orbit`). -/
theorem solow_detrended_convergence (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t)) :
    (∀ t, 0 < k t) ∧
      (k 0 < steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) → StrictMono k ∧
        ∀ t, k t < steady (solow_technology hF) s δ ((1 + γ) * (1 + n))) ∧
      (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) < k 0 → StrictAnti k ∧
        ∀ t, steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) < k t) ∧
      Tendsto k atTop (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have hp : IsPath (intensive F) s δ ((1 + γ) * (1 + n)) k := ⟨h0, fun t => by
    unfold next
    rw [eq_div_iff (ne_of_gt P.growth_pos), mul_comm, hk]
    ring⟩
  obtain ⟨h1, h2, h3, _, _, h6⟩ := hp.orbit (solow_technology hF) P
  exact ⟨h1, h2, h3, h6⟩

/-- AKMM, p. 79: "the rate of technological progress `γ` and the population growth rate `n`
work similarly to depreciation": faster growth of `A` or `L` lowers `k̃̄`
(EconomicGrowth's `steady_strictAnti_growth`). -/
theorem solow_bgp_strictAnti_growth (hF : SolowAssumptions F) {s δ G₁ G₂ : ℝ} (hs : 0 < s)
    (hm : 0 < G₁ - 1 + δ) (hG : G₁ < G₂) :
    steady (solow_technology hF) s δ G₂ < steady (solow_technology hF) s δ G₁ :=
  steady_strictAnti_growth (solow_technology hF) hs hm hG

/-- AKMM, pp. 79–80: untransforming, `Y_t/(A_t L_t) = f(k̃_t)`, income per capita
`y_t = Y_t/L_t = A_t f(k̃_t)` and `K_t/Y_t = k̃_t/f(k̃_t)`, where `Y_t = F(K_t, A_t L_t)`. -/
theorem solow_untransform (hF : SolowAssumptions F) {K A L : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hL : 0 < L) :
    F K (A * L) / (A * L) = intensive F (K / (A * L)) ∧
      F K (A * L) / L = A * intensive F (K / (A * L)) ∧
      K / F K (A * L) = K / (A * L) / intensive F (K / (A * L)) := by
  have hE : 0 < A * L := mul_pos hA hL
  have hf := solow_intensive_pos hF (div_pos hK hE)
  rw [solow_intensive_form hF hK.le hE]
  refine ⟨by field_simp, by field_simp, by field_simp⟩

/-- AKMM, pp. 79–80: from the aggregate equations and `K₀ > 0`, capital per efficiency unit,
output per efficiency unit and the capital–output ratio converge to their balanced-growth values
`k̃̄`, `f(k̃̄)` and `k̃̄/f(k̃̄)` ("the ratio `k_t/y_t` eventually stabilizes", p. 75). -/
theorem solow_aggregate_convergence (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {K A L : ℕ → ℝ}
    (hA : ∀ t, A (t + 1) = (1 + γ) * A t) (hL : ∀ t, L (t + 1) = (1 + n) * L t)
    (hApos : ∀ t, 0 < A t) (hLpos : ∀ t, 0 < L t) (hK0 : 0 < K 0)
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + s * F (K t) (A t * L t)) :
    Tendsto (fun t => K t / (A t * L t)) atTop
        (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) ∧
      Tendsto (fun t => F (K t) (A t * L t) / (A t * L t)) atTop
        (𝓝 (intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) ∧
      Tendsto (fun t => K t / F (K t) (A t * L t)) atTop
        (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) /
          intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have h := solow_technology hF
  have hpath : IsPath (intensive F) s δ ((1 + γ) * (1 + n)) (fun t => K t / (A t * L t)) := by
    refine ⟨div_pos hK0 (mul_pos (hApos 0) (hLpos 0)), fun t => ?_⟩
    have hpos : 0 < K t := by
      induction t with
      | zero => exact hK0
      | succ u ih =>
        rw [hK u]
        have := mul_pos hs (solow_intensive_form hF ih.le (mul_pos (hApos u) (hLpos u)) ▸
          mul_pos (mul_pos (hApos u) (hLpos u))
            (solow_intensive_pos hF (div_pos ih (mul_pos (hApos u) (hLpos u)))))
        have := mul_nonneg (sub_nonneg.mpr hδ1.le) ih.le
        linarith
    exact (eq_3_7 hF P.growth_pos (hA t) (hL t) (hApos t) (hLpos t) hpos.le (hK t)).1
  have hlim := hpath.tendsto h P
  have hks := (steady_spec h P).1
  have hpos : ∀ t, 0 < K t := fun t => by
    have := hpath.pos h P t
    exact (div_pos_iff_of_pos_right (mul_pos (hApos t) (hLpos t))).mp this
  have hy : Tendsto (fun t => intensive F (K t / (A t * L t))) atTop
      (𝓝 (intensive F (steady h s δ ((1 + γ) * (1 + n))))) :=
    (h.differentiable _ hks).continuousAt.tendsto.comp hlim
  have e1 : ∀ t, F (K t) (A t * L t) / (A t * L t) = intensive F (K t / (A t * L t)) :=
    fun t => (solow_untransform hF (hpos t) (hApos t) (hLpos t)).1
  have e2 : ∀ t, K t / F (K t) (A t * L t) =
      K t / (A t * L t) / intensive F (K t / (A t * L t)) :=
    fun t => (solow_untransform hF (hpos t) (hApos t) (hLpos t)).2.2
  refine ⟨hlim, ?_, ?_⟩
  · simp only [e1]
    exact hy
  · simp only [e2]
    exact hlim.div hy (ne_of_gt (h.output_pos hks))

/-- AKMM, p. 80: in the long run `y_t/A_t = f(k̃_t)` converges to `f(k̃̄)`, i.e. income per
capita approaches `f(k̃̄) A_t`. -/
theorem solow_income_long_run (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k y A : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t))
    (hApos : ∀ t, 0 < A t) (hy : ∀ t, y t = A t * intensive F (k t)) :
    Tendsto (fun t => y t / A t) atTop
      (𝓝 (intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) := by
  have hlim := (solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk).2.2.2
  have hks := (steady_spec (solow_technology hF) (solow_params_growth hs hδ hδ1 hγ hn)).1
  have e : ∀ t, y t / A t = intensive F (k t) := fun t => by
    rw [hy]; field_simp [ne_of_gt (hApos t)]
  simp only [e]
  exact ((solow_technology hF).differentiable _ hks).continuousAt.tendsto.comp hlim

/-- AKMM, p. 80: on the balanced growth path (`k̃_t = k̃̄` for all `t`) income per capita
`y_t = A_t f(k̃̄)` grows at the rate `γ` of technology, whatever `s`. -/
theorem solow_bgp_income_growth {f : ℝ → ℝ} {γ kbar : ℝ} {k y A : ℕ → ℝ} (hf : 0 < f kbar)
    (hApos : ∀ t, 0 < A t) (hA : ∀ t, A (t + 1) = (1 + γ) * A t) (hbgp : ∀ t, k t = kbar)
    (hy : ∀ t, y t = A t * f (k t)) (t : ℕ) :
    (y (t + 1) - y t) / y t = γ := by
  rw [hy, hy, hbgp, hbgp, hA]
  have := hApos t
  field_simp
  ring

/-- AKMM, p. 80: in general the growth rate of income per capita is
`(y_{t+1} − y_t)/y_t = (1 + γ) f(k̃_{t+1})/f(k̃_t) − 1`. -/
theorem solow_income_growth_identity {f : ℝ → ℝ} {γ : ℝ} {k y A : ℕ → ℝ} {t : ℕ}
    (hf : 0 < f (k t)) (hApos : 0 < A t) (hA : A (t + 1) = (1 + γ) * A t)
    (hy : ∀ t, y t = A t * f (k t)) :
    (y (t + 1) - y t) / y t = f (k (t + 1)) / f (k t) * (1 + γ) - 1 := by
  rw [hy, hy, hA]
  field_simp

/-- AKMM, p. 80: if `k̃₀ < k̃̄` income per capita grows faster than `γ` in every period ("a poor
country grows faster than at rate `γ`"); if `k̃₀ > k̃̄` it grows slower. -/
theorem solow_transition_growth (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k y A : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t))
    (hApos : ∀ t, 0 < A t) (hA : ∀ t, A (t + 1) = (1 + γ) * A t)
    (hy : ∀ t, y t = A t * intensive F (k t)) :
    (k 0 < steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) →
        ∀ t, γ < (y (t + 1) - y t) / y t) ∧
      (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) < k 0 →
        ∀ t, (y (t + 1) - y t) / y t < γ) := by
  obtain ⟨hpos, hlow, hhigh, _⟩ := solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk
  have hmono := solow_intensive_strictMono hF
  have hfpos : ∀ t, 0 < intensive F (k t) := fun t => solow_intensive_pos hF (hpos t)
  have hg : 0 < 1 + γ := by linarith
  refine ⟨fun hlt t => ?_, fun hgt t => ?_⟩
  · rw [solow_income_growth_identity (hfpos t) (hApos t) (hA t) hy]
    have h1 := hmono (Set.mem_Ici.mpr (hpos t).le) (Set.mem_Ici.mpr (hpos (t + 1)).le)
      ((hlow hlt).1 (Nat.lt_succ_self t))
    have h2 : 1 < intensive F (k (t + 1)) / intensive F (k t) := (one_lt_div (hfpos t)).mpr h1
    nlinarith
  · rw [solow_income_growth_identity (hfpos t) (hApos t) (hA t) hy]
    have h1 := hmono (Set.mem_Ici.mpr (hpos (t + 1)).le) (Set.mem_Ici.mpr (hpos t).le)
      ((hhigh hgt).1 (Nat.lt_succ_self t))
    have h2 : intensive F (k (t + 1)) / intensive F (k t) < 1 := (div_lt_one (hfpos t)).mpr h1
    nlinarith

/-- AKMM, p. 80: the growth rate of income per capita converges to `γ`; saving affects the
level, not the long-run growth rate. -/
theorem solow_income_growth_tendsto (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k y A : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t))
    (hApos : ∀ t, 0 < A t) (hA : ∀ t, A (t + 1) = (1 + γ) * A t)
    (hy : ∀ t, y t = A t * intensive F (k t)) :
    Tendsto (fun t => (y (t + 1) - y t) / y t) atTop (𝓝 γ) := by
  obtain ⟨hpos, _, _, hlim⟩ := solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk
  have hks := (steady_spec (solow_technology hF) (solow_params_growth hs hδ hδ1 hγ hn)).1
  have hc := ((solow_technology hF).differentiable _ hks).continuousAt.tendsto.comp hlim
  have hc1 := hc.comp (tendsto_add_atTop_nat 1)
  have hne := ne_of_gt ((solow_technology hF).output_pos hks)
  have e : ∀ t, (y (t + 1) - y t) / y t =
      intensive F (k (t + 1)) / intensive F (k t) * (1 + γ) - 1 := fun t =>
    solow_income_growth_identity (solow_intensive_pos hF (hpos t)) (hApos t) (hA t) hy
  simp only [e]
  have := ((hc1.div hc hne).mul_const (1 + γ)).sub_const 1
  rw [div_self hne, one_mul, add_sub_cancel_left] at this
  exact this

/-- AKMM, §3.3, p. 81: the competitive rental rate, the marginal product of capital
`r = F₁(K, AL)`, equals `f'(k̃)` with `k̃ = K/(AL)` (differentiate `F(K, E) = E f(K/E)` in `K`). -/
theorem solow_rental_rate (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    HasDerivAt (fun K' => F K' E) (deriv (intensive F) (K / E)) K := by
  have hf := (hF.differentiable 1 (K / E) one_pos (div_pos hK hE)).hasDerivAt
  have h2 := (hf.comp K ((hasDerivAt_id K).div_const E)).const_mul E
  have h3 : HasDerivAt (fun K' => E * intensive F (K' / E)) (deriv (intensive F) (K / E)) K := by
    convert h2 using 1
    · rfl
    change deriv (fun K => F K 1) (K / E) = _
    field_simp
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hK] with K' hK'
  exact solow_intensive_form hF (le_of_lt hK') hE

/-- AKMM, §3.3, p. 81: the wage per efficiency unit, the marginal product of effective labour
`w = F₂(K, AL)`, equals `f(k̃) − k̃ f'(k̃)` (EconomicGrowth's `wage`); differentiate
`F(K, E) = E f(K/E)` in `E`. -/
theorem solow_wage_rate (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    HasDerivAt (fun E' => F K E') (wage (intensive F) (K / E)) E := by
  have hf := (hF.differentiable 1 (K / E) one_pos (div_pos hK hE)).hasDerivAt
  have hq : HasDerivAt (fun y => K / y) (-(K / E ^ 2)) E := by
    have := (hasDerivAt_inv (ne_of_gt hE)).const_mul K
    convert this using 1
    · funext y; ring
    · ring
  have h2 := (hasDerivAt_id E).mul (hf.comp E hq)
  have h3 : HasDerivAt (fun E' => E' * intensive F (K / E')) (wage (intensive F) (K / E)) E := by
    convert h2 using 1
    · rfl
    unfold wage intensive
    simp only [id, Function.comp_apply]
    field_simp
    ring
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hE] with E' hE'
  exact solow_intensive_form hF hK.le hE'

/-- AKMM, §3.3 and footnote 5, p. 81: Euler's theorem for the degree-one homogeneous `F`,
`Y = K F₁(K, AL) + AL F₂(K, AL)`; output is exhausted by factor payments. -/
theorem solow_euler (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    F K E = K * deriv (fun K' => F K' E) K + E * deriv (fun E' => F K E') E := by
  rw [(solow_rental_rate hF hK hE).deriv, (solow_wage_rate hF hK hE).deriv,
    solow_intensive_form hF hK.le hE]
  unfold wage
  field_simp
  ring

/-- AKMM, §3.3, p. 81: the capital share is `rK/Y = k̃ f'(k̃)/f(k̃)`, the labour share is
`wAL/Y = 1 − rK/Y`, and `AL/Y = 1/f(k̃)`. -/
theorem solow_factor_shares (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    deriv (fun K' => F K' E) K * K / F K E =
        K / E * deriv (intensive F) (K / E) / intensive F (K / E) ∧
      deriv (fun E' => F K E') E * E / F K E =
        1 - deriv (fun K' => F K' E) K * K / F K E ∧
      E / F K E = 1 / intensive F (K / E) := by
  have hf := solow_intensive_pos hF (div_pos hK hE)
  have hY : 0 < F K E := by rw [solow_intensive_form hF hK.le hE]; positivity
  have heu := solow_euler hF hK hE
  rw [(solow_rental_rate hF hK hE).deriv] at heu ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [solow_intensive_form hF hK.le hE]; field_simp
  · rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (ne_of_gt hY)]
    linarith
  · rw [solow_intensive_form hF hK.le hE]; field_simp

/-- AKMM, §3.3, pp. 80–81: on the balanced growth path (`k̃_t = k̃̄`), the rental rate
`r_t = f'(k̃̄)`, the wage per efficiency unit `w_t`, the capital–output ratio and the capital share
are the same in every period. -/
theorem solow_factor_prices_bgp {f : ℝ → ℝ} {kbar : ℝ} {k : ℕ → ℝ} (hbgp : ∀ t, k t = kbar)
    (t : ℕ) :
    deriv f (k t) = deriv f kbar ∧ wage f (k t) = wage f kbar ∧ k t / f (k t) = kbar / f kbar ∧
      k t * deriv f (k t) / f (k t) = kbar * deriv f kbar / f kbar := by
  rw [hbgp t]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- AKMM, §3.3, p. 81: along every path of (3.7) the rental rate `f'(k̃_t)`, the wage
`f(k̃_t) − k̃_t f'(k̃_t)` and the capital share converge to their balanced-growth values. -/
theorem solow_factor_prices_tendsto (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t)) :
    Tendsto (fun t => deriv (intensive F) (k t)) atTop
        (𝓝 (deriv (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) ∧
      Tendsto (fun t => wage (intensive F) (k t)) atTop
        (𝓝 (wage (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) ∧
      Tendsto (fun t => k t * deriv (intensive F) (k t) / intensive F (k t)) atTop
        (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) *
          deriv (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))) /
            intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) := by
  have h := solow_technology hF
  obtain ⟨hpos, _, _, hlim⟩ := solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk
  have hks := (steady_spec h (solow_params_growth hs hδ hδ1 hγ hn)).1
  have hev : ∀ᶠ t in atTop, k t ∈ Set.Ioi (0 : ℝ) := Eventually.of_forall hpos
  have hr : Tendsto (fun t => deriv (intensive F) (k t)) atTop
      (𝓝 (deriv (intensive F) (steady h s δ ((1 + γ) * (1 + n))))) :=
    ((h.derivative_continuous _ hks).tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hev⟩)
  have hy := (h.differentiable _ hks).continuousAt.tendsto.comp hlim
  refine ⟨hr, ?_, ?_⟩
  · unfold wage
    exact hy.sub (hlim.mul hr)
  · exact (hlim.mul hr).div hy (ne_of_gt (h.output_pos hks))

/-- AKMM, §3.3, p. 81: for `F(K, AL) = K^α (AL)^{1−α}` the capital share is `α` and the labour
share is `1 − α` at every `(K, AL)`, on or off the balanced growth path. -/
theorem solow_cobbDouglas_shares {α K E : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hE : 0 < E) :
    deriv (fun K' => K' ^ α * E ^ (1 - α)) K * K / (K ^ α * E ^ (1 - α)) = α ∧
      deriv (fun E' => K ^ α * E' ^ (1 - α)) E * E / (K ^ α * E ^ (1 - α)) = 1 - α := by
  have hF := solow_cobbDouglas_assumptions hα hα1
  obtain ⟨h1, h2, _⟩ := solow_factor_shares hF hK hE
  have hk : 0 < K / E := div_pos hK hE
  have hd : deriv (intensive (fun K L => K ^ α * L ^ (1 - α))) (K / E) =
      α * (K / E) ^ (α - 1) := by
    rw [solow_intensive_cobbDouglas]
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))).deriv
  have hcap : deriv (fun K' => K' ^ α * E ^ (1 - α)) K * K / (K ^ α * E ^ (1 - α)) = α := by
    have := h1
    beta_reduce at this
    rw [this, hd, solow_intensive_cobbDouglas, Real.rpow_sub_one (ne_of_gt hk)]
    have : 0 < (K / E) ^ α := Real.rpow_pos_of_pos hk α
    field_simp
  refine ⟨hcap, ?_⟩
  have := h2
  beta_reduce at this
  rw [this, hcap]

end AKMM.Solow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The speed of convergence

AKMM, §3.4.1 and §3.4.3, pp. 82–88. The book's linearisations (3.10) and (3.12) are statements
about the derivative of the Solow map at its fixed point; they are proved as exact derivatives,
reusing EconomicGrowth's `next_hasDerivAt`, `slope_at_steady`, `contraction_steady` and
`cobbDouglas_contraction`.

* (3.10): the slope of (3.5) at `k̄` is `1 − δ + s f'(k̄) = 1 − λ`, `λ = δ − s f'(k̄) ∈ (0, 1)`
  (`eq_3_10`), and the relative-deviation form (`solow_linearised_relative`).
* Cobb–Douglas: slope `1 − δ(1 − α)` and (3.11) `λ = δ(1 − α)` (`eq_3_11`); `s` does not affect
  `λ` (`solow_speed_independent_of_saving`) because the two forces cancel exactly: `f'(k̄)` falls
  with `s` (`solow_marginal_product_falls_with_saving`) while `s f'(k̄) = αδ`
  (`solow_cobbDouglas_forces_offset`).
* (3.12) with growth: slope `(1 − δ + s f'(k̃̄))/((1 + γ)(1 + n))` (`eq_3_12`); Cobb–Douglas slope
  `α + (1 − α)(1 − δ)/((1 + γ)(1 + n))` and (3.13) `λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))`
  (`eq_3_13`).
* Local stability of the steady state from the slope (`solow_steady_locally_stable`,
  `solow_steady_locallyAttracting`).
* §3.4.3: on the balanced path `(1 + γ)(1 + n) = 1 − δ + I/K` (`solow_bgp_investment_rate`);
  doubling `s` multiplies balanced-growth output by `2^{α/(1−α)}`, which is `√2` at `α = 1/3`:
  a 41% rise, not the 17% printed on p. 88 (`solow_saving_output_ratio`,
  `solow_p88_doubling_saving`).
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, (3.10), p. 82: the derivative of `k ↦ (1 − δ)k + s f(k)` at the steady state is
`1 − δ + s f'(k̄) = 1 − λ` with the convergence speed `λ = δ − s f'(k̄)`, and `0 < λ < 1`
(EconomicGrowth's `next_hasDerivAt` and `slope_at_steady`). -/
theorem eq_3_10 (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) :
    HasDerivAt (fun k => (1 - δ) * k + s * intensive F k)
        (1 - δ + s * deriv (intensive F) (steady (solow_technology hF) s δ 1))
        (steady (solow_technology hF) s δ 1) ∧
      1 - δ + s * deriv (intensive F) (steady (solow_technology hF) s δ 1) =
        1 - (δ - s * deriv (intensive F) (steady (solow_technology hF) s δ 1)) ∧
      0 < δ - s * deriv (intensive F) (steady (solow_technology hF) s δ 1) ∧
      δ - s * deriv (intensive F) (steady (solow_technology hF) s δ 1) < 1 := by
  have P := solow_params_basic hs hδ hδ1
  have h := solow_technology hF
  have hk := (steady_spec h P).1
  have hd := next_hasDerivAt h s δ 1 hk
  have hsl := slope_at_steady h P
  rw [div_one] at hd hsl
  refine ⟨?_, by ring, by linarith [hsl.2], by linarith [hsl.1]⟩
  have e : next (intensive F) s δ 1 = fun k => (1 - δ) * k + s * intensive F k := by
    funext k; rw [next_acemoglu]; ring
  rw [e] at hd
  convert hd using 1
  ring

/-- AKMM, p. 82: the linearised law `Δk_{t+1} = (1 − λ)Δk_t`, `Δk_t = k_t − k̄`, in relative
deviations: `(k_{t+1} − k̄)/k̄ = (1 − λ)(k_t − k̄)/k̄`. -/
theorem solow_linearised_relative {kbar lam : ℝ} {k : ℕ → ℝ}
    (hlin : ∀ t, k (t + 1) - kbar = (1 - lam) * (k t - kbar)) (t : ℕ) :
    (k (t + 1) - kbar) / kbar = (1 - lam) * ((k t - kbar) / kbar) := by
  rw [hlin, mul_div_assoc]

/-- AKMM, p. 82 and (3.11), p. 82: with `f(k) = k^α` the slope of (3.5) at `k̄` is
`1 − δ(1 − α)`, so `λ = δ − s f'(k̄) = δ(1 − α)` (EconomicGrowth's `cobbDouglas_contraction`). -/
theorem eq_3_11 {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ + s * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s δ 1) =
        1 - δ * (1 - α) ∧
      δ - s * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s δ 1) =
        δ * (1 - α) := by
  have P := solow_params_basic hs hδ hδ1
  have h1 := contraction_steady (technology_rpow hα hα1) P
  rw [cobbDouglas_contraction hα hα1 P, div_one] at h1
  constructor <;> linarith

/-- AKMM, p. 83: in the Cobb–Douglas case `s` does not affect the convergence speed `λ`. -/
theorem solow_speed_independent_of_saving {α s₁ s₂ δ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hδ : 0 < δ) (hδ1 : δ < 1) :
    δ - s₁ * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s₁ δ 1) =
      δ - s₂ * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s₂ δ 1) := by
  rw [(eq_3_11 hα hα1 hs₁ hδ hδ1).2, (eq_3_11 hα hα1 hs₂ hδ hδ1).2]

/-- AKMM, p. 83 (the second of the two opposing forces): a higher saving rate raises `k̄` and so
lowers the marginal product `f'(k̄)` at the steady state. -/
theorem solow_marginal_product_falls_with_saving (hF : SolowAssumptions F) {s₁ s₂ δ : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ < s₂) (hδ : 0 < δ) :
    deriv (intensive F) (steady (solow_technology hF) s₂ δ 1) <
      deriv (intensive F) (steady (solow_technology hF) s₁ δ 1) := by
  have hm : (0 : ℝ) < 1 - 1 + δ := by linarith
  exact (solow_technology hF).marginal_strictAnti (steadyCapital_spec _ hs₁ hm).1
    (steadyCapital_spec _ (hs₁.trans hs) hm).1 (solow_steady_strictMono_saving hF hs₁ hs hδ).1

/-- AKMM, p. 83: "these two opposing forces exactly offset each other when the production
function is in the Cobb–Douglas form": `s f'(k̄) = αδ` at every saving rate. -/
theorem solow_cobbDouglas_forces_offset {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    s * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s δ 1) = α * δ := by
  have := (eq_3_11 hα hα1 hs hδ hδ1).2
  linarith

/-- AKMM, (3.12), p. 83: with growth, the derivative of the map of (3.7) at `k̃̄` is
`(1 − δ + s f'(k̃̄))/((1 + γ)(1 + n)) = 1 − λ` with
`λ = 1 − (1 − δ + s f'(k̃̄))/((1 + γ)(1 + n)) ∈ (0, 1)`. -/
theorem eq_3_12 (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    HasDerivAt (next (intensive F) s δ ((1 + γ) * (1 + n)))
        ((1 - δ + s * deriv (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))
          / ((1 + γ) * (1 + n)))
        (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))) ∧
      0 < 1 - (1 - δ + s * deriv (intensive F)
        (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) ∧
      1 - (1 - δ + s * deriv (intensive F)
        (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) < 1 := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have h := solow_technology hF
  have hd := next_hasDerivAt h s δ ((1 + γ) * (1 + n)) (steady_spec h P).1
  have hsl := slope_at_steady h P
  rw [add_comm (s * _)] at hd hsl
  exact ⟨hd, by linarith [hsl.2], by linarith [hsl.1]⟩

/-- AKMM, p. 83 and (3.13), p. 83: with `f(k) = k^α` the slope at `k̃̄` is
`α + (1 − α)(1 − δ)/((1 + γ)(1 + n))`, so
`λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))`, which does not involve `s` (p. 86). -/
theorem eq_3_13 {α s δ γ n : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    (1 - δ + s * deriv (fun k : ℝ => k ^ α)
        (steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) =
        α + (1 - α) * (1 - δ) / ((1 + γ) * (1 + n)) ∧
      1 - (1 - δ + s * deriv (fun k : ℝ => k ^ α)
        (steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) =
        (1 - α) * (1 - (1 - δ) / ((1 + γ) * (1 + n))) := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have h1 := contraction_steady (technology_rpow hα hα1) P
  rw [cobbDouglas_contraction hα hα1 P, add_comm (s * _)] at h1
  rw [← h1]
  have hG : (1 + γ) * (1 + n) ≠ 0 := ne_of_gt P.growth_pos
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- AKMM, §3.4.1 with footnote a of p. 78: the steady state of (3.5) is locally stable; paths
started within `ε` of `k̄` approach it at least geometrically, with ratio `ρ < 1`. -/
theorem solow_steady_locally_stable (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ ε > 0, ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x₀, |x₀ - steady (solow_technology hF) s δ 1| < ε →
      (∀ t, |(fun k => (1 - δ) * k + s * intensive F k)^[t] x₀ -
          steady (solow_technology hF) s δ 1| ≤ ρ ^ t * |x₀ - steady (solow_technology hF) s δ 1|) ∧
        Tendsto (fun t => (fun k => (1 - δ) * k + s * intensive F k)^[t] x₀) atTop
          (𝓝 (steady (solow_technology hF) s δ 1)) := by
  obtain ⟨hd, _, hl0, hl1⟩ := eq_3_10 hF hs hδ hδ1
  have hfix : (fun k => (1 - δ) * k + s * intensive F k) (steady (solow_technology hF) s δ 1) =
      steady (solow_technology hF) s δ 1 := by
    have := (solow_steady_spec hF hs hδ hδ1).2
    simp only
    linarith
  exact solow_local_stability hd hfix (by rw [abs_lt]; constructor <;> linarith)

/-- AKMM, §3.4.1 and pp. 76–77: the steady state of the basic model is locally attracting in the
sense used for poverty traps (`SolowLocallyAttracting`). -/
theorem solow_steady_locallyAttracting (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    SolowLocallyAttracting (fun k => (1 - δ) * k + s * intensive F k)
      (steady (solow_technology hF) s δ 1) := by
  obtain ⟨ε, hε, ρ, _, _, h⟩ := solow_steady_locally_stable hF hs hδ hδ1
  exact ⟨ε, hε, fun x₀ hx => (h x₀ hx).2⟩

/-- AKMM, §3.4.3, p. 87: on the balanced growth path (3.7) reads
`(1 + γ)(1 + n) = 1 − δ + I/K`, with `I/K = s f(k̃)/k̃`. -/
theorem solow_bgp_investment_rate {f : ℝ → ℝ} {s δ γ n k : ℝ} (hk : 0 < k)
    (hbgp : (1 + γ) * (1 + n) * k = (1 - δ) * k + s * f k) :
    (1 + γ) * (1 + n) = 1 - δ + s * f k / k := by
  field_simp
  linarith

/-- AKMM, §3.4.3, pp. 87–88: with `f(k) = k^α`, balanced-growth output per efficiency unit is
`f(k̃̄) = (s/((1 + γ)(1 + n) + δ − 1))^{α/(1−α)}`, so raising saving from `s₁` to `s₂` multiplies it
by `(s₂/s₁)^{α/(1−α)}`. -/
theorem solow_saving_output_ratio {α s₁ s₂ δ γ n : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs₁ : 0 < s₁)
    (hs₂ : 0 < s₂) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    steady (technology_rpow hα hα1) s₂ δ ((1 + γ) * (1 + n)) ^ α /
        steady (technology_rpow hα hα1) s₁ δ ((1 + γ) * (1 + n)) ^ α =
      (s₂ / s₁) ^ (α / (1 - α)) := by
  have hm : 0 < (1 + γ) * (1 + n) + δ - 1 := by
    have := (solow_params_growth hs₁ hδ hδ1 hγ hn).dilution_pos; linarith
  have hy : ∀ s, 0 < s → steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)) ^ α =
      (s / ((1 + γ) * (1 + n) + δ - 1)) ^ (α / (1 - α)) := by
    intro s hs
    rw [eq_3_8 hα hα1 hs hδ hδ1 hγ hn, ← Real.rpow_mul (div_pos hs hm).le]
    congr 1
    ring
  rw [hy s₁ hs₁, hy s₂ hs₂, ← Real.div_rpow (div_pos hs₂ hm).le (div_pos hs₁ hm).le]
  congr 1
  field_simp

/-- AKMM, §3.4.3, p. 88, corrected. With the calibrated `α = 1/3`, doubling the saving rate
(from 10% to 20%) multiplies balanced-growth output per efficiency unit by `2^{1/2} = √2 > 1.41`:
a 41% increase, not the printed 17% (`1.24/1.06`). The other calibrated parameters do not
matter. -/
theorem solow_p88_doubling_saving {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    steady (technology_rpow (α := 1 / 3) (by norm_num) (by norm_num)) (2 * s) δ
          ((1 + γ) * (1 + n)) ^ (1 / 3 : ℝ) /
        steady (technology_rpow (α := 1 / 3) (by norm_num) (by norm_num)) s δ
          ((1 + γ) * (1 + n)) ^ (1 / 3 : ℝ) = Real.sqrt 2 ∧
      (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 ≠ 1.24 / 1.06 := by
  have h := solow_saving_output_ratio (α := 1 / 3) (by norm_num) (by norm_num) hs
    (by positivity : 0 < 2 * s) hδ hδ1 hγ hn
  rw [show 2 * s / s = 2 by field_simp, show (1 / 3 : ℝ) / (1 - 1 / 3) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow] at h
  have hlt : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  refine ⟨h, hlt, ?_⟩
  intro heq
  rw [heq] at hlt
  norm_num at hlt

end AKMM.Solow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Business cycles in the Solow model: variants and impulse responses

AKMM, §3.5, pp. 88–92.

* **Variants** (§3.5.1): the RBC law of motion reduces to (3.5) with constant saving, labour and
  technology (`solow_rbc_reduces`); Harrod- and Hicks-neutral Cobb–Douglas technology coincide
  with `Ã = A^{1−α}` (`solow_harrod_hicks_cobbDouglas`); the investment-specific law
  `k_{t+1} = sν_t F(k_t, ℓ) + (1 − δ)k_t` from `y = c + i/ν` (`solow_investment_specific`); demand
  shocks: `c + i = c/(1 − s)`, the law of motion, and the unemployment rate is determined by
  `(c, k)` (`solow_demand_shock`, `solow_demand_unemployment_unique`).
* **Impulse responses** (§3.5.2): the steady state (3.17) with its Cobb–Douglas closed form
  (`eq_3_17`); the exact log form of (3.14) in deviations `k̂, Â` (`solow_irf_log_form`); the
  log-linear law (3.18) as the exact partial derivatives of that map at the steady state
  (`eq_3_18`); the closed-form solution of the linear recursion, as the book's sum and as a
  geometric expression (`solow_irf_capital_sum`, `solow_irf_capital_closed_form`); the output
  response, corrected (`solow_irf_output`) with a counterexample to the printed formula
  (`solow_irf_output_printed_false`); the level linearisation `g_k = 1 − δ(1 − α)`,
  `g_A = s^{1/(1−α)} δ^{−α/(1−α)} A^{α/(1−α)}` (`solow_level_linearisation`).

Only the linear recursion (3.18) is solved; "the log-linear approximation performs well" and the
figure's numbers are numerical claims and are not formalised.
-/

namespace AKMM.Solow

open Filter Topology

/-- AKMM, §3.5.1, p. 89: the RBC law of motion `k_{t+1} = (1 − δ)k_t + s(k_t, A_t) A_t F(k_t,
ℓ(k_t, A_t))` is the fundamental equation (3.5) when saving and labour are constant (`ℓ = 1`)
and `A_t = 1`. -/
theorem solow_rbc_reduces {F : ℝ → ℝ → ℝ} {δ s : ℝ} (sfun ℓfun : ℝ → ℝ → ℝ)
    (hs : ∀ k A, sfun k A = s) (hℓ : ∀ k A, ℓfun k A = 1) (k : ℝ) :
    (1 - δ) * k + sfun k 1 * 1 * F k (ℓfun k 1) = (1 - δ) * k + s * intensive F k := by
  rw [hs, hℓ, mul_one]
  rfl

/-- AKMM, p. 89: with Cobb–Douglas production the Harrod-neutral form `k^α (Aℓ)^{1−α}` equals the
Hicks-neutral form `Ã k^α ℓ^{1−α}` with `Ã = A^{1−α}`. -/
theorem solow_harrod_hicks_cobbDouglas {α A k ℓ : ℝ} (hA : 0 ≤ A) (hℓ : 0 ≤ ℓ) :
    k ^ α * (A * ℓ) ^ (1 - α) = A ^ (1 - α) * (k ^ α * ℓ ^ (1 - α)) := by
  rw [Real.mul_rpow hA hℓ]
  ring

/-- AKMM, §3.5.1, p. 89 (investment-specific technology): with `y = c + i/ν`, consumption
`c = (1 − s)y` and `k_{t+1} = i_t + (1 − δ)k_t`, the law of motion is
`k_{t+1} = sν_t F(k_t, ℓ) + (1 − δ)k_t`; with `ν = 1` it is (3.5). -/
theorem solow_investment_specific {F : ℝ → ℝ → ℝ} {s δ ℓ : ℝ} {k c i y ν : ℕ → ℝ} {t : ℕ}
    (hν : ν t ≠ 0) (hy : y t = F (k t) ℓ) (hres : y t = c t + i t / ν t)
    (hc : c t = (1 - s) * y t) (hk : k (t + 1) = i t + (1 - δ) * k t) :
    k (t + 1) = s * ν t * F (k t) ℓ + (1 - δ) * k t := by
  have hi : i t = s * ν t * y t := by
    have : i t / ν t = s * y t := by rw [hc] at hres; linarith
    field_simp at this
    linarith
  rw [hk, hi, hy]

/-- AKMM, §3.5.1, pp. 89–90 (demand shocks): if `i_t/c_t = s/(1 − s)` then total demand is
`c_t + i_t = c_t/(1 − s)`; when output is demand-determined, `y_t = c_t/(1 − s) =
F(k_t, ℓ(1 − u_t))`, and `k_{t+1} = i_t + (1 − δ)k_t` gives
`k_{t+1} = s F(k_t, ℓ(1 − u_t)) + (1 − δ)k_t`. -/
theorem solow_demand_shock {F : ℝ → ℝ → ℝ} {s δ ℓ : ℝ} {k c i u : ℕ → ℝ} {t : ℕ} (hs1 : s < 1)
    (hc : c t ≠ 0) (hic : i t / c t = s / (1 - s))
    (hy : c t / (1 - s) = F (k t) (ℓ * (1 - u t))) (hk : k (t + 1) = i t + (1 - δ) * k t) :
    c t + i t = c t / (1 - s) ∧ k (t + 1) = s * F (k t) (ℓ * (1 - u t)) + (1 - δ) * k t := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith)
  have hi : i t = s / (1 - s) * c t := by
    rw [div_eq_iff hc] at hic
    exact hic
  refine ⟨by rw [hi]; field_simp; ring, ?_⟩
  rw [hk, ← hy, hi]
  ring

/-- AKMM, p. 90: "`u_t` can be represented as a function of `c_t` and `k_t`": since `F` is
strictly increasing in labour, at most one unemployment rate `u < 1` clears
`c/(1 − s) = F(k, ℓ(1 − u))`. -/
theorem solow_demand_unemployment_unique {F : ℝ → ℝ → ℝ} (hF : SolowAssumptions F)
    {s ℓ c k u₁ u₂ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (hu₁ : u₁ < 1) (hu₂ : u₂ < 1)
    (h₁ : c / (1 - s) = F k (ℓ * (1 - u₁))) (h₂ : c / (1 - s) = F k (ℓ * (1 - u₂))) :
    u₁ = u₂ := by
  have hp₁ : ℓ * (1 - u₁) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (mul_pos hℓ (by linarith))
  have hp₂ : ℓ * (1 - u₂) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (mul_pos hℓ (by linarith))
  have := (hF.mono_labour k hk).injOn hp₁ hp₂ (h₁.symm.trans h₂)
  have := mul_left_cancel₀ (ne_of_gt hℓ) this
  linarith

/-- AKMM, (3.17), p. 92: the steady state of (3.14) at `A = Ā`, `k̄ = (sĀℓ^{1−α}/δ)^{1/(1−α)}`,
solves `k̄ = sĀk̄^α ℓ^{1−α} + (1 − δ)k̄`, i.e. `δk̄ = sĀk̄^α ℓ^{1−α}`. -/
theorem eq_3_17 {α s δ A ℓ : ℝ} (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ) (hA : 0 < A)
    (hℓ : 0 < ℓ) :
    δ * (s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α)) =
        s * A * ((s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α))) ^ α * ℓ ^ (1 - α) ∧
      (s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α)) =
        s * A * ((s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α))) ^ α * ℓ ^ (1 - α) +
          (1 - δ) * (s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α)) := by
  set b := s * A * ℓ ^ (1 - α) / δ with hb
  have hbpos : 0 < b := by positivity
  set k := b ^ (1 / (1 - α)) with hk
  have hkpos : 0 < k := Real.rpow_pos_of_pos hbpos _
  have h1α : (1 - α) ≠ 0 := ne_of_gt (by linarith)
  have hpow : k ^ (1 - α) = b := by
    rw [hk, ← Real.rpow_mul hbpos.le, one_div, inv_mul_cancel₀ h1α, Real.rpow_one]
  have hsplit : k = k ^ (1 - α) * k ^ α := by
    rw [← Real.rpow_add hkpos, sub_add_cancel, Real.rpow_one]
  have key : δ * k = s * A * k ^ α * ℓ ^ (1 - α) := by
    conv_lhs => rw [hsplit, hpow, hb]
    field_simp
  exact ⟨key, by linarith⟩

/-- AKMM, p. 92: writing `k_t = k̄ e^{k̂_t}` and `A_t = Ā e^{Â_t}` (3.15) and using
`δk̄ = sĀk̄^α ℓ^{1−α}` (3.17), the right side of (3.14) is exactly
`k̄ (δ e^{Â_t + αk̂_t} + (1 − δ) e^{k̂_t})`; so (3.14) is
`k̂_{t+1} = log(δ e^{Â_t + αk̂_t} + (1 − δ) e^{k̂_t})`. -/
theorem solow_irf_log_form {α s δ A ℓ kbar kh ah : ℝ} (hk : 0 < kbar)
    (hss : δ * kbar = s * A * kbar ^ α * ℓ ^ (1 - α)) :
    s * (A * Real.exp ah) * (kbar * Real.exp kh) ^ α * ℓ ^ (1 - α) +
        (1 - δ) * (kbar * Real.exp kh) =
      kbar * (δ * Real.exp (ah + α * kh) + (1 - δ) * Real.exp kh) := by
  rw [Real.mul_rpow hk.le (Real.exp_pos kh).le, ← Real.exp_mul, Real.exp_add]
  have : s * (A * Real.exp ah) * (kbar ^ α * Real.exp (kh * α)) * ℓ ^ (1 - α) =
      (s * A * kbar ^ α * ℓ ^ (1 - α)) * (Real.exp ah * Real.exp (kh * α)) := by ring
  rw [this, ← hss, mul_comm kh α]
  ring

/-- AKMM, (3.18), p. 92: the map `(k̂, Â) ↦ log(δ e^{Â + αk̂} + (1 − δ) e^{k̂})` of
`solow_irf_log_form` vanishes at the steady state and its partial derivatives there are
`1 − δ(1 − α)` in `k̂` and `δ` in `Â`; the first-order approximation is
`k̂_{t+1} = (1 − δ(1 − α))k̂_t + δÂ_t`. -/
theorem eq_3_18 {α δ : ℝ} :
    Real.log (δ * Real.exp (0 + α * 0) + (1 - δ) * Real.exp 0) = 0 ∧
      HasDerivAt (fun x => Real.log (δ * Real.exp (0 + α * x) + (1 - δ) * Real.exp x))
        (1 - δ * (1 - α)) 0 ∧
      HasDerivAt (fun a => Real.log (δ * Real.exp (a + α * 0) + (1 - δ) * Real.exp 0)) δ 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · have hin : HasDerivAt (fun x => δ * Real.exp (0 + α * x) + (1 - δ) * Real.exp x)
        (δ * (Real.exp (0 + α * 0) * (α * 1)) + (1 - δ) * Real.exp 0) 0 := by
      have h1 : HasDerivAt (fun x : ℝ => 0 + α * x) (α * 1) 0 :=
        ((hasDerivAt_id' 0).const_mul α).const_add 0
      exact (h1.exp.const_mul δ).add ((Real.hasDerivAt_exp 0).const_mul (1 - δ))
    have h := hin.log (by simp)
    convert h using 1
    simp
    ring
  · have hin : HasDerivAt (fun a => δ * Real.exp (a + α * 0) + (1 - δ) * Real.exp 0)
        (δ * (Real.exp (0 + α * 0) * 1)) 0 := by
      have h1 : HasDerivAt (fun a : ℝ => a + α * 0) 1 0 := (hasDerivAt_id' 0).add_const _
      exact (h1.exp.const_mul δ).add_const _
    have h := hin.log (by simp)
    convert h using 1
    simp

/-- AKMM, p. 92: the impulse response of (3.18) with `k̂₀ = 0`, `Â_t = ρ^t ε`:
`k̂_{t+1} = Σ_{τ=0}^{t} ρ^{t−τ}(1 − λ)^τ δε`. -/
theorem solow_irf_capital_sum {lam δ ρ ε : ℝ} {x : ℕ → ℝ} (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) (t : ℕ) :
    x (t + 1) = ∑ τ ∈ Finset.range (t + 1), ρ ^ (t - τ) * (1 - lam) ^ τ * (δ * ε) := by
  induction t with
  | zero => rw [hx, h0]; simp
  | succ u ih =>
    rw [hx, ih, Finset.sum_range_succ' _ (u + 1), Finset.mul_sum]
    simp only [Nat.sub_zero, pow_zero, mul_one, Nat.add_sub_add_right, pow_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro τ _
      ring
    · ring

/-- AKMM, p. 92: the closed form
`k̂_{t+1} = ρ^t (1 − ((1 − λ)/ρ)^{t+1})/(1 − (1 − λ)/ρ) · δε`, for `ρ ≠ 0` and `ρ ≠ 1 − λ`. -/
theorem solow_irf_capital_closed_form {lam δ ρ ε : ℝ} {x : ℕ → ℝ} (hρ : ρ ≠ 0)
    (hq : (1 - lam) / ρ ≠ 1) (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) (t : ℕ) :
    x (t + 1) = ρ ^ t * ((1 - ((1 - lam) / ρ) ^ (t + 1)) / (1 - (1 - lam) / ρ)) * (δ * ε) := by
  have hq' : 1 - (1 - lam) / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  set q := (1 - lam) / ρ with hqdef
  have hl : 1 - lam = q * ρ := by rw [hqdef]; field_simp
  induction t with
  | zero => rw [hx, h0]; field_simp; ring
  | succ u ih =>
    rw [hx, ih, hl]
    field_simp
    ring

/-- AKMM, p. 92, corrected: the output response `ŷ_t = Â_t + αk̂_t` is `ŷ₀ = ε` and, for
`t ≥ 1`, `ŷ_t = ρ^t ε (1 + (αδ/ρ)(1 − q^t)/(1 − q))` with `q = (1 − λ)/ρ`. The first term is
`ρ^t ε`, since `Â_t = ρ^t ε`. -/
theorem solow_irf_output {α lam δ ρ ε : ℝ} {x : ℕ → ℝ} (hρ : ρ ≠ 0)
    (hq : (1 - lam) / ρ ≠ 1) (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) (t : ℕ) :
    ρ ^ 0 * ε + α * x 0 = ε ∧
      ρ ^ (t + 1) * ε + α * x (t + 1) =
        ρ ^ (t + 1) * ε * (1 + α * δ / ρ * ((1 - ((1 - lam) / ρ) ^ (t + 1)) /
          (1 - (1 - lam) / ρ))) := by
  refine ⟨by rw [h0]; ring, ?_⟩
  rw [solow_irf_capital_closed_form hρ hq h0 hx t, pow_succ]
  field_simp

/-- AKMM, p. 92, the printed formula `ŷ_t = ρ^t (1 + (α/ρ)(1 − q^t)/(1 − q)) δε` is false: at
`t = 1` the true response is `ρε + αδε` and the printed one is `ρδε + αδε`; they differ whenever
`δ ≠ 1`, `ρ ≠ 0`, `ε ≠ 0`. -/
theorem solow_irf_output_printed_false {α lam δ ρ ε : ℝ} {x : ℕ → ℝ} (hρ : ρ ≠ 0) (hε : ε ≠ 0)
    (hδ1 : δ ≠ 1) (hq : (1 - lam) / ρ ≠ 1) (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) :
    ρ ^ 1 * ε + α * x 1 ≠
      ρ ^ 1 * (1 + α / ρ * ((1 - ((1 - lam) / ρ) ^ 1) / (1 - (1 - lam) / ρ))) * (δ * ε) := by
  have hq' : 1 - (1 - lam) / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hx1 : x 1 = δ * ε := by rw [hx 0, h0]; ring
  rw [hx1, pow_one, pow_one, div_self hq', mul_one]
  intro h
  field_simp at h
  have : ρ * (1 - δ) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hρ h1
  · exact hδ1 (by linarith)

/-- AKMM, p. 92: for `g(k, A) = (1 − δ)k + sA k^α` at the steady state
`k̄ = (sA/δ)^{1/(1−α)}`, the partial derivatives are `g_k = 1 − δ(1 − α)` and
`g_A = s^{1/(1−α)} δ^{−α/(1−α)} A^{α/(1−α)}`, so `Δk_{t+1} = g_k Δk_t + g_A ΔA_t`. -/
theorem solow_level_linearisation {α s δ A : ℝ} (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hA : 0 < A) :
    HasDerivAt (fun k => (1 - δ) * k + s * A * k ^ α) (1 - δ * (1 - α))
        ((s * A / δ) ^ (1 / (1 - α))) ∧
      HasDerivAt (fun a => (1 - δ) * (s * A / δ) ^ (1 / (1 - α)) +
          s * a * ((s * A / δ) ^ (1 / (1 - α))) ^ α)
        (s ^ (1 / (1 - α)) * δ ^ (-(α / (1 - α))) * A ^ (α / (1 - α))) A := by
  set k := (s * A / δ) ^ (1 / (1 - α)) with hk
  have hb : 0 < s * A / δ := by positivity
  have hkpos : 0 < k := Real.rpow_pos_of_pos hb _
  have h1α : (1 - α) ≠ 0 := ne_of_gt (by linarith)
  have hpow : k ^ (1 - α) = s * A / δ := by
    rw [hk, ← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ h1α, Real.rpow_one]
  have hsplit : k = k ^ (1 - α) * k ^ α := by
    rw [← Real.rpow_add hkpos, sub_add_cancel, Real.rpow_one]
  have hss : s * A * k ^ α = δ * k := by
    conv_rhs => rw [hsplit, hpow]
    field_simp
  refine ⟨?_, ?_⟩
  · have hd := ((hasDerivAt_id' k).const_mul (1 - δ)).add
      ((Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hkpos))).const_mul (s * A))
    convert hd using 1
    rw [Real.rpow_sub_one (ne_of_gt hkpos)]
    have : s * A * (α * (k ^ α / k)) = α * (s * A * k ^ α) / k := by ring
    rw [this, hss]
    field_simp
    ring
  · have hd := ((hasDerivAt_id' A).const_mul s).mul_const (k ^ α) |>.const_add ((1 - δ) * k)
    convert hd using 1
    rw [mul_one, hk, ← Real.rpow_mul hb.le, Real.div_rpow (by positivity) hδ.le,
      Real.mul_rpow hs.le hA.le, Real.rpow_neg hδ.le]
    have hs' : s ^ (1 / (1 - α)) = s * s ^ (α / (1 - α)) := by
      rw [show (1 / (1 - α)) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hs,
        Real.rpow_one]
    rw [hs', show 1 / (1 - α) * α = α / (1 - α) by ring]
    field_simp

end AKMM.Solow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Uzawa's theorem in discrete time

AKMM, Appendix 3.A, pp. 825–826 (cited on p. 78): a discrete-time version of Uzawa (1961)
following Schlicht (2006). EconomicGrowth's `UzawaModern` formalises the continuous-time
Jones–Scrimgeour/Schlicht argument with exponential paths; the book's statements are in discrete
time and are proved here, reusing `UzawaModern.Uzawa.rate_eq_of_weighted_moments` (the
weighted-moment identity that identifies growth factors) for the variant with nonnegative
consumption.

* **Theorem .1** (Part I): if every balanced path of the reference technology `F̃₀` is consistent
  with `F̃_t`, then `F̃_t(K, L) = F̃₀(K, A_t L)` with `A_t = ((1 + γ)/(1 + n))^t` (`theorem_3A_1`).
  `A_t` grows at `(1 + γ)/(1 + n) − 1` (`uzawa_technology_growth`), and the labour-augmenting
  factor is unique when `F̃₀` is increasing in labour (`uzawa_technology_unique`).
* **Theorem .2** (Part II): with `K_{t+1} − K_t = I_t − δK_t` (3.A.2), `Y_t = C_t + I_t` (3.A.3),
  constant growth rates and `I_t > 0`, `γ_Y = γ_K` (`theorem_3A_2`). The proof's steps:
  `γ_K = I_t/K_t − δ` (`uzawa_capital_growth`), `γ_I = γ_K` (`uzawa_investment_growth`), and
  (3.A.4) (`eq_3A_4`). Variants: nonnegative consumption, via `UzawaModern`
  (`uzawa_part2_nonneg_consumption`); the constant-saving Solow case (`uzawa_part2_solow`).

**Departures.** (i) Theorem .1 says `A_t` grows at `(1 + γ)(1 + n) − 1`; its own proof gives
`A_t = ((1 + γ)/(1 + n))^t`, a rate of `(1 + γ)/(1 + n) − 1`. The printed rate is false
(`uzawa_printed_rate_counterexample`, with `γ = 0`, `n = 1`). (ii) The proof of Theorem .2 writes
`1 + γ_K = I_t/K_t − δ`; the correct identity is `γ_K = I_t/K_t − δ`
(`uzawa_capital_growth`). (iii) Theorem .2 needs output to be nonzero (so that `γ_Y` is defined
as a ratio); we assume `Y₀ ≠ 0`, and with `Y ≡ 0` the conclusion fails
(`uzawa_part2_zero_output_counterexample`).
-/

namespace AKMM.Solow

/-- **Theorem .1** (Uzawa Theorem, Part I; AKMM, Appendix 3.A, p. 825). Let `F̃₀` have constant
returns on the positive orthant and suppose that for all `Y, K, L > 0` with `Y = F̃₀(K, L)` the
balanced path `Y(1 + γ)^t = F̃_t(K(1 + γ)^t, L(1 + n)^t)` is consistent with `F̃_t` at every `t`.
Then `F̃_t(K_t, L_t) = F̃₀(K_t, A_t L_t)` for all `K_t, L_t > 0`, with `A_t = ((1 + γ)/(1 + n))^t`:
technical progress is labour-augmenting and `F = F̃₀`. -/
theorem theorem_3A_1 {Ft : ℕ → ℝ → ℝ → ℝ} {γ n : ℝ} (hγ : 0 < 1 + γ) (hn : 0 < 1 + n)
    (hcrs : ∀ c K L, 0 < c → 0 < K → 0 < L → Ft 0 (c * K) (c * L) = c * Ft 0 K L)
    (hbg : ∀ Y K L, 0 < K → 0 < L → Y = Ft 0 K L →
      ∀ t : ℕ, Y * (1 + γ) ^ t = Ft t (K * (1 + γ) ^ t) (L * (1 + n) ^ t))
    (t : ℕ) {Kt Lt : ℝ} (hK : 0 < Kt) (hL : 0 < Lt) :
    Ft t Kt Lt = Ft 0 Kt (((1 + γ) / (1 + n)) ^ t * Lt) := by
  have hg : 0 < (1 + γ) ^ t := pow_pos hγ t
  have hnt : 0 < (1 + n) ^ t := pow_pos hn t
  have h := hbg (Ft 0 (Kt / (1 + γ) ^ t) (Lt / (1 + n) ^ t)) (Kt / (1 + γ) ^ t)
    (Lt / (1 + n) ^ t) (div_pos hK hg) (div_pos hL hnt) rfl t
  rw [div_mul_cancel₀ Kt (ne_of_gt hg), div_mul_cancel₀ Lt (ne_of_gt hnt)] at h
  rw [← h, mul_comm, ← hcrs _ _ _ hg (div_pos hK hg) (div_pos hL hnt),
    mul_div_cancel₀ Kt (ne_of_gt hg), div_pow]
  congr 1
  field_simp

/-- AKMM, Appendix 3.A, p. 826, corrected: the labour-augmenting factor of Theorem .1,
`A_t = ((1 + γ)/(1 + n))^t`, has `A₀ = 1` and grows at the constant rate `(1 + γ)/(1 + n) − 1`. -/
theorem uzawa_technology_growth {γ n : ℝ} (t : ℕ) :
    ((1 + γ) / (1 + n)) ^ 0 = 1 ∧
      ((1 + γ) / (1 + n)) ^ (t + 1) = (1 + ((1 + γ) / (1 + n) - 1)) * ((1 + γ) / (1 + n)) ^ t :=
  ⟨pow_zero _, by rw [pow_succ]; ring⟩

/-- AKMM, Appendix 3.A, p. 826 ("`F(K_t, A_t L_t)` completely characterizes `F̃_t`"): if `F̃₀` is
strictly increasing in labour, the labour-augmenting factor in a representation
`F̃_t(K, L) = F̃₀(K, B L)` is unique. -/
theorem uzawa_technology_unique {F0 : ℝ → ℝ → ℝ} {K L A B : ℝ}
    (hmono : StrictMonoOn (F0 K) (Set.Ioi 0)) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (h : F0 K (A * L) = F0 K (B * L)) : A = B := by
  have := hmono.injOn (Set.mem_Ioi.mpr (mul_pos hA hL)) (Set.mem_Ioi.mpr (mul_pos hB hL)) h
  exact mul_right_cancel₀ (ne_of_gt hL) this

/-- AKMM, Appendix 3.A, Theorem .1 as printed ("`A_t` grows at a constant rate
`(1 + γ)(1 + n) − 1`") is false. With `γ = 0`, `n = 1` and `F̃_t(K, L) = K + (1/2)^t L`, the
hypotheses of Theorem .1 hold (`F̃₀ = K + L` has constant returns), but `F̃₁(K, L) ≠ F̃₀(K, 2L)`:
the factor at `t = 1` is `1/2 = (1 + γ)/(1 + n)`, not `2 = (1 + γ)(1 + n)`. -/
theorem uzawa_printed_rate_counterexample :
    ∃ Ft : ℕ → ℝ → ℝ → ℝ,
      (∀ c K L, 0 < c → 0 < K → 0 < L → Ft 0 (c * K) (c * L) = c * Ft 0 K L) ∧
      (∀ Y K L, 0 < K → 0 < L → Y = Ft 0 K L →
        ∀ t : ℕ, Y * (1 + 0) ^ t = Ft t (K * (1 + 0) ^ t) (L * (1 + 1) ^ t)) ∧
      ¬ (∀ K L, 0 < K → 0 < L → Ft 1 K L = Ft 0 K (((1 + 0) * (1 + 1)) ^ 1 * L)) := by
  refine ⟨fun t K L => K + (1 / 2 : ℝ) ^ t * L, fun c K L _ _ _ => by ring,
    fun Y K L _ _ hY t => ?_, fun h => ?_⟩
  · rw [hY]
    have : (1 / 2 : ℝ) ^ t * (L * (1 + 1) ^ t) = L * ((1 / 2) * 2) ^ t := by rw [mul_pow]; ring
    simp only
    rw [this]
    norm_num
  · have := h 1 1 one_pos one_pos
    norm_num at this

/-- AKMM, Appendix 3.A, proof of Theorem .2, corrected: from (3.A.2) and constant capital
growth `K_{t+1} = (1 + γ_K)K_t` with `I_t > 0`, capital is never zero and
`γ_K = I_t/K_t − δ` (printed as `1 + γ_K = I_t/K_t − δ`). -/
theorem uzawa_capital_growth {K I : ℕ → ℝ} {δ γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) (t : ℕ) : K t ≠ 0 ∧ γK = I t / K t - δ := by
  have hK : K t ≠ 0 := by
    intro h0
    have := hacc t
    rw [hgK, h0] at this
    linarith [hI t]
  refine ⟨hK, ?_⟩
  have := hacc t
  rw [hgK] at this
  field_simp
  linarith

/-- AKMM, Appendix 3.A, proof of Theorem .2: `I_t/K_t` is constant, so `γ_I = γ_K`. -/
theorem uzawa_investment_growth {K I : ℕ → ℝ} {δ γK γI : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (hI : ∀ t, 0 < I t) : γI = γK := by
  have hlev : ∀ t, I t = (γK + δ) * K t := fun t => by
    have := hacc t; rw [hgK] at this; linarith
  have h1 : I 1 = (1 + γK) * I 0 := by rw [hlev 1, hlev 0, hgK 0]; ring
  rw [hgI 0] at h1
  have := mul_right_cancel₀ (ne_of_gt (hI 0)) h1
  linarith

/-- AKMM, (3.A.4), p. 826: subtracting (3.A.3) at `t` from `t + 1` with constant growth rates
gives `γ_C C_t + γ_I I_t = γ_Y Y_t` and `(γ_C − γ_Y)C_t = (γ_Y − γ_I)I_t`. -/
theorem eq_3A_4 {Y C I : ℕ → ℝ} {γY γC γI : ℝ} (hres : ∀ t, Y t = C t + I t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgC : ∀ t, C (t + 1) = (1 + γC) * C t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (t : ℕ) :
    γC * C t + γI * I t = γY * Y t ∧ (γC - γY) * C t = (γY - γI) * I t := by
  have h1 := hres (t + 1)
  rw [hgY, hgC, hgI, hres t] at h1
  have h2 : γC * C t + γI * I t = γY * Y t := by rw [hres t]; linarith
  refine ⟨h2, ?_⟩
  rw [hres t] at h2
  linarith

/-- **Theorem .2** (Uzawa Theorem, Part II; AKMM, Appendix 3.A, p. 826). Under (3.A.2) and
(3.A.3), on a path with `I_t > 0` along which `Y_t, C_t, I_t, K_t` grow at constant rates
`γ_Y, γ_C, γ_I, γ_K`, output and capital grow at the same rate: `γ_Y = γ_K` (and `γ_I = γ_K`).
Output is assumed nonzero (`Y₀ ≠ 0`), as the definition of `γ_Y` as a ratio requires. -/
theorem theorem_3A_2 {Y C I K : ℕ → ℝ} {δ γY γC γI γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hres : ∀ t, Y t = C t + I t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgC : ∀ t, C (t + 1) = (1 + γC) * C t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) (hY : Y 0 ≠ 0) : γY = γK ∧ γI = γK := by
  have hIK := uzawa_investment_growth hacc hgK hgI hI
  refine ⟨?_, hIK⟩
  rw [← hIK]
  by_contra hne
  have E0 := (eq_3A_4 hres hgY hgC hgI 0).2
  have E1 := (eq_3A_4 hres hgY hgC hgI 1).2
  rw [hgC 0, hgI 0] at E1
  -- `(γ_Y − γ_I) I₀ ≠ 0`, so `(γ_C − γ_Y) C₀ ≠ 0`
  have hR : (γY - γI) * I 0 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne) (ne_of_gt (hI 0))
  have hL : (γC - γY) * C 0 ≠ 0 := E0 ▸ hR
  -- comparing `t = 0` and `t = 1`: `γ_C = γ_I`, i.e. `I_t/C_t` constant
  have hCI : γC = γI := by
    have : (γC - γY) * C 0 * (1 + γC) = (γC - γY) * C 0 * (1 + γI) := by
      calc (γC - γY) * C 0 * (1 + γC) = (γY - γI) * ((1 + γI) * I 0) := by rw [← E1]; ring
        _ = (γY - γI) * I 0 * (1 + γI) := by ring
        _ = (γC - γY) * C 0 * (1 + γI) := by rw [E0]
    have := mul_left_cancel₀ hL this
    linarith
  -- then `(γ_I − γ_Y) Y₀ = 0`, contradicting `Y₀ ≠ 0`
  rw [hCI] at E0
  have : (γI - γY) * Y 0 = 0 := by rw [hres 0]; linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hne (by linarith)
  · exact hY h

/-- AKMM, Appendix 3.A, Theorem .2 with nonnegative consumption (the Jones–Scrimgeour setting):
then no assumption on output is needed, and `γ_Y = γ_I` follows from `UzawaModern`'s
weighted-moment identity `rate_eq_of_weighted_moments` applied to the growth factors. -/
theorem uzawa_part2_nonneg_consumption {Y C I K : ℕ → ℝ} {δ γY γC γI γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hres : ∀ t, Y t = C t + I t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgC : ∀ t, C (t + 1) = (1 + γC) * C t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) (hC : 0 ≤ C 0) : γY = γK := by
  have hIK := uzawa_investment_growth hacc hgK hgI hI
  have h1 := hres 1
  rw [hgY, hgC, hgI] at h1
  have h2 := hres 2
  rw [hgY, hgY, hgC, hgC, hgI, hgI] at h2
  have := UzawaModern.Uzawa.rate_eq_of_weighted_moments hC (hI 0) (hres 0)
    (by rw [mul_comm]; linarith : Y 0 * (1 + γY) = C 0 * (1 + γC) + I 0 * (1 + γI))
    (by nlinarith : Y 0 * (1 + γY) ^ 2 = C 0 * (1 + γC) ^ 2 + I 0 * (1 + γI) ^ 2)
  linarith

/-- AKMM, Appendix 3.A, closing remark: in the Solow model `I_t = sY_t`, so
`γ_I = γ_Y` directly and `γ_Y = γ_K`. -/
theorem uzawa_part2_solow {Y I K : ℕ → ℝ} {s δ γY γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hsave : ∀ t, I t = s * Y t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) : γY = γK :=
  uzawa_investment_growth hacc hgK (fun t => by rw [hsave, hsave, hgY]; ring) hI

/-- AKMM, Appendix 3.A, Theorem .2 needs `Y ≠ 0`: with `Y_t = 0`, `C_t = −(3/2)2^t`,
`I_t = (3/2)2^t`, `K_t = 2^t` and `δ = 1/2`, (3.A.2), (3.A.3) and the constant-growth conditions
hold with `γ_Y = 0`, `γ_C = γ_I = γ_K = 1` and `I_t > 0`, yet `γ_Y ≠ γ_K`. -/
theorem uzawa_part2_zero_output_counterexample :
    ∃ (Y C I K : ℕ → ℝ) (δ γY γC γI γK : ℝ),
      (∀ t, K (t + 1) - K t = I t - δ * K t) ∧ (∀ t, Y t = C t + I t) ∧
      (∀ t, Y (t + 1) = (1 + γY) * Y t) ∧ (∀ t, C (t + 1) = (1 + γC) * C t) ∧
      (∀ t, I (t + 1) = (1 + γI) * I t) ∧ (∀ t, K (t + 1) = (1 + γK) * K t) ∧
      (∀ t, 0 < I t) ∧ Y 0 = 0 ∧ γY ≠ γK := by
  refine ⟨fun _ => 0, fun t => -(3 / 2 * 2 ^ t), fun t => 3 / 2 * 2 ^ t, fun t => 2 ^ t,
    1 / 2, 0, 1, 1, 1, fun t => ?_, fun t => by ring, fun t => by ring, fun t => ?_,
    fun t => ?_, fun t => ?_, fun t => by positivity, rfl, by norm_num⟩ <;>
  · simp only
    rw [pow_succ]
    ring

end AKMM.Solow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Figure claims: poverty traps (Fig. 3.3) and the speed of convergence (Fig. 3.5)

AKMM, §3.1.1, "Poverty traps", pp. 76–77 (Figure 3.3), and §3.4.1, p. 82 (Figure 3.5).

* **Poverty traps** (p. 77, Fig. 3.3). The figure's picture is captured by
  `SolowThreeCrossings`: `f` continuous and nondecreasing on `k > 0` (Assumption 1 weakened to
  weak monotonicity; no concavity, convexity or differentiability), `0 < δ < 1`, and the curve
  `(1 − δ)k + s f(k)` crossing the 45-degree line at `0 < k̄₁ < k̄₂ < k̄₃` with the figure's sign
  pattern (above, below, above, below). Then the basins are global: every path from
  `k₀ ∈ (0, k̄₂)` converges to `k̄₁`, from `k₀ > k̄₂` to `k̄₃`, and `k̄₂` is a rest point
  (`solow_poverty_trap_basins`); so `k̄₁`, `k̄₃` are locally attracting and `k̄₂` is not, and a
  small perturbation from `k̄₂` moves the path further away (`solow_poverty_trap_stability`).
* **Raising saving** (p. 77). If `f(k) ≥ m k` near `0` (as in the figure, where `f(0) > 0`) and
  `f(k)/k` falls strictly to zero beyond some `k̂`, then any saving rate `s' > δ/m` leaves exactly
  one positive steady state and every path converges to it (`solow_poverty_trap_saving_rise`);
  if `s' > s` it lies above `k̄₃`, and `k̄₁`, `k̄₂` disappear
  (`solow_poverty_trap_saving_rise_removes`). A temporary rise to `s'` for long enough, followed
  by a return to `s`, takes every economy to `k̄₃` (`solow_poverty_trap_temporary_saving`).
* A concrete technology `f(k) = max(1, min(2k − 2, 3))` with `s = δ = 1/10` has steady states
  `1, 2, 3` and satisfies every hypothesis (`solow_poverty_trap_example`); with `s' = 1/2` its
  unique steady state is `15` (`solow_poverty_trap_example_dynamics`).
* **Speed of convergence** (p. 82, Fig. 3.5). In the book's approximation the (relative) gap to
  the steady state obeys `x_{t+1} = (1 − λ)x_t`, so `x_t = (1 − λ)^t x_0`
  (`solow_linearised_gap_closed_form`). For `λ₁ < λ₂ ≤ 1` and the same initial gap, the gap
  under `λ₂` is smaller in absolute value at every date, strictly from date 1 on, both paths stay
  on the side they start (the figure's staircase from `k₀ < k̄`), and the faster path enters every
  band `|x| ≤ ε` no later (`solow_faster_convergence`): a higher `λ` means fewer steps, not "more
  steps" as printed. By (3.11) and (3.13) `λ` falls with `α` and rises with `δ`
  (`solow_speed_parameters`).
-/

namespace AKMM.Solow

open Filter Topology

/-- AKMM, p. 77, Figure 3.3 (the picture's hypotheses). `f` is continuous and nondecreasing on
`k > 0`, `0 < s`, `0 < δ < 1`, and the right side of (3.5), `(1 − δ)k + s f(k)`, crosses the
45-degree line exactly at `0 < k̄₁ < k̄₂ < k̄₃`: above it on `(0, k̄₁)` and `(k̄₂, k̄₃)`, below it
on `(k̄₁, k̄₂)` and beyond `k̄₃`. In the form `s f(k)` against `δ k`. -/
structure SolowThreeCrossings (f : ℝ → ℝ) (s δ k₁ k₂ k₃ : ℝ) : Prop where
  saving_pos : 0 < s
  depreciation_pos : 0 < δ
  depreciation_lt_one : δ < 1
  cont : ContinuousOn f (Set.Ioi 0)
  mono : MonotoneOn f (Set.Ioi 0)
  pos₁ : 0 < k₁
  lt₁₂ : k₁ < k₂
  lt₂₃ : k₂ < k₃
  fix₁ : δ * k₁ = s * f k₁
  fix₂ : δ * k₂ = s * f k₂
  fix₃ : δ * k₃ = s * f k₃
  above₁ : ∀ k, 0 < k → k < k₁ → δ * k < s * f k
  below₂ : ∀ k, k₁ < k → k < k₂ → s * f k < δ * k
  above₃ : ∀ k, k₂ < k → k < k₃ → δ * k < s * f k
  below₄ : ∀ k, k₃ < k → s * f k < δ * k

/-- AKMM, p. 77 (poverty traps, the rising branch of Fig. 3.3): for a continuous nondecreasing
map `g` on `k > 0` with `g(b) = b` and `g` above the diagonal on `(a, b)`, `a ≥ 0`, every path
from `x₀ ∈ (a, b]` rises monotonically to `b`. -/
theorem solow_ptrap_rise {g : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} (ha : 0 ≤ a)
    (hmono : MonotoneOn g (Set.Ioi 0)) (hc : ContinuousOn g (Set.Ioi 0)) (hfix : g b = b)
    (hup : ∀ y, a < y → y < b → y < g y) (h0 : a < x 0) (h0b : x 0 ≤ b)
    (hsucc : ∀ t, x (t + 1) = g (x t)) :
    Monotone x ∧ (∀ t, x 0 ≤ x t ∧ x t ≤ b) ∧ Tendsto x atTop (𝓝 b) := by
  have hb : 0 < b := by linarith
  have hinv : ∀ t, x 0 ≤ x t ∧ x t ≤ b := by
    intro t
    induction t with
    | zero => exact ⟨le_rfl, h0b⟩
    | succ u ih =>
      rw [hsucc u]
      have hpos : 0 < x u := by linarith [ih.1]
      refine ⟨?_, ?_⟩
      · rcases ih.2.lt_or_eq with hl | he
        · exact ih.1.trans (hup _ (by linarith [ih.1]) hl).le
        · rw [he, hfix]; exact h0b
      · rw [← hfix]; exact hmono (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hb) ih.2
  have hstep : ∀ t, x t ≤ x (t + 1) := by
    intro t
    rw [hsucc t]
    rcases (hinv t).2.lt_or_eq with hl | he
    · exact (hup _ (by linarith [(hinv t).1]) hl).le
    · rw [he, hfix]
  have hmon : Monotone x := monotone_nat_of_le_succ hstep
  have hbdd : BddAbove (Set.range x) := ⟨b, by rintro _ ⟨t, rfl⟩; exact (hinv t).2⟩
  have hlim := tendsto_atTop_ciSup hmon hbdd
  have hL0 : x 0 ≤ ⨆ t, x t := le_ciSup hbdd 0
  have hLb : ⨆ t, x t ≤ b := ciSup_le fun t => (hinv t).2
  have hLpos : 0 < ⨆ t, x t := by linarith
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (⨆ t, x t)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g (⨆ t, x t))) := by
    simp only [hsucc]
    exact ((hc.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hlim
  have hgL : g (⨆ t, x t) = ⨆ t, x t := tendsto_nhds_unique h2 h1
  have hLeq : (⨆ t, x t) = b := by
    rcases hLb.lt_or_eq with hl | he
    · exact absurd hgL (ne_of_gt (hup _ (by linarith) hl))
    · exact he
  exact ⟨hmon, hinv, hLeq ▸ hlim⟩

/-- AKMM, p. 77 (poverty traps, the falling branch of Fig. 3.3): for a continuous nondecreasing
map `g` on `k > 0` with `g(b) = b`, `b > 0`, and `g` below the diagonal on `(b, c)`, every path
from `x₀ ∈ [b, c)` falls monotonically to `b`. -/
theorem solow_ptrap_fall {g : ℝ → ℝ} {b c : ℝ} {x : ℕ → ℝ} (hb : 0 < b)
    (hmono : MonotoneOn g (Set.Ioi 0)) (hc : ContinuousOn g (Set.Ioi 0)) (hfix : g b = b)
    (hdown : ∀ y, b < y → y < c → g y < y) (h0 : b ≤ x 0) (h0c : x 0 < c)
    (hsucc : ∀ t, x (t + 1) = g (x t)) :
    Antitone x ∧ (∀ t, b ≤ x t ∧ x t ≤ x 0) ∧ Tendsto x atTop (𝓝 b) := by
  have hinv : ∀ t, b ≤ x t ∧ x t ≤ x 0 := by
    intro t
    induction t with
    | zero => exact ⟨h0, le_rfl⟩
    | succ u ih =>
      rw [hsucc u]
      refine ⟨?_, ?_⟩
      · rw [← hfix]
        exact hmono (Set.mem_Ioi.mpr hb) (Set.mem_Ioi.mpr (by linarith [ih.1])) ih.1
      · rcases ih.1.lt_or_eq with hl | he
        · exact (hdown _ hl (by linarith [ih.2])).le.trans ih.2
        · rw [← he, hfix]; exact h0
  have hstep : ∀ t, x (t + 1) ≤ x t := by
    intro t
    rw [hsucc t]
    rcases (hinv t).1.lt_or_eq with hl | he
    · exact (hdown _ hl (by linarith [(hinv t).2])).le
    · rw [← he, hfix]
  have hanti : Antitone x := antitone_nat_of_succ_le hstep
  have hbdd : BddBelow (Set.range x) := ⟨b, by rintro _ ⟨t, rfl⟩; exact (hinv t).1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hLb : b ≤ ⨅ t, x t := le_ciInf fun t => (hinv t).1
  have hLx : ⨅ t, x t ≤ x 0 := ciInf_le hbdd 0
  have hLpos : 0 < ⨅ t, x t := by linarith
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (⨅ t, x t)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g (⨅ t, x t))) := by
    simp only [hsucc]
    exact ((hc.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hlim
  have hgL : g (⨅ t, x t) = ⨅ t, x t := tendsto_nhds_unique h2 h1
  have hLeq : (⨅ t, x t) = b := by
    rcases hLb.lt_or_eq with hl | he
    · exact absurd hgL (ne_of_lt (hdown _ hl (by linarith)))
    · exact he.symm
  exact ⟨hanti, hinv, hLeq ▸ hlim⟩

/-- AKMM, p. 77, Fig. 3.3: under `SolowThreeCrossings` the right side of (3.5),
`g(k) = (1 − δ)k + s f(k)`, is continuous and nondecreasing on `k > 0`, fixes `k̄₁, k̄₂, k̄₃`, lies
above the diagonal on `(0, k̄₁)` and `(k̄₂, k̄₃)` and below it on `(k̄₁, k̄₂)` and `(k̄₃, ∞)`. -/
theorem solow_three_crossings_map {f : ℝ → ℝ} {s δ k₁ k₂ k₃ : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) :
    MonotoneOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) ∧
      ContinuousOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) ∧
      (1 - δ) * k₁ + s * f k₁ = k₁ ∧ (1 - δ) * k₂ + s * f k₂ = k₂ ∧
      (1 - δ) * k₃ + s * f k₃ = k₃ ∧
      (∀ y, 0 < y → y < k₁ → y < (1 - δ) * y + s * f y) ∧
      (∀ y, k₁ < y → y < k₂ → (1 - δ) * y + s * f y < y) ∧
      (∀ y, k₂ < y → y < k₃ → y < (1 - δ) * y + s * f y) ∧
      (∀ y, k₃ < y → (1 - δ) * y + s * f y < y) := by
  refine ⟨?_, ?_, by linarith [h.fix₁], by linarith [h.fix₂], by linarith [h.fix₃],
    fun y h1 h2 => by linarith [h.above₁ y h1 h2], fun y h1 h2 => by linarith [h.below₂ y h1 h2],
    fun y h1 h2 => by linarith [h.above₃ y h1 h2], fun y h1 => by linarith [h.below₄ y h1]⟩
  · intro x hx y hy hxy
    have h1 := mul_le_mul_of_nonneg_left (h.mono hx hy hxy) h.saving_pos.le
    have h2 := mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr h.depreciation_lt_one.le)
    simp only
    linarith
  · exact (continuousOn_id.const_mul (1 - δ)).add (h.cont.const_mul s)

/-- AKMM, p. 77, Fig. 3.3 (the basins): "when the economy starts from a very low `k₀`, the
economy converges to `k̄₁` and gets trapped in it"; "pushed up to a larger level than `k̄₂`, … it
would converge to `k̄₃`". Every path of (3.5) from `k₀ ∈ (0, k̄₂)` converges to `k̄₁`, from
`k₀ = k̄₂` stays there, and from `k₀ > k̄₂` converges to `k̄₃`. -/
theorem solow_poverty_trap_basins {f : ℝ → ℝ} {s δ k₁ k₂ k₃ : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (k 0 < k₂ → Tendsto k atTop (𝓝 k₁)) ∧ (k 0 = k₂ → ∀ t, k t = k₂) ∧
      (k₂ < k 0 → Tendsto k atTop (𝓝 k₃)) := by
  obtain ⟨hm, hc, hf1, hf2, hf3, hu1, hd2, hu3, hd4⟩ := solow_three_crossings_map h
  have p1 := h.pos₁
  have p12 := h.lt₁₂
  have p23 := h.lt₂₃
  refine ⟨fun hlt => ?_, fun heq t => ?_, fun hgt => ?_⟩
  · rcases le_or_gt (k 0) k₁ with hle | hgt1
    · exact (solow_ptrap_rise le_rfl hm hc hf1 hu1 hk0 hle hk).2.2
    · exact (solow_ptrap_fall p1 hm hc hf1 hd2 hgt1.le hlt hk).2.2
  · induction t with
    | zero => exact heq
    | succ u ih => rw [hk u, ih]; exact hf2
  · rcases le_or_gt (k 0) k₃ with hle | hgt3
    · exact (solow_ptrap_rise (by linarith) hm hc hf3 hu3 hgt hle hk).2.2
    · exact (solow_ptrap_fall (by linarith) hm hc hf3 (fun y hy _ => hd4 y hy) hgt3.le
        (lt_add_one (k 0)) hk).2.2

/-- AKMM, p. 77, Fig. 3.3: "of these three, `k̄₁` and `k̄₃` are stable steady states", while `k̄₂`
is not: "a small perturbation away from the steady state leads further away from it". Under
`SolowThreeCrossings`, `k̄₁` and `k̄₃` are locally attracting for the map of (3.5), `k̄₂` is not,
and just below (above) `k̄₂` the map moves capital down (up), away from `k̄₂`. -/
theorem solow_poverty_trap_stability {f : ℝ → ℝ} {s δ k₁ k₂ k₃ : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) :
    SolowLocallyAttracting (fun x => (1 - δ) * x + s * f x) k₁ ∧
      SolowLocallyAttracting (fun x => (1 - δ) * x + s * f x) k₃ ∧
      ¬ SolowLocallyAttracting (fun x => (1 - δ) * x + s * f x) k₂ ∧
      (∀ y, k₁ < y → y < k₂ → (1 - δ) * y + s * f y < y) ∧
      (∀ y, k₂ < y → y < k₃ → y < (1 - δ) * y + s * f y) := by
  obtain ⟨-, -, -, -, -, -, hd2, hu3, -⟩ := solow_three_crossings_map h
  have p1 := h.pos₁
  have p12 := h.lt₁₂
  have p23 := h.lt₂₃
  set g := fun x => (1 - δ) * x + s * f x with hg
  have horb : ∀ x₀ : ℝ, ∀ t, g^[t + 1] x₀ = (1 - δ) * g^[t] x₀ + s * f (g^[t] x₀) :=
    fun x₀ t => Function.iterate_succ_apply' g t x₀
  have hlow : ∀ x₀, 0 < x₀ → x₀ < k₂ → Tendsto (fun t => g^[t] x₀) atTop (𝓝 k₁) :=
    fun x₀ h0 h2 => (solow_poverty_trap_basins h (k := fun t => g^[t] x₀) h0 (horb x₀)).1 h2
  have hhigh : ∀ x₀, k₂ < x₀ → Tendsto (fun t => g^[t] x₀) atTop (𝓝 k₃) :=
    fun x₀ h2 => (solow_poverty_trap_basins h (k := fun t => g^[t] x₀) (by
      change 0 < x₀; linarith) (horb x₀)).2.2 h2
  refine ⟨⟨min k₁ (k₂ - k₁), lt_min p1 (by linarith), fun x₀ hx => ?_⟩,
    ⟨k₃ - k₂, by linarith, fun x₀ hx => ?_⟩, ?_, hd2, hu3⟩
  · have hm1 := min_le_left k₁ (k₂ - k₁)
    have hm2 := min_le_right k₁ (k₂ - k₁)
    rw [abs_lt] at hx
    exact hlow x₀ (by linarith) (by linarith)
  · rw [abs_lt] at hx
    exact hhigh x₀ (by linarith)
  · rintro ⟨ε, hε, hat⟩
    have hm : 0 < min ε (k₂ - k₁) := lt_min hε (by linarith)
    have hm1 := min_le_left ε (k₂ - k₁)
    have hm2 := min_le_right ε (k₂ - k₁)
    have h2 := hat (k₂ - min ε (k₂ - k₁) / 2) (by
      rw [abs_lt]; constructor <;> linarith)
    have h1 := hlow (k₂ - min ε (k₂ - k₁) / 2) (by linarith) (by linarith)
    have := tendsto_nhds_unique h1 h2
    linarith

/-- AKMM, p. 77: "if the saving rate is raised sufficiently … the steady states `k̄₁` and `k̄₂`
will disappear and the economy converges globally". Suppose `f` is continuous and nondecreasing
on `k > 0`, `f(k) ≥ m k` on `(0, k̂]` for some `m > 0` (in Fig. 3.3, `f(0) > 0`), and the average
product `f(k)/k` is strictly decreasing on `[k̂, ∞)` with limit `0`. Then for every saving rate
`s' > δ/m` there is exactly one positive steady state `k̄ > k̂`, the curve is above the diagonal
below it and below the diagonal above it, and every path from `k₀ > 0` converges to it. -/
theorem solow_poverty_trap_saving_rise {f : ℝ → ℝ} {δ s' m kh : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hc : ContinuousOn f (Set.Ioi 0)) (hmono : MonotoneOn f (Set.Ioi 0)) (hm : 0 < m)
    (hkh : 0 < kh) (hlow : ∀ k, 0 < k → k ≤ kh → m * k ≤ f k)
    (hanti : StrictAntiOn (fun k => f k / k) (Set.Ici kh))
    (hlim : Tendsto (fun k => f k / k) atTop (𝓝 0)) (hs' : δ / m < s') :
    ∃ ks, kh < ks ∧ δ * ks = s' * f ks ∧ (∀ k, 0 < k → k < ks → δ * k < s' * f k) ∧
      (∀ k, ks < k → s' * f k < δ * k) ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → (∀ t, x (t + 1) = (1 - δ) * x t + s' * f (x t)) →
        Tendsto x atTop (𝓝 ks) := by
  have hs'pos : 0 < s' := lt_trans (div_pos hδ hm) hs'
  have hδs : δ < s' * m := (div_lt_iff₀ hm).mp hs'
  have hq : 0 < δ / s' := div_pos hδ hs'pos
  have hqm : δ / s' < m := (div_lt_iff₀ hs'pos).mpr (by linarith)
  have hkh_av : m ≤ f kh / kh := (le_div_iff₀ hkh).mpr (hlow kh hkh le_rfl)
  -- a capital stock beyond `k̂` with average product below `δ/s'`
  obtain ⟨K, hK, hKkh⟩ := ((hlim.eventually (gt_mem_nhds hq)).and
    (eventually_ge_atTop kh)).exists
  have hKpos : 0 < K := lt_of_lt_of_le hkh hKkh
  have hcav : ContinuousOn (fun k => f k / k) (Set.Icc kh K) := by
    have hsub : Set.Icc kh K ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le hkh hy.1
    exact (hc.mono hsub).div continuousOn_id fun y hy => ne_of_gt (hsub hy)
  obtain ⟨ks, hks, hksv⟩ := intermediate_value_Icc' hKkh hcav
    (Set.mem_Icc.mpr ⟨hK.le, by linarith⟩)
  have hksv' : f ks / ks = δ / s' := hksv
  have hkspos : 0 < ks := lt_of_lt_of_le hkh hks.1
  have hkslt : kh < ks := by
    rcases hks.1.lt_or_eq with hl | he
    · exact hl
    · rw [← he] at hksv'; linarith
  have hfix : δ * ks = s' * f ks := by
    rw [div_eq_div_iff (ne_of_gt hkspos) (ne_of_gt hs'pos)] at hksv'
    linarith
  have hbelow : ∀ k, 0 < k → k < ks → δ * k < s' * f k := by
    intro k hk hlt
    rcases le_or_gt k kh with hle | hgt
    · have := hlow k hk hle
      nlinarith
    · have h := hanti (Set.mem_Ici.mpr hgt.le) (Set.mem_Ici.mpr hks.1) hlt
      simp only at h
      rw [hksv', div_lt_div_iff₀ hs'pos hk] at h
      linarith
  have habove : ∀ k, ks < k → s' * f k < δ * k := by
    intro k hlt
    have hk : 0 < k := hkspos.trans hlt
    have h := hanti (Set.mem_Ici.mpr hks.1) (Set.mem_Ici.mpr (hks.1.trans hlt.le)) hlt
    simp only at h
    rw [hksv', div_lt_div_iff₀ hk hs'pos] at h
    linarith
  refine ⟨ks, hkslt, hfix, hbelow, habove, fun x hx0 hx => ?_⟩
  have hgm : StrictMonoOn (fun y => (1 - δ) * y + s' * f y) (Set.Ioi 0) := by
    intro y hy z hz hyz
    have h1 := mul_le_mul_of_nonneg_left (hmono hy hz hyz.le) hs'pos.le
    have h2 := mul_lt_mul_of_pos_left hyz (sub_pos.mpr hδ1)
    simp only
    linarith
  have hgc : ContinuousOn (fun y => (1 - δ) * y + s' * f y) (Set.Ioi 0) :=
    (continuousOn_id.const_mul (1 - δ)).add (hc.const_mul s')
  exact (Solow1956.DiscreteTime.Map.attracting_orbit hgm hgc hkspos (by linarith)
    (fun y hy hlt => by linarith [hbelow y hy hlt]) (fun y hlt => by linarith [habove y hlt])
    hx0 hx).2.2.2.2.2

/-- AKMM, p. 77 (poverty traps): raising the saving rate from `s` to `s' > max(s, δ/m)` removes
the steady states `k̄₁` and `k̄₂` of Fig. 3.3: the only positive steady state at `s'` lies above
`k̄₃`, at `k̄₁` and `k̄₂` the curve is now strictly above the diagonal, and the economy converges
globally to the new steady state. -/
theorem solow_poverty_trap_saving_rise_removes {f : ℝ → ℝ} {s δ k₁ k₂ k₃ s' m kh : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) (hm : 0 < m) (hkh : 0 < kh)
    (hlow : ∀ k, 0 < k → k ≤ kh → m * k ≤ f k)
    (hanti : StrictAntiOn (fun k => f k / k) (Set.Ici kh))
    (hlim : Tendsto (fun k => f k / k) atTop (𝓝 0)) (hs' : δ / m < s') (hss : s < s') :
    ∃ ks, k₃ < ks ∧ δ * ks = s' * f ks ∧ (∀ k, 0 < k → δ * k = s' * f k → k = ks) ∧
      δ * k₁ < s' * f k₁ ∧ δ * k₂ < s' * f k₂ ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → (∀ t, x (t + 1) = (1 - δ) * x t + s' * f (x t)) →
        Tendsto x atTop (𝓝 ks) := by
  obtain ⟨ks, -, hfix, hbelow, habove, hconv⟩ := solow_poverty_trap_saving_rise
    h.depreciation_pos h.depreciation_lt_one h.cont h.mono hm hkh hlow hanti hlim hs'
  have p1 := h.pos₁
  have p12 := h.lt₁₂
  have p23 := h.lt₂₃
  have hδ := h.depreciation_pos
  have hs := h.saving_pos
  -- at `k̄₃` the new curve is strictly above the diagonal
  have hf3 : 0 < f k₃ := by
    have := h.fix₃
    have : 0 < s * f k₃ := by rw [← this]; exact mul_pos hδ (by linarith)
    exact pos_of_mul_pos_right this hs.le
  have h3 : δ * k₃ < s' * f k₃ := by
    rw [h.fix₃]; exact mul_lt_mul_of_pos_right hss hf3
  have hks3 : k₃ < ks := by
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hl | he
    · linarith [habove k₃ hl]
    · rw [he] at hfix; linarith
  have huniq : ∀ k, 0 < k → δ * k = s' * f k → k = ks := by
    intro k hk he
    rcases lt_trichotomy k ks with hl | heq | hg
    · linarith [hbelow k hk hl]
    · exact heq
    · linarith [habove k hg]
  exact ⟨ks, hks3, hfix, huniq, hbelow k₁ p1 (by linarith), hbelow k₂ (by linarith)
    (by linarith), hconv⟩

/-- AKMM, p. 77 (escaping the trap): "to escape from the trap, the capital stock would have to be
pushed up to a larger level than `k̄₂`, from which it would converge to `k̄₃`. One way to achieve
this movement is to (temporarily) encourage very high saving." Under the hypotheses of
`solow_poverty_trap_saving_rise_removes`, from every `k₀ > 0` there is a date `T` such that
saving at `s'` before `T` and at the original `s` from `T` on takes the economy to `k̄₃`. -/
theorem solow_poverty_trap_temporary_saving {f : ℝ → ℝ} {s δ k₁ k₂ k₃ s' m kh : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) (hm : 0 < m) (hkh : 0 < kh)
    (hlow : ∀ k, 0 < k → k ≤ kh → m * k ≤ f k)
    (hanti : StrictAntiOn (fun k => f k / k) (Set.Ici kh))
    (hlim : Tendsto (fun k => f k / k) atTop (𝓝 0)) (hs' : δ / m < s') (hss : s < s')
    {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∃ T : ℕ, ∀ k : ℕ → ℝ, k 0 = k₀ →
      (∀ t, t < T → k (t + 1) = (1 - δ) * k t + s' * f (k t)) →
      (∀ t, T ≤ t → k (t + 1) = (1 - δ) * k t + s * f (k t)) → Tendsto k atTop (𝓝 k₃) := by
  obtain ⟨ks, hks3, -, -, -, -, hconv⟩ :=
    solow_poverty_trap_saving_rise_removes h hm hkh hlow hanti hlim hs' hss
  set g := fun y => (1 - δ) * y + s' * f y with hg
  have horb : ∀ t, g^[t + 1] k₀ = (1 - δ) * g^[t] k₀ + s' * f (g^[t] k₀) :=
    fun t => Function.iterate_succ_apply' g t k₀
  have hx := hconv (fun t => g^[t] k₀) hk₀ horb
  obtain ⟨T, hT⟩ := (hx.eventually (lt_mem_nhds (h.lt₂₃.trans hks3))).exists
  refine ⟨T, fun k hk0 hbefore hafter => ?_⟩
  have hagree : ∀ t, t ≤ T → k t = g^[t] k₀ := by
    intro t
    induction t with
    | zero => intro _; exact hk0
    | succ u ih =>
      intro hu
      rw [hbefore u (by omega), ih (by omega), horb u]
  have hkT : k₂ < k T := by rw [hagree T le_rfl]; exact hT
  have hshift : Tendsto (fun t => k (t + T)) atTop (𝓝 k₃) := by
    have hp : 0 < k₂ := h.pos₁.trans h.lt₁₂
    refine (solow_poverty_trap_basins h (k := fun t => k (t + T)) (by
      rw [zero_add]; linarith) (fun t => ?_)).2.2 (by
      rw [zero_add]; exact hkT)
    rw [show t + 1 + T = t + T + 1 by omega]
    exact hafter (t + T) (by omega)
  exact (tendsto_add_atTop_iff_nat T).mp hshift

/-- AKMM, p. 77, Fig. 3.3 (a concrete instance): a technology with a convex middle section,
`f(k) = max(1, min(2k − 2, 3))`, flat at `1` up to `k = 3/2`, rising with slope `2` and flat at
`3` from `k = 5/2`. -/
noncomputable def solowPovertyTrapTech (k : ℝ) : ℝ := max 1 (min (2 * k - 2) 3)

/-- AKMM, p. 77, Fig. 3.3: the hypotheses are not vacuous. With `f = solowPovertyTrapTech` and
`s = δ = 1/10`, `SolowThreeCrossings` holds with `k̄₁ = 1`, `k̄₂ = 2`, `k̄₃ = 3`; and
`f(k) ≥ (2/5)k` on `(0, 5/2]`, `f(k)/k = 3/k` is strictly decreasing on `[5/2, ∞)` with
limit `0`. -/
theorem solow_poverty_trap_example :
    SolowThreeCrossings solowPovertyTrapTech (1 / 10) (1 / 10) 1 2 3 ∧
      (∀ k, 0 < k → k ≤ 5 / 2 → 2 / 5 * k ≤ solowPovertyTrapTech k) ∧
      StrictAntiOn (fun k => solowPovertyTrapTech k / k) (Set.Ici (5 / 2)) ∧
      Tendsto (fun k => solowPovertyTrapTech k / k) atTop (𝓝 0) := by
  have hge : ∀ k, 1 ≤ solowPovertyTrapTech k := fun k => le_max_left _ _
  have htop : ∀ k, 5 / 2 ≤ k → solowPovertyTrapTech k = 3 := by
    intro k hk
    unfold solowPovertyTrapTech
    rw [min_eq_right (by linarith), max_eq_right (by norm_num)]
  have hv : ∀ k, solowPovertyTrapTech k = max 1 (min (2 * k - 2) 3) := fun k => rfl
  have h1 : solowPovertyTrapTech 1 = 1 := by
    rw [hv, min_eq_left (by norm_num), max_eq_left (by norm_num)]
  have h2 : solowPovertyTrapTech 2 = 2 := by
    rw [hv, min_eq_left (by norm_num), max_eq_right (by norm_num)]
    norm_num
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num,
    by rw [h1], by rw [h2], by rw [htop 3 (by norm_num)], ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (continuous_const.max (((continuous_const.mul continuous_id).sub
      continuous_const).min continuous_const)).continuousOn
  · intro x _ y _ hxy
    exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)
  · intro k _ hk
    linarith [hge k]
  · intro k hk1 hk2
    have : solowPovertyTrapTech k < k := by
      rw [hv]
      exact max_lt hk1 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    linarith
  · intro k hk2 hk3
    have : k < solowPovertyTrapTech k := by
      rw [hv]
      exact lt_of_lt_of_le (lt_min (by linarith) hk3) (le_max_right _ _)
    linarith
  · intro k hk3
    have : solowPovertyTrapTech k < k := by
      rw [hv]
      exact max_lt (by linarith) (lt_of_le_of_lt (min_le_right _ _) hk3)
    linarith
  · intro k _ hk
    linarith [hge k]
  · intro x hx y hy hxy
    have hx' : (5 : ℝ) / 2 ≤ x := hx
    have hy' : (5 : ℝ) / 2 ≤ y := hy
    simp only [htop x hx', htop y hy']
    exact div_lt_div_of_pos_left (by norm_num) (by linarith) hxy
  · have h3 : Tendsto (fun k : ℝ => 3 / k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop (5 / 2)] with k hk
    rw [htop k hk]

/-- AKMM, p. 77, Fig. 3.3, for the concrete technology `solowPovertyTrapTech` with
`s = δ = 1/10`: paths from `k₀ ∈ (0, 2)` converge to `1` and from `k₀ > 2` to `3`; `1` and `3`
are locally attracting and `2` is not; and at the saving rate `s' = 1/2` the only positive
steady state is `15`, to which every path converges. -/
theorem solow_poverty_trap_example_dynamics :
    (∀ k : ℕ → ℝ, 0 < k 0 → (∀ t, k (t + 1) = (1 - 1 / 10) * k t +
        1 / 10 * solowPovertyTrapTech (k t)) →
      (k 0 < 2 → Tendsto k atTop (𝓝 1)) ∧ (2 < k 0 → Tendsto k atTop (𝓝 3))) ∧
      SolowLocallyAttracting (fun x => (1 - 1 / 10) * x + 1 / 10 * solowPovertyTrapTech x) 1 ∧
      SolowLocallyAttracting (fun x => (1 - 1 / 10) * x + 1 / 10 * solowPovertyTrapTech x) 3 ∧
      ¬ SolowLocallyAttracting
        (fun x => (1 - 1 / 10) * x + 1 / 10 * solowPovertyTrapTech x) 2 ∧
      (∀ k, 0 < k → 1 / 10 * k = 1 / 2 * solowPovertyTrapTech k → k = 15) ∧
      1 / 10 * 15 = 1 / 2 * solowPovertyTrapTech 15 ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → (∀ t, x (t + 1) = (1 - 1 / 10) * x t +
        1 / 2 * solowPovertyTrapTech (x t)) → Tendsto x atTop (𝓝 15) := by
  obtain ⟨h, hlow, hanti, hlim⟩ := solow_poverty_trap_example
  obtain ⟨hs1, hs3, hs2, -, -⟩ := solow_poverty_trap_stability h
  obtain ⟨ks, -, -, huniq, -, -, hconv⟩ :=
    solow_poverty_trap_saving_rise_removes (s' := 1 / 2) h
    (by norm_num : (0 : ℝ) < 2 / 5) (by norm_num : (0 : ℝ) < 5 / 2) hlow hanti hlim
    (by norm_num) (by norm_num)
  have h15 : 1 / 10 * (15 : ℝ) = 1 / 2 * solowPovertyTrapTech 15 := by
    unfold solowPovertyTrapTech
    rw [min_eq_right (by norm_num), max_eq_right (by norm_num)]
    norm_num
  have hks : (15 : ℝ) = ks := huniq 15 (by norm_num) h15
  refine ⟨fun k hk0 hk => ?_, hs1, hs3, hs2, fun k hk he => (huniq k hk he).trans hks.symm, h15,
    fun x hx0 hx => hks ▸ hconv x hx0 hx⟩
  have hb := solow_poverty_trap_basins h hk0 hk
  exact ⟨hb.1, hb.2.2⟩

/-- AKMM, p. 82: in the book's approximation (3.10), written in relative deviations, the gap
`x_t = (k_t − k̄)/k̄` (or `Δk_t = k_t − k̄`) obeys `x_{t+1} = (1 − λ)x_t`, so
`x_t = (1 − λ)^t x_0`: `λ` is the fraction of the remaining gap closed each period. -/
theorem solow_linearised_gap_closed_form {lam : ℝ} {x : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t) (t : ℕ) : x t = (1 - lam) ^ t * x 0 := by
  induction t with
  | zero => simp
  | succ u ih => rw [hx u, ih, pow_succ]; ring

/-- AKMM, p. 82, Figure 3.5 ("slow and fast convergence"): "a large value of `λ` implies that
`Δk_{t+1}` becomes smaller (in absolute value) more quickly, implying a faster convergence". Two
economies with speeds `λ₁ < λ₂ ≤ 1` (as in (3.10), where `λ < 1`) start from the same gap
`x₀` in the approximation `x_{t+1} = (1 − λ)x_t`. Then at every date the gap of the faster one is
no larger in absolute value, strictly smaller from date 1 on when `x₀ ≠ 0`; starting below the
steady state (`x₀ ≤ 0`, the figure's `k₀ < k̄`) both stay below it with the faster one closer
(`x_t ≤ y_t ≤ 0`); and whenever the slower gap is within `ε` the faster one is too, so the
faster economy needs no more steps to come within any `ε` of the steady state (and strictly fewer
for some `ε`). -/
theorem solow_faster_convergence {lam₁ lam₂ : ℝ} {x y : ℕ → ℝ} (hlam : lam₁ < lam₂)
    (hlam₂ : lam₂ ≤ 1) (hx : ∀ t, x (t + 1) = (1 - lam₁) * x t)
    (hy : ∀ t, y (t + 1) = (1 - lam₂) * y t) (h0 : y 0 = x 0) :
    (∀ t, |y t| ≤ |x t|) ∧ (x 0 ≠ 0 → ∀ t, 0 < t → |y t| < |x t|) ∧
      (x 0 ≤ 0 → ∀ t, x t ≤ y t ∧ y t ≤ 0) ∧ (∀ ε t, |x t| ≤ ε → |y t| ≤ ε) ∧
      (x 0 ≠ 0 → ∃ ε, |y 1| ≤ ε ∧ ¬ |x 1| ≤ ε) := by
  have hb : 0 ≤ 1 - lam₂ := by linarith
  have hab : 1 - lam₂ < 1 - lam₁ := by linarith
  have hxt := solow_linearised_gap_closed_form hx
  have hyt := solow_linearised_gap_closed_form hy
  have hpow : ∀ t, (1 - lam₂) ^ t ≤ (1 - lam₁) ^ t := fun t => pow_le_pow_left₀ hb hab.le t
  have habs : ∀ t, |y t| ≤ |x t| := by
    intro t
    rw [hxt t, hyt t, h0, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hb t),
      abs_of_nonneg (pow_nonneg (hb.trans hab.le) t)]
    exact mul_le_mul_of_nonneg_right (hpow t) (abs_nonneg _)
  have hstrict : x 0 ≠ 0 → ∀ t, 0 < t → |y t| < |x t| := by
    intro hx0 t ht
    rw [hxt t, hyt t, h0, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hb t),
      abs_of_nonneg (pow_nonneg (hb.trans hab.le) t)]
    exact mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hab hb (Nat.pos_iff_ne_zero.mp ht))
      (abs_pos.mpr hx0)
  refine ⟨habs, hstrict, fun hx0 t => ?_, fun ε t hε => (habs t).trans hε, fun hx0 => ?_⟩
  · rw [hxt t, hyt t, h0]
    exact ⟨mul_le_mul_of_nonpos_right (hpow t) hx0,
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hb t) hx0⟩
  · exact ⟨|y 1|, le_rfl, not_le.mpr (hstrict hx0 1 one_pos)⟩

/-- AKMM, p. 83 ("the convergence is faster when `α` is small and `δ` is large"), for (3.11)
`λ = δ(1 − α)`, and the same for (3.13) `λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))` with
`(1 + γ)(1 + n) ≥ 1`: `λ` is strictly decreasing in `α` and strictly increasing in `δ`. -/
theorem solow_speed_parameters {α α' δ δ' G : ℝ} (hα : α < α') (hα1 : α' < 1) (hδ : 0 < δ)
    (hδδ : δ < δ') (hδ1 : δ' ≤ 1) (hG : 1 ≤ G) :
    δ * (1 - α') < δ * (1 - α) ∧ δ * (1 - α') < δ' * (1 - α') ∧
      (1 - α') * (1 - (1 - δ) / G) < (1 - α) * (1 - (1 - δ) / G) ∧
      (1 - α') * (1 - (1 - δ) / G) < (1 - α') * (1 - (1 - δ') / G) := by
  have hGpos : 0 < G := by linarith
  have hq : (1 - δ) / G < 1 := by
    rw [div_lt_one hGpos]; linarith
  have hqq : (1 - δ') / G < (1 - δ) / G := div_lt_div_of_pos_right (by linarith) hGpos
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end AKMM.Solow

set_option linter.style.longLine false
#print axioms AKMM.Solow.StrictQuasiconcavePos
#print axioms AKMM.Solow.SolowAssumptions
#print axioms AKMM.Solow.SolowAssumptions.mk
#print axioms AKMM.Solow.SolowAssumptions.mono_capital
#print axioms AKMM.Solow.SolowAssumptions.mono_labour
#print axioms AKMM.Solow.SolowAssumptions.quasiconcave
#print axioms AKMM.Solow.SolowAssumptions.crs
#print axioms AKMM.Solow.SolowAssumptions.zero_capital
#print axioms AKMM.Solow.SolowAssumptions.continuous
#print axioms AKMM.Solow.SolowAssumptions.differentiable
#print axioms AKMM.Solow.SolowAssumptions.derivative_continuous
#print axioms AKMM.Solow.SolowAssumptions.inada_zero
#print axioms AKMM.Solow.SolowAssumptions.inada_top
#print axioms AKMM.Solow.intensive
#print axioms AKMM.Solow.solow_intensive_form
#print axioms AKMM.Solow.solow_intensive_zero
#print axioms AKMM.Solow.solow_intensive_strictMono
#print axioms AKMM.Solow.solow_intensive_pos
#print axioms AKMM.Solow.solow_intensive_strictConcave
#print axioms AKMM.Solow.solow_intensive_deriv_pos
#print axioms AKMM.Solow.solow_technology
#print axioms AKMM.Solow.solow_rpow_strictQuasiconcave
#print axioms AKMM.Solow.solow_deriv_rpow_mul_const
#print axioms AKMM.Solow.solow_cobbDouglas_assumptions
#print axioms AKMM.Solow.solow_intensive_cobbDouglas
#print axioms AKMM.Solow.solow_assumption1_conflicts_assumption4
#print axioms AKMM.Solow.solow_assumption2_alone_counterexample
#print axioms AKMM.Solow.solow_params_basic
#print axioms AKMM.Solow.eq_3_5
#print axioms AKMM.Solow.solow_growth_rate_form
#print axioms AKMM.Solow.solow_fixed_iff
#print axioms AKMM.Solow.solow_steady_existsUnique
#print axioms AKMM.Solow.solow_steady_spec
#print axioms AKMM.Solow.solow_global_convergence
#print axioms AKMM.Solow.solow_convergence_proof_steps
#print axioms AKMM.Solow.solow_average_product_strictAnti
#print axioms AKMM.Solow.eq_3_6
#print axioms AKMM.Solow.solow_cobbDouglas_output
#print axioms AKMM.Solow.solow_steady_strictMono_saving
#print axioms AKMM.Solow.solow_steady_strictAnti_depreciation
#print axioms AKMM.Solow.solow_capital_output_ratio
#print axioms AKMM.Solow.solow_capital_output_ratio_mono
#print axioms AKMM.Solow.solow_average_strictAnti_of_concave
#print axioms AKMM.Solow.solow_steady_existsUnique_weak
#print axioms AKMM.Solow.solow_global_convergence_weak
#print axioms AKMM.Solow.solow_endogenous_no_steady_state
#print axioms AKMM.Solow.solow_endogenous_growth
#print axioms AKMM.Solow.solow_ak_constant_gap
#print axioms AKMM.Solow.solow_ak_plus_labour
#print axioms AKMM.Solow.SolowLocallyAttracting
#print axioms AKMM.Solow.solow_poverty_trap_unstable
#print axioms AKMM.Solow.solow_decreasing_map_overshoots
#print axioms AKMM.Solow.solow_local_stability
#print axioms AKMM.Solow.solow_params_growth
#print axioms AKMM.Solow.eq_3_7
#print axioms AKMM.Solow.solow_fixed_iff_growth
#print axioms AKMM.Solow.solow_bgp_existsUnique
#print axioms AKMM.Solow.eq_3_8
#print axioms AKMM.Solow.solow_detrended_convergence
#print axioms AKMM.Solow.solow_bgp_strictAnti_growth
#print axioms AKMM.Solow.solow_untransform
#print axioms AKMM.Solow.solow_aggregate_convergence
#print axioms AKMM.Solow.solow_income_long_run
#print axioms AKMM.Solow.solow_bgp_income_growth
#print axioms AKMM.Solow.solow_income_growth_identity
#print axioms AKMM.Solow.solow_transition_growth
#print axioms AKMM.Solow.solow_income_growth_tendsto
#print axioms AKMM.Solow.solow_rental_rate
#print axioms AKMM.Solow.solow_wage_rate
#print axioms AKMM.Solow.solow_euler
#print axioms AKMM.Solow.solow_factor_shares
#print axioms AKMM.Solow.solow_factor_prices_bgp
#print axioms AKMM.Solow.solow_factor_prices_tendsto
#print axioms AKMM.Solow.solow_cobbDouglas_shares
#print axioms AKMM.Solow.eq_3_10
#print axioms AKMM.Solow.solow_linearised_relative
#print axioms AKMM.Solow.eq_3_11
#print axioms AKMM.Solow.solow_speed_independent_of_saving
#print axioms AKMM.Solow.solow_marginal_product_falls_with_saving
#print axioms AKMM.Solow.solow_cobbDouglas_forces_offset
#print axioms AKMM.Solow.eq_3_12
#print axioms AKMM.Solow.eq_3_13
#print axioms AKMM.Solow.solow_steady_locally_stable
#print axioms AKMM.Solow.solow_steady_locallyAttracting
#print axioms AKMM.Solow.solow_bgp_investment_rate
#print axioms AKMM.Solow.solow_saving_output_ratio
#print axioms AKMM.Solow.solow_p88_doubling_saving
#print axioms AKMM.Solow.solow_rbc_reduces
#print axioms AKMM.Solow.solow_harrod_hicks_cobbDouglas
#print axioms AKMM.Solow.solow_investment_specific
#print axioms AKMM.Solow.solow_demand_shock
#print axioms AKMM.Solow.solow_demand_unemployment_unique
#print axioms AKMM.Solow.eq_3_17
#print axioms AKMM.Solow.solow_irf_log_form
#print axioms AKMM.Solow.eq_3_18
#print axioms AKMM.Solow.solow_irf_capital_sum
#print axioms AKMM.Solow.solow_irf_capital_closed_form
#print axioms AKMM.Solow.solow_irf_output
#print axioms AKMM.Solow.solow_irf_output_printed_false
#print axioms AKMM.Solow.solow_level_linearisation
#print axioms AKMM.Solow.theorem_3A_1
#print axioms AKMM.Solow.uzawa_technology_growth
#print axioms AKMM.Solow.uzawa_technology_unique
#print axioms AKMM.Solow.uzawa_printed_rate_counterexample
#print axioms AKMM.Solow.uzawa_capital_growth
#print axioms AKMM.Solow.uzawa_investment_growth
#print axioms AKMM.Solow.eq_3A_4
#print axioms AKMM.Solow.theorem_3A_2
#print axioms AKMM.Solow.uzawa_part2_nonneg_consumption
#print axioms AKMM.Solow.uzawa_part2_solow
#print axioms AKMM.Solow.uzawa_part2_zero_output_counterexample
#print axioms AKMM.Solow.SolowThreeCrossings
#print axioms AKMM.Solow.SolowThreeCrossings.mk
#print axioms AKMM.Solow.SolowThreeCrossings.saving_pos
#print axioms AKMM.Solow.SolowThreeCrossings.depreciation_pos
#print axioms AKMM.Solow.SolowThreeCrossings.depreciation_lt_one
#print axioms AKMM.Solow.SolowThreeCrossings.cont
#print axioms AKMM.Solow.SolowThreeCrossings.mono
#print axioms AKMM.Solow.SolowThreeCrossings.pos₁
#print axioms AKMM.Solow.SolowThreeCrossings.lt₁₂
#print axioms AKMM.Solow.SolowThreeCrossings.lt₂₃
#print axioms AKMM.Solow.SolowThreeCrossings.fix₁
#print axioms AKMM.Solow.SolowThreeCrossings.fix₂
#print axioms AKMM.Solow.SolowThreeCrossings.fix₃
#print axioms AKMM.Solow.SolowThreeCrossings.above₁
#print axioms AKMM.Solow.SolowThreeCrossings.below₂
#print axioms AKMM.Solow.SolowThreeCrossings.above₃
#print axioms AKMM.Solow.SolowThreeCrossings.below₄
#print axioms AKMM.Solow.solow_ptrap_rise
#print axioms AKMM.Solow.solow_ptrap_fall
#print axioms AKMM.Solow.solow_three_crossings_map
#print axioms AKMM.Solow.solow_poverty_trap_basins
#print axioms AKMM.Solow.solow_poverty_trap_stability
#print axioms AKMM.Solow.solow_poverty_trap_saving_rise
#print axioms AKMM.Solow.solow_poverty_trap_saving_rise_removes
#print axioms AKMM.Solow.solow_poverty_trap_temporary_saving
#print axioms AKMM.Solow.solowPovertyTrapTech
#print axioms AKMM.Solow.solow_poverty_trap_example
#print axioms AKMM.Solow.solow_poverty_trap_example_dynamics
#print axioms AKMM.Solow.solow_linearised_gap_closed_form
#print axioms AKMM.Solow.solow_faster_convergence
#print axioms AKMM.Solow.solow_speed_parameters
