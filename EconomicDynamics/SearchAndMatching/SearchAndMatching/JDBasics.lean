/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tools for Miao §§18.2–18.3: Nash bargaining, first-order and envelope conditions

Generic facts used by the derivations of Miao, *Economic Dynamics in Discrete Time*, §§18.2–18.3
(pp. 600–614):

* **Nash bargaining with affine surpluses.** If the worker's surplus is `a + λ w` and the firm's is
  `c − w`, then `w` maximises the Nash product `(a + λ w)^η (c − w)^(1−η)` over the feasible wages
  iff `(1 − η)(a + λ w) = η λ (c − w)` (`jd_nash_iff`). This is the first-order condition used for
  (18.37)–(18.38) (`λ = 1`) and in §18.3 (`λ = Λ_t`, the marginal utility). The proof is the
  weighted AM–GM inequality with its equality case (`jd_nash_le`, `jd_nash_eq_iff`), so it is a
  global statement, not only a first-order condition.
* **First-order and envelope conditions** (`jd_foc`, `jd_envelope`): at a maximiser the derivative
  of the objective vanishes; if `g ≤ W` with equality at `x₀` and both are differentiable there,
  then `W′(x₀) = g′(x₀)` (the envelope condition, with `g` the objective at the optimal control).
* **Constant returns to scale**: the partial derivatives of a linearly homogeneous function are
  homogeneous of degree zero (`jd_partial_homog_one`, `jd_partial_homog_two`).
* **Affine recursions** `u_{t+1} = a u_t + r` (`jd_affine_sol`, `jd_affine_antitone`,
  `jd_affine_tendsto`): used for unemployment dynamics (18.43).
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Weighted AM–GM in the form used for Nash bargaining (Miao, (18.11), p. 590, used on
pp. 601 and 612): `x^η y^(1−η) ≤ η^η (1−η)^(1−η) (x + y)`. -/
theorem jd_nash_le {η x y : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ η * y ^ (1 - η) ≤ η ^ η * (1 - η) ^ (1 - η) * (x + y) := by
  have h1η : 0 < 1 - η := by linarith
  have hp1 : 0 ≤ x / η := div_nonneg hx hη0.le
  have hp2 : 0 ≤ y / (1 - η) := div_nonneg hy h1η.le
  have key := Real.geom_mean_le_arith_mean2_weighted hη0.le h1η.le hp1 hp2 (by ring)
  have ex : x = η * (x / η) := by field_simp
  have ey : y = (1 - η) * (y / (1 - η)) := by field_simp
  have hxe : x ^ η = η ^ η * (x / η) ^ η := by
    conv_lhs => rw [ex]
    exact Real.mul_rpow hη0.le hp1
  have hye : y ^ (1 - η) = (1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η) := by
    conv_lhs => rw [ey]
    exact Real.mul_rpow h1η.le hp2
  have hs : η * (x / η) + (1 - η) * (y / (1 - η)) = x + y := by field_simp
  rw [hxe, hye, ← hs]
  have hc : 0 ≤ η ^ η * (1 - η) ^ (1 - η) :=
    mul_nonneg (Real.rpow_nonneg hη0.le _) (Real.rpow_nonneg h1η.le _)
  calc η ^ η * (x / η) ^ η * ((1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η))
      = η ^ η * (1 - η) ^ (1 - η) * ((x / η) ^ η * (y / (1 - η)) ^ (1 - η)) := by ring
    _ ≤ η ^ η * (1 - η) ^ (1 - η) * (η * (x / η) + (1 - η) * (y / (1 - η))) :=
        mul_le_mul_of_nonneg_left key hc

/-- The equality case of `jd_nash_le` (Miao, p. 591): equality iff `(1 − η) x = η y`, i.e. the
worker receives the share `η` of the total surplus. -/
theorem jd_nash_eq_iff {η x y : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ η * y ^ (1 - η) = η ^ η * (1 - η) ^ (1 - η) * (x + y) ↔ (1 - η) * x = η * y := by
  have h1η : 0 < 1 - η := by linarith
  have hp1 : 0 ≤ x / η := div_nonneg hx hη0.le
  have hp2 : 0 ≤ y / (1 - η) := div_nonneg hy h1η.le
  have key := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hη0 h1η hp1 hp2 (by ring)
  have ex : x = η * (x / η) := by field_simp
  have ey : y = (1 - η) * (y / (1 - η)) := by field_simp
  have hxe : x ^ η = η ^ η * (x / η) ^ η := by
    conv_lhs => rw [ex]
    exact Real.mul_rpow hη0.le hp1
  have hye : y ^ (1 - η) = (1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η) := by
    conv_lhs => rw [ey]
    exact Real.mul_rpow h1η.le hp2
  have hs : η * (x / η) + (1 - η) * (y / (1 - η)) = x + y := by field_simp
  have hc : 0 < η ^ η * (1 - η) ^ (1 - η) :=
    mul_pos (Real.rpow_pos_of_pos hη0 _) (Real.rpow_pos_of_pos h1η _)
  rw [hxe, hye, ← hs]
  have e1 : η ^ η * (x / η) ^ η * ((1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η))
      = η ^ η * (1 - η) ^ (1 - η) * ((x / η) ^ η * (y / (1 - η)) ^ (1 - η)) := by ring
  rw [e1, mul_right_inj' hc.ne', key]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- **Nash bargaining with affine surpluses** (Miao, (18.11), p. 590; (18.37)–(18.38), p. 602;
p. 613). With worker surplus `a + λ w` (`λ > 0`) and firm surplus `c − w`, a feasible wage `w`
maximises the Nash product over all feasible wages iff `(1 − η)(a + λ w) = η λ (c − w)`. -/
theorem jd_nash_iff {η a c lam w : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hlam : 0 < lam)
    (hW : 0 ≤ a + lam * w) (hF : 0 ≤ c - w) :
    (∀ w', 0 ≤ a + lam * w' → 0 ≤ c - w' →
      (a + lam * w') ^ η * (c - w') ^ (1 - η) ≤ (a + lam * w) ^ η * (c - w) ^ (1 - η)) ↔
      (1 - η) * (a + lam * w) = η * lam * (c - w) := by
  have h1η : 0 < 1 - η := by linarith
  set K : ℝ := η ^ η * (1 - η) ^ (1 - η) with hK
  -- the Nash product equals `lam^η (x^η y^(1-η))` with `x = (a + lam w)/lam`, `y = c - w`
  have rew : ∀ w', 0 ≤ a + lam * w' → (a + lam * w') ^ η * (c - w') ^ (1 - η)
      = lam ^ η * (((a + lam * w') / lam) ^ η * (c - w') ^ (1 - η)) := by
    intro w' h
    have : a + lam * w' = lam * ((a + lam * w') / lam) := by field_simp
    conv_lhs => rw [this, Real.mul_rpow hlam.le (div_nonneg h hlam.le)]
    ring
  have hS : (a + lam * w) / lam + (c - w) = a / lam + c := by field_simp; ring
  have hsum : ∀ w', (a + lam * w') / lam + (c - w') = a / lam + c := by
    intro w'; field_simp; ring
  have hS0 : 0 ≤ a / lam + c := by rw [← hS]; exact add_nonneg (div_nonneg hW hlam.le) hF
  have hpos : 0 < lam ^ η := Real.rpow_pos_of_pos hlam _
  -- the candidate maximiser
  set w0 : ℝ := c - (1 - η) * (a / lam + c) with hw0
  have hx0 : (a + lam * w0) / lam = η * (a / lam + c) := by
    rw [hw0]; field_simp; ring
  have hW0 : 0 ≤ a + lam * w0 := by
    have : a + lam * w0 = lam * (η * (a / lam + c)) := by rw [← hx0]; field_simp
    rw [this]; exact mul_nonneg hlam.le (mul_nonneg hη0.le hS0)
  have hF0 : 0 ≤ c - w0 := by rw [hw0]; nlinarith
  have hval0 : (a + lam * w0) ^ η * (c - w0) ^ (1 - η) = lam ^ η * (K * (a / lam + c)) := by
    rw [rew w0 hW0]
    congr 1
    rw [← hsum w0]
    refine (jd_nash_eq_iff hη0 hη1 (div_nonneg hW0 hlam.le) hF0).2 ?_
    rw [hx0, hw0]; ring
  have hle : ∀ w', 0 ≤ a + lam * w' → 0 ≤ c - w' →
      (a + lam * w') ^ η * (c - w') ^ (1 - η) ≤ lam ^ η * (K * (a / lam + c)) := by
    intro w' h1 h2
    rw [rew w' h1, ← hsum w']
    exact mul_le_mul_of_nonneg_left (jd_nash_le hη0 hη1 (div_nonneg h1 hlam.le) h2) hpos.le
  have hfoc : (1 - η) * (a + lam * w) = η * lam * (c - w) ↔
      (1 - η) * ((a + lam * w) / lam) = η * (c - w) := by
    constructor
    · intro h; field_simp; linarith
    · intro h; field_simp at h; linarith
  rw [hfoc, ← jd_nash_eq_iff hη0 hη1 (div_nonneg hW hlam.le) hF, hS]
  constructor
  · intro h
    have h1 := h w0 hW0 hF0
    rw [hval0, rew w hW] at h1
    have h2 := hle w hW hF
    rw [rew w hW] at h2
    have h1' := le_of_mul_le_mul_left h1 hpos
    have h2' := le_of_mul_le_mul_left h2 hpos
    rw [← hK]; linarith
  · intro h w' h1 h2
    rw [rew w hW, h, ← hK]
    exact hle w' h1 h2

/-- First-order condition (Miao, pp. 601, 609–611): if `y₀` maximises a function differentiable
at `y₀`, its derivative there is zero. -/
theorem jd_foc {h : ℝ → ℝ} {y₀ d : ℝ} (hmax : ∀ y, h y ≤ h y₀) (hd : HasDerivAt h d y₀) :
    d = 0 :=
  IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmax) hd

/-- Envelope condition (Miao, pp. 609–612): if `g ≤ W` with equality at `x₀` (`g` is the objective
evaluated at the control that is optimal at `x₀`), and both are differentiable at `x₀`, then
`W′(x₀) = g′(x₀)`. -/
theorem jd_envelope {W g : ℝ → ℝ} {x₀ dW dg : ℝ} (hle : ∀ x, g x ≤ W x) (heq : g x₀ = W x₀)
    (hW : HasDerivAt W dW x₀) (hg : HasDerivAt g dg x₀) : dW = dg := by
  have hmin : IsLocalMin (fun x => W x - g x) x₀ :=
    Filter.Eventually.of_forall fun x => by simp only; linarith [hle x]
  have := hmin.hasDerivAt_eq_zero (hW.sub hg)
  linarith

/-- Constant returns to scale (Miao, p. 610, used for (18.51)): if `F` is linearly homogeneous on
the positive quadrant and differentiable in its first argument with partial derivative `F₁`,
then `F₁` is homogeneous of degree zero. -/
theorem jd_partial_homog_one {F F₁ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun x => F x l) (F₁ k l) k)
    {t k l : ℝ} (ht : 0 < t) (hk : 0 < k) (hl : 0 < l) : F₁ (t * k) (t * l) = F₁ k l := by
  have h1 : HasDerivAt (fun x => F (t * x) (t * l)) (F₁ (t * k) (t * l) * t) k := by
    have := (hd (t * k) (t * l) (mul_pos ht hk) (mul_pos ht hl)).comp k
      ((hasDerivAt_id k).const_mul t)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun x => F (t * x) (t * l)) (t * F₁ k l) k := by
    have h3 := (hd k l hk hl).const_mul t
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hk] with x hx
    exact hhom t x l ht hx hl
  have := h1.unique h2
  have ht' : t ≠ 0 := ht.ne'
  have : t * F₁ (t * k) (t * l) = t * F₁ k l := by linarith
  exact mul_left_cancel₀ ht' this

/-- Constant returns to scale, second argument (Miao, p. 613, used for (18.56)): the partial
derivative `F₂` of a linearly homogeneous `F` is homogeneous of degree zero. -/
theorem jd_partial_homog_two {F F₂ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun y => F k y) (F₂ k l) l)
    {t k l : ℝ} (ht : 0 < t) (hk : 0 < k) (hl : 0 < l) : F₂ (t * k) (t * l) = F₂ k l := by
  have h1 : HasDerivAt (fun y => F (t * k) (t * y)) (F₂ (t * k) (t * l) * t) l := by
    have := (hd (t * k) (t * l) (mul_pos ht hk) (mul_pos ht hl)).comp l
      ((hasDerivAt_id l).const_mul t)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun y => F (t * k) (t * y)) (t * F₂ k l) l := by
    have h3 := (hd k l hk hl).const_mul t
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hl] with y hy
    exact hhom t k y ht hk hy
  have := h1.unique h2
  have : t * F₂ (t * k) (t * l) = t * F₂ k l := by linarith
  exact mul_left_cancel₀ ht.ne' this

/-- Solution of the affine recursion `u_{t+1} = a u_t + r` (Miao, (18.43), p. 603): with
`ū = r/(1 − a)`, `u_t − ū = aᵗ (u₀ − ū)`. -/
theorem jd_affine_sol {a r : ℝ} {u : ℕ → ℝ} (ha : a ≠ 1) (hu : ∀ t, u (t + 1) = a * u t + r)
    (t : ℕ) : u t - r / (1 - a) = a ^ t * (u 0 - r / (1 - a)) := by
  have h1a : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hu n, pow_succ]
    have : a * u n + r - r / (1 - a) = a * (u n - r / (1 - a)) := by field_simp; ring
    rw [this, ih]; ring

/-- Monotone adjustment (Miao, p. 607): if `0 ≤ a < 1` and `u₀ ≥ ū`, the solution of
`u_{t+1} = a u_t + r` is nonincreasing and stays above `ū = r/(1 − a)`. -/
theorem jd_affine_antitone {a r : ℝ} {u : ℕ → ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hu : ∀ t, u (t + 1) = a * u t + r) (h0 : r / (1 - a) ≤ u 0) :
    Antitone u ∧ ∀ t, r / (1 - a) ≤ u t := by
  have hsol := jd_affine_sol ha1.ne hu
  have hge : ∀ t, r / (1 - a) ≤ u t := fun t => by
    have := hsol t
    have : 0 ≤ a ^ t * (u 0 - r / (1 - a)) := mul_nonneg (pow_nonneg ha0 t) (by linarith)
    linarith
  refine ⟨antitone_nat_of_succ_le fun t => ?_, hge⟩
  have e1 := hsol t
  have e2 := hsol (t + 1)
  have : a ^ (t + 1) * (u 0 - r / (1 - a)) ≤ a ^ t * (u 0 - r / (1 - a)) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact pow_le_pow_of_le_one ha0 ha1.le (Nat.le_succ t)
  linarith

/-- Convergence (Miao, pp. 595, 607): if `|a| < 1`, the solution of `u_{t+1} = a u_t + r`
converges to `ū = r/(1 − a)`. -/
theorem jd_affine_tendsto {a r : ℝ} {u : ℕ → ℝ} (ha : |a| < 1)
    (hu : ∀ t, u (t + 1) = a * u t + r) : Tendsto u atTop (𝓝 (r / (1 - a))) := by
  have ha1 : a ≠ 1 := by intro h; rw [h] at ha; simp at ha
  have hsol := jd_affine_sol ha1 hu
  have hp : Tendsto (fun t : ℕ => a ^ t * (u 0 - r / (1 - a))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha).mul_const (u 0 - r / (1 - a))
  have : u = fun t => a ^ t * (u 0 - r / (1 - a)) + r / (1 - a) := by
    funext t; linarith [hsol t]
  rw [this]
  simpa using hp.add_const (r / (1 - a))

end Miao.SearchAndMatching
