/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.CurrencyStationary

/-!
# The pure currency economy: differentiability of the value function

SLP §13.5, Exercise 13.5(b) (differentiability), p. 398.

* One-sided derivatives of a concave function on `ℝ₊` (`cvDerivR`, `cvDerivL`, from Mathlib's
  one-sided derivatives of convex functions): existence at `x > 0`, `φ′₊ ≤ φ′₋`, convergence of
  chord slopes, differentiability when they agree (`hasDerivAt_of_cvDerivL_eq`), and the
  one-sided Benveniste–Scheinkman inequalities (`le_cvDerivR_of_le`, `cvDerivL_le_of_le`).
* `cash_envelope_pos` (the envelope condition, Theorem 4.10): where `c(x, z) > 0`, `v(·, z)` is
  differentiable at `x > 0` with `v₁(x, z) = U₁(c(x, z), z)`. This covers the point where the
  cash-in-advance constraint just binds (`c = x`, the book's hint), since `m′ = y` is feasible at
  every `m`.
* `cash_envelope_corner`: where `c(x, z) = 0` the envelope argument fails; there
  `v′₋(x, z) ≤ βW′₋(x + y)` and `βW′₊(x + y) ≤ v′₊(x, z)`.
* `cash_jump_le`, `cashW_hasDerivAt`: the kink `J(x) = W′₋(x) − W′₊(x)` satisfies
  `J(x) = ∫ [v′₋(x, z) − v′₊(x, z)] μ(dz) ≤ βJ(x + y)` and is bounded on `[x, ∞)`, so
  `J(x) ≤ βⁿJ(x + ny) → 0`: `W` is differentiable on `(0, ∞)`.
* **Exercise 13.5(b)** (`ex_13_5b_deriv`, `ex_13_5b_C1`): `v(·, z)` is differentiable on `(0, ∞)`,
  with `v₁ = U₁(c, z)` where `c > 0` and `v₁ = βW′(x + y)` where `c = 0`, and its derivative is
  continuous (`currency_continuousAt_deriv`: the derivative of a differentiable concave function
  is continuous).

**Gap in the book and the manual** (Exercise 13.5(b)). The hint covers the corner `m′ = y`; the
manual applies Theorem 9.10 at interior choices and checks `m′ = y`. Neither covers the other
corner `m′ = m + y` (`c = 0`), which does occur (`ex_13_5e_counterexample`): there Theorem 9.10
does not apply, and differentiability needs the kink-propagation argument above.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-! ### One-sided derivatives of concave functions -/

/-- The right derivative of a concave function, `−(−φ)′₊(x)`. -/
noncomputable def cvDerivR (φ : ℝ → ℝ) (x : ℝ) : ℝ := -derivWithin (-φ) (Ioi x) x

/-- The left derivative of a concave function, `−(−φ)′₋(x)`. -/
noncomputable def cvDerivL (φ : ℝ → ℝ) (x : ℝ) : ℝ := -derivWithin (-φ) (Iio x) x

variable {φ : ℝ → ℝ} {x : ℝ}

/-- `x > 0` is interior to `ℝ₊`. -/
theorem currency_mem_interior_Ici (hx : 0 < x) : x ∈ interior (Ici (0 : ℝ)) := by
  rw [interior_Ici]; exact hx

/-- A concave function on `ℝ₊` has a right derivative at every `x > 0`. -/
theorem hasDerivWithinAt_cvDerivR (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    HasDerivWithinAt φ (cvDerivR φ x) (Ioi x) x := by
  have := (hφ.neg.hasDerivWithinAt_rightDeriv_of_mem_interior (currency_mem_interior_Ici hx)).neg
  simpa [cvDerivR] using this

/-- A concave function on `ℝ₊` has a left derivative at every `x > 0`. -/
theorem hasDerivWithinAt_cvDerivL (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    HasDerivWithinAt φ (cvDerivL φ x) (Iio x) x := by
  have := (hφ.neg.hasDerivWithinAt_leftDeriv_of_mem_interior (currency_mem_interior_Ici hx)).neg
  simpa [cvDerivL] using this

/-- `φ′₊(x) ≤ φ′₋(x)` for concave `φ`. -/
theorem cvDerivR_le_cvDerivL (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    cvDerivR φ x ≤ cvDerivL φ x := by
  have := hφ.neg.leftDeriv_le_rightDeriv_of_mem_interior (currency_mem_interior_Ici hx)
  simp only [cvDerivR, cvDerivL]
  linarith

/-- Right chord slopes at `x` tend to the right derivative. -/
theorem tendsto_slope_cvDerivR (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    Tendsto (slope φ x) (𝓝[>] x) (𝓝 (cvDerivR φ x)) :=
  (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi x) (lt_irrefl x)).1
    (hasDerivWithinAt_cvDerivR hφ hx)

/-- Left chord slopes at `x` tend to the left derivative. -/
theorem tendsto_slope_cvDerivL (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    Tendsto (slope φ x) (𝓝[<] x) (𝓝 (cvDerivL φ x)) :=
  (hasDerivWithinAt_iff_tendsto_slope' (s := Iio x) (lt_irrefl x)).1
    (hasDerivWithinAt_cvDerivL hφ hx)

/-- `(φ(x + s) − φ(x))/s → φ′₊(x)` as `s ↓ 0`. -/
theorem currency_tendsto_slope_right (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    Tendsto (fun s => slope φ x (x + s)) (𝓝[>] 0) (𝓝 (cvDerivR φ x)) := by
  refine (tendsto_slope_cvDerivR hφ hx).comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have : Tendsto (fun s : ℝ => x + s) (𝓝 0) (𝓝 (x + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs ⊢
    linarith

/-- `(φ(x) − φ(x − s))/s → φ′₋(x)` as `s ↓ 0`. -/
theorem currency_tendsto_slope_left (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) :
    Tendsto (fun s => slope φ x (x - s)) (𝓝[>] 0) (𝓝 (cvDerivL φ x)) := by
  refine (tendsto_slope_cvDerivL hφ hx).comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have : Tendsto (fun s : ℝ => x - s) (𝓝 0) (𝓝 (x - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi, mem_Iio] at hs ⊢
    linarith

/-- If both one-sided derivatives agree, `φ` is differentiable. -/
theorem hasDerivAt_of_cvDerivL_eq (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x)
    (h : cvDerivL φ x = cvDerivR φ x) :
    HasDerivAt φ (cvDerivR φ x) x :=
  hasDerivAt_iff_tendsto_slope_left_right.2
    ⟨h ▸ tendsto_slope_cvDerivL hφ hx, tendsto_slope_cvDerivR hφ hx⟩

/-- **Benveniste–Scheinkman, right side.** If `V ≤ φ` on `(x, x + δ)`, `V(x) = φ(x)` and `V` has
right derivative `a` at `x`, then `a ≤ φ′₊(x)`. -/
theorem le_cvDerivR_of_le (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) {V : ℝ → ℝ} {a δ : ℝ}
    (hδ : 0 < δ) (hV : HasDerivWithinAt V a (Ioi x) x) (hVx : V x = φ x)
    (hle : ∀ t, x < t → t < x + δ → V t ≤ φ t) : a ≤ cvDerivR φ x := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi x) (lt_irrefl x)).1 hV
  refine le_of_tendsto_of_tendsto h1 (tendsto_slope_cvDerivR hφ hx) ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : x < x + δ)] with t ht
  rw [slope_def_field, slope_def_field, hVx]
  exact div_le_div_of_nonneg_right (by linarith [hle t ht.1 ht.2]) (by linarith [ht.1])

/-- **Benveniste–Scheinkman, left side.** If `V ≤ φ` on `(x − δ, x)`, `V(x) = φ(x)` and `V` has
left derivative `a` at `x`, then `φ′₋(x) ≤ a`. -/
theorem cvDerivL_le_of_le (hφ : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x) {V : ℝ → ℝ} {a δ : ℝ}
    (hδ : 0 < δ) (hV : HasDerivWithinAt V a (Iio x) x) (hVx : V x = φ x)
    (hle : ∀ t, x - δ < t → t < x → V t ≤ φ t) : cvDerivL φ x ≤ a := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope' (s := Iio x) (lt_irrefl x)).1 hV
  refine le_of_tendsto_of_tendsto (tendsto_slope_cvDerivL hφ hx) h1 ?_
  filter_upwards [Ioo_mem_nhdsLT (by linarith : x - δ < x)] with t ht
  rw [slope_def_field, slope_def_field, hVx]
  exact div_le_div_of_nonpos_of_le (by linarith [ht.2]) (by linarith [hle t ht.1 ht.2])

/-- For concave nondecreasing `φ` with `|φ| ≤ C` on `ℝ₊` and `0 < s ≤ x/2`, the left and right
difference quotients at `x` satisfy `0 ≤ right ≤ left ≤ 4C/x`. -/
theorem currency_concave_slopes_bound (hφ : ConcaveOn ℝ (Ici 0) φ) (hm : MonotoneOn φ (Ici 0))
    {C : ℝ}
    (hC : ∀ t, 0 ≤ t → |φ t| ≤ C) (hx : 0 < x) {s : ℝ} (hs : 0 < s) (hsx : s ≤ x / 2) :
    0 ≤ slope φ x (x + s) ∧ slope φ x (x + s) ≤ slope φ x (x - s) ∧
      slope φ x (x - s) ≤ 4 * C / x := by
  have e1 : slope φ x (x + s) = s⁻¹ * (φ (x + s) - φ x) := by
    rw [slope_def_field, show x + s - x = s by ring, div_eq_inv_mul]
  have e2 : slope φ x (x - s) = s⁻¹ * (φ x - φ (x - s)) := by
    rw [slope_def_field, show x - s - x = -s by ring, div_neg, ← neg_div, neg_sub,
      div_eq_inv_mul]
  rw [e1, e2]
  have hsi : 0 < s⁻¹ := inv_pos.2 hs
  have hmono : φ x ≤ φ (x + s) := hm (mem_Ici.2 hx.le) (mem_Ici.2 (by linarith)) (by linarith)
  have hex := currency_concave_exchange hφ (p := x - s) (q := x) (r := x) (t := x + s)
    (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith) (by linarith) (by ring)
  have hsl := currency_concave_left_slope_le hφ (a := x) hs hsx (by linarith)
  have h1 := abs_le.1 (hC x hx.le)
  have h2 := abs_le.1 (hC (x - x / 2) (by linarith))
  refine ⟨mul_nonneg hsi.le (by linarith), mul_le_mul_of_nonneg_left (by linarith) hsi.le,
    hsl.trans ?_⟩
  rw [show (x / 2)⁻¹ = 2 / x by field_simp]
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx]
  nlinarith

/-! ### The value function -/

variable {U U1 : ℝ → ℝ → ℝ} {β y zl zh : ℝ}

/-- `m ↦ v(m, z)`, extended to `ℝ` (by `0` off `ℝ₊`). -/
noncomputable def cashV (v : Ici (0 : ℝ) × Icc zl zh → ℝ) (z : Icc zl zh) : ℝ → ℝ :=
  liftS fun m : Ici (0 : ℝ) => v (m, z)

/-- On `ℝ₊`, `cashV v z m = v(m, z)`. -/
theorem cashV_of_mem (v : Ici (0 : ℝ) × Icc zl zh → ℝ) (z : Icc zl zh) (m : Ici (0 : ℝ)) :
    cashV v z m = v (m, z) :=
  liftS_of_mem _ m.2

variable (μ : Measure (Icc zl zh)) [IsProbabilityMeasure μ]

/-- `v(·, z)` is concave on `ℝ₊` (part (b)). -/
theorem cashV_concave (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    ConcaveOn ℝ (Ici 0) (cashV v z) :=
  concaveOn_liftS (cash_concave μ h hv z)

/-- `v(·, z)` is nondecreasing on `ℝ₊` (part (b)). -/
theorem cashV_mono (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    MonotoneOn (cashV v z) (Ici 0) := fun a ha b hb hab => by
  rw [show cashV v z a = cashV v z ((⟨a, ha⟩ : Ici (0 : ℝ)) : ℝ) from rfl,
    show cashV v z b = cashV v z ((⟨b, hb⟩ : Ici (0 : ℝ)) : ℝ) from rfl, cashV_of_mem,
    cashV_of_mem]
  exact (cash_strictMono μ h hv z).monotone (show (⟨a, ha⟩ : Ici (0 : ℝ)) ≤ ⟨b, hb⟩ from hab)

omit [IsProbabilityMeasure μ] in
/-- `|v| ≤ ‖v‖`. -/
theorem abs_cashV_le (v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ) (z : Icc zl zh) (t : ℝ) :
    |cashV v z t| ≤ ‖v‖ := by
  by_cases ht : t ∈ Ici (0 : ℝ)
  · rw [show cashV v z t = cashV v z ((⟨t, ht⟩ : Ici (0 : ℝ)) : ℝ) from rfl, cashV_of_mem,
      ← Real.norm_eq_abs]
    exact v.norm_coe_le_norm _
  · simp only [cashV, liftS, ht, ↓reduceDIte, abs_zero]
    exact norm_nonneg _

/-- `W` is concave on `ℝ₊`. -/
theorem cashW_concave (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    ConcaveOn ℝ (Ici 0) (cashW μ v) :=
  (cashW_strictConcave μ h hv).concaveOn

/-- `cashV` at a real point: the Bellman equation (1). -/
theorem cashV_spec (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) {m : ℝ}
    (hm : 0 ≤ m) :
    cashV v z m = U (m + y - cashPolicy μ U β y v (⟨m, mem_Ici.2 hm⟩, z)) z +
        β * cashW μ v (cashPolicy μ U β y v (⟨m, mem_Ici.2 hm⟩, z)) ∧
      ∀ x' : ℝ, y ≤ x' → x' ≤ m + y → U (m + y - x') z + β * cashW μ v x' ≤ cashV v z m := by
  have := cashPolicy_spec μ h hv (⟨m, mem_Ici.2 hm⟩, z)
  rw [show cashV v z m = cashV v z ((⟨m, mem_Ici.2 hm⟩ : Ici (0 : ℝ)) : ℝ) from rfl,
    cashV_of_mem]
  exact ⟨this.2.2.1, this.2.2.2⟩

/-- **The envelope condition where consumption is positive.** If `c(x, z) > 0` (this includes the
point where the cash-in-advance constraint just binds, `c = x`), then `v(·, z)` is differentiable
at `x > 0` with derivative `U₁(c(x, z), z)`: the choice `g(x, z)` stays feasible near `x`, so
`U(m + y − g, z) + βW(g) ≤ v(m, z)` with equality at `x` (Theorem 4.10). -/
theorem cash_envelope_pos (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) {x : ℝ}
    (hx : 0 < x)
    (hc : 0 < x + y - cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z)) :
    HasDerivAt (cashV v z) (U1 (x + y - cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z)) z) x ∧
      cvDerivR (cashV v z) x = U1 (x + y - cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z)) z ∧
      cvDerivL (cashV v z) x = cvDerivR (cashV v z) x := by
  set g := (cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z) : ℝ)
  have hφ := cashV_concave μ h hv z
  have hg := (cashPolicy_spec μ h hv (⟨x, mem_Ici.2 hx.le⟩, z)).1
  set V : ℝ → ℝ := fun m => U (m + (y - g)) z + β * cashW μ v g
  have hV : HasDerivAt V (U1 (x + y - g) z) x := by
    have h1 := hd.deriv z z.2 (x + (y - g)) (by linarith)
    have h2 := (h1.comp x ((hasDerivAt_id x).add_const (y - g))).add_const (β * cashW μ v g)
    simp only [mul_one] at h2
    rw [show x + y - g = x + (y - g) by ring]
    exact h2
  have hVx : V x = cashV v z x := by
    simp only [V]
    rw [(cashV_spec μ h hv z hx.le).1, show x + (y - g) = x + y - g by ring]
  have hle : ∀ t, g - y < t → V t ≤ cashV v z t := fun t ht => by
    have := (cashV_spec μ h hv z (show 0 ≤ t by linarith)).2 g hg (by linarith)
    simp only [V]
    rw [show t + (y - g) = t + y - g by ring]
    exact this
  have hR := le_cvDerivR_of_le hφ hx one_pos hV.hasDerivWithinAt hVx fun t ht _ =>
    hle t (by linarith)
  have hL := cvDerivL_le_of_le hφ hx hc hV.hasDerivWithinAt hVx fun t ht _ => hle t (by linarith)
  have hRL := cvDerivR_le_cvDerivL hφ hx
  have heq : cvDerivR (cashV v z) x = U1 (x + y - g) z := le_antisymm (by linarith) hR
  have heqL : cvDerivL (cashV v z) x = cvDerivR (cashV v z) x := by linarith
  refine ⟨?_, heq, heqL⟩
  rw [← heq]
  exact hasDerivAt_of_cvDerivL_eq hφ hx heqL

/-- **At a corner `c(x, z) = 0`** (all money saved), `v(m, z) ≥ U(0, z) + βW(m + y)` with
equality at `x`, so `v′₋(x, z) ≤ βW′₋(x + y)` and `βW′₊(x + y) ≤ v′₊(x, z)`. -/
theorem cash_envelope_corner (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) {x : ℝ}
    (hx : 0 < x) (hc : (cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z) : ℝ) = x + y) :
    cvDerivL (cashV v z) x ≤ β * cvDerivL (cashW μ v) (x + y) ∧
      β * cvDerivR (cashW μ v) (x + y) ≤ cvDerivR (cashV v z) x := by
  have hφ := cashV_concave μ h hv z
  have hW := cashW_concave μ h hv
  have hy := h.y_pos
  set V : ℝ → ℝ := fun m => U 0 z + β * cashW μ v (m + y)
  have hVx : V x = cashV v z x := by
    simp only [V]
    rw [(cashV_spec μ h hv z hx.le).1, hc, show x + y - (x + y) = 0 by ring]
  have hle : ∀ t, 0 ≤ t → V t ≤ cashV v z t := fun t ht => by
    have := (cashV_spec μ h hv z ht).2 (t + y) (by linarith) le_rfl
    simp only [V]
    rwa [show t + y - (t + y) = 0 by ring] at this
  have hshift : HasDerivAt (fun m : ℝ => m + y) 1 x := (hasDerivAt_id x).add_const y
  have hVR : HasDerivWithinAt V (β * cvDerivR (cashW μ v) (x + y)) (Ioi x) x := by
    have h1 := ((hasDerivWithinAt_cvDerivR hW (by linarith : 0 < x + y)).comp x
      (hshift.hasDerivWithinAt (s := Ioi x))
      (fun t ht => by simp only [mem_Ioi] at ht ⊢; linarith)).const_mul β
    simp only [mul_one] at h1
    exact h1.const_add (U 0 z)
  have hVL : HasDerivWithinAt V (β * cvDerivL (cashW μ v) (x + y)) (Iio x) x := by
    have h1 := ((hasDerivWithinAt_cvDerivL hW (by linarith : 0 < x + y)).comp x
      (hshift.hasDerivWithinAt (s := Iio x))
      (fun t ht => by simp only [mem_Iio] at ht ⊢; linarith)).const_mul β
    simp only [mul_one] at h1
    exact h1.const_add (U 0 z)
  exact ⟨cvDerivL_le_of_le hφ hx hx hVL hVx fun t ht _ => hle t (by linarith),
    le_cvDerivR_of_le hφ hx one_pos hVR hVx fun t ht _ => hle t (by linarith)⟩

/-- **The kink inequality.** The jump `J(x) = W′₋(x) − W′₊(x)` satisfies `J(x) ≤ βJ(x + y)`:
`J(x) = ∫ [v′₋(x, z) − v′₊(x, z)] μ(dz)` (dominated convergence of difference quotients), the
jump of `v(·, z)` at `x` vanishes where `c(x, z) > 0` (`cash_envelope_pos`) and is at most
`βJ(x + y)` where `c(x, z) = 0` (`cash_envelope_corner`). -/
theorem cash_jump_le (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {x : ℝ} (hx : 0 < x) :
    cvDerivL (cashW μ v) x - cvDerivR (cashW μ v) x ≤
      β * (cvDerivL (cashW μ v) (x + y) - cvDerivR (cashW μ v) (x + y)) := by
  have hW := cashW_concave μ h hv
  have hy := h.y_pos
  have hβ := h.β_pos
  set J := cvDerivL (cashW μ v) (x + y) - cvDerivR (cashW μ v) (x + y)
  have hJ0 : 0 ≤ J := sub_nonneg.2 (cvDerivR_le_cvDerivL hW (by linarith))
  set jump : Icc zl zh → ℝ := fun z => cvDerivL (cashV v z) x - cvDerivR (cashV v z) x
  have hjump : ∀ z, 0 ≤ jump z ∧ jump z ≤ β * J := fun z => by
    have hφ := cashV_concave μ h hv z
    refine ⟨sub_nonneg.2 (cvDerivR_le_cvDerivL hφ hx), ?_⟩
    obtain ⟨hg1, hg2, -, -⟩ := cashPolicy_spec μ h hv (⟨x, mem_Ici.2 hx.le⟩, z)
    dsimp only at hg2
    rcases (sub_nonneg.2 hg2).eq_or_lt with hc0 | hcpos
    · have hc : (cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z) : ℝ) = x + y := by linarith
      obtain ⟨h1, h2⟩ := cash_envelope_corner μ h hv z hx hc
      simp only [jump, J]
      nlinarith
    · have heqL := (cash_envelope_pos μ h hd hv z hx hcpos).2.2
      simp only [jump]
      rw [heqL, sub_self]
      exact mul_nonneg hβ.le hJ0
  -- the difference quotients
  have hcz : ∀ t, 0 ≤ t → Continuous fun z => cashV v z t := fun t ht => by
    have : (fun z => cashV v z t) = fun z => v (⟨t, ht⟩, z) :=
      funext fun z => cashV_of_mem v z ⟨t, ht⟩
    rw [this]
    exact v.continuous.comp (Continuous.prodMk_right _)
  have hint : ∀ t, 0 ≤ t → Integrable (fun z => cashV v z t) μ := fun t ht => by
    have : (fun z => cashV v z t) = fun z => v (⟨t, ht⟩, z) :=
      funext fun z => cashV_of_mem v z ⟨t, ht⟩
    rw [this]
    exact integrable_section_v μ v _
  have hWint : ∀ t, 0 ≤ t → cashW μ v t = ∫ z, cashV v z t ∂μ := fun t ht => by
    rw [show cashW μ v t = cashW μ v ((⟨t, ht⟩ : Ici (0 : ℝ)) : ℝ) from rfl, cashW_of_mem]
    exact integral_congr_ae (Eventually.of_forall fun z => (cashV_of_mem v z ⟨t, ht⟩).symm)
  have hslope : ∀ t, 0 ≤ t → ∫ z, slope (cashV v z) x t ∂μ = slope (cashW μ v) x t :=
    fun t ht => by
      simp only [slope_def_field]
      rw [integral_div, integral_sub (hint t ht) (hint x hx.le), hWint t ht, hWint x hx.le]
  set F : ℝ → Icc zl zh → ℝ := fun s z =>
    slope (cashV v z) x (x - s) - slope (cashV v z) x (x + s)
  have hlimF : ∀ z, Tendsto (fun s => F s z) (𝓝[>] 0) (𝓝 (jump z)) := fun z =>
    (currency_tendsto_slope_left (cashV_concave μ h hv z) hx).sub
      (currency_tendsto_slope_right (cashV_concave μ h hv z) hx)
  have hDCT : Tendsto (fun s => ∫ z, F s z ∂μ) (𝓝[>] 0) (𝓝 (∫ z, jump z ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4 * ‖v‖ / x) ?_ ?_
      (integrable_const _) (Eventually.of_forall hlimF)
    · filter_upwards [Ioc_mem_nhdsGT (show 0 < x / 2 by linarith)] with s hs
      have : F s = fun z => (cashV v z (x - s) - cashV v z x) / (x - s - x) -
          (cashV v z (x + s) - cashV v z x) / (x + s - x) := by
        funext z; simp only [F, slope_def_field]
      rw [this]
      exact (((((hcz _ (by linarith [hs.2])).sub (hcz x hx.le)).div_const _).sub
        (((hcz _ (by linarith [hs.1])).sub (hcz x hx.le)).div_const _))).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show 0 < x / 2 by linarith)] with s hs
      refine Eventually.of_forall fun z => ?_
      have hb := currency_concave_slopes_bound (cashV_concave μ h hv z) (cashV_mono μ h hv z)
        (fun t _ => abs_cashV_le v z t) hx hs.1 hs.2
      rw [Real.norm_eq_abs, abs_le]
      simp only [F]
      constructor <;> linarith [hb.1, hb.2.1, hb.2.2]
  have hlimW : Tendsto (fun s => ∫ z, F s z ∂μ) (𝓝[>] 0)
      (𝓝 (cvDerivL (cashW μ v) x - cvDerivR (cashW μ v) x)) := by
    refine ((currency_tendsto_slope_left hW hx).sub (currency_tendsto_slope_right hW hx)).congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hx] with s hs
    simp only [F]
    rw [integral_sub ?_ ?_, hslope _ (by linarith [hs.2]), hslope _ (by linarith [hs.1])]
    · simp only [slope_def_field]
      exact ((hint _ (by linarith [hs.2])).sub (hint x hx.le)).div_const _
    · simp only [slope_def_field]
      exact ((hint _ (by linarith [hs.1])).sub (hint x hx.le)).div_const _
  rw [tendsto_nhds_unique hlimW hDCT]
  have := integral_mono_of_nonneg (Eventually.of_forall fun z => (hjump z).1)
    (integrable_const (μ := μ) (β * J)) (Eventually.of_forall fun z => (hjump z).2)
  rw [integral_const, probReal_univ, one_smul] at this
  exact this

/-- **`W` is differentiable on `(0, ∞)`.** The jump `J(x) = W′₋(x) − W′₊(x) ≥ 0` satisfies
`J(x) ≤ βJ(x + y) ≤ … ≤ βⁿJ(x + ny)`, and `J ≤ 4‖v‖/x` on `[x, ∞)` (the left derivative is at
most a chord slope, the right derivative is nonnegative), so `J(x) = 0`. -/
theorem cashW_hasDerivAt (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cashW μ v) (cvDerivR (cashW μ v) x) x := by
  have hW := cashW_concave μ h hv
  have hy := h.y_pos
  have hβ := h.β_pos
  set J : ℝ → ℝ := fun t => cvDerivL (cashW μ v) t - cvDerivR (cashW μ v) t
  have hJ0 : ∀ t, 0 < t → 0 ≤ J t := fun t ht => sub_nonneg.2 (cvDerivR_le_cvDerivL hW ht)
  have hJb : ∀ t, x ≤ t → J t ≤ 4 * ‖v‖ / x := fun t ht => by
    have ht0 : 0 < t := hx.trans_le ht
    have hL := hW.le_slope_of_hasDerivWithinAt_Iio (mem_Ici.2 (by linarith : (0 : ℝ) ≤ t - x / 2))
      (mem_Ici.2 ht0.le) (by linarith) (hasDerivWithinAt_cvDerivL hW ht0)
    have hR := hW.slope_le_of_hasDerivWithinAt_Ioi (mem_Ici.2 ht0.le)
      (mem_Ici.2 (by linarith : (0 : ℝ) ≤ t + 1)) (by linarith) (hasDerivWithinAt_cvDerivR hW ht0)
    rw [slope_def_field] at hL hR
    have hm := cashW_mono μ h hv ht0.le (by linarith : t ≤ t + 1)
    have h1 := abs_le.1 (abs_cashW_le μ v t)
    have h2 := abs_le.1 (abs_cashW_le μ v (t - x / 2))
    rw [show t - (t - x / 2) = x / 2 by ring] at hL
    rw [show t + 1 - t = 1 by ring, div_one] at hR
    have hL' : cvDerivL (cashW μ v) t ≤ 4 * ‖v‖ / x := by
      refine hL.trans ?_
      rw [div_le_div_iff₀ (by linarith) hx]
      nlinarith
    simp only [J]
    linarith
  have hiter : ∀ n : ℕ, J x ≤ β ^ n * J (x + n * y) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have := cash_jump_le μ h hd hv (x := x + n * y) (by positivity)
      have e : x + n * y + y = x + ((n + 1 : ℕ) : ℝ) * y := by push_cast; ring
      rw [e] at this
      calc J x ≤ β ^ n * J (x + n * y) := ih
        _ ≤ β ^ n * (β * J (x + ((n + 1 : ℕ) : ℝ) * y)) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hβ.le n)
        _ = β ^ (n + 1) * J (x + ((n + 1 : ℕ) : ℝ) * y) := by ring
  have hbound : ∀ n : ℕ, J x ≤ β ^ n * (4 * ‖v‖ / x) := fun n =>
    (hiter n).trans (mul_le_mul_of_nonneg_left (hJb _ (by
      have : (0 : ℝ) ≤ n * y := by positivity
      linarith)) (pow_nonneg hβ.le n))
  have hlim : Tendsto (fun n : ℕ => β ^ n * (4 * ‖v‖ / x)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le h.β_lt).mul_const (4 * ‖v‖ / x)
  have hJx : J x ≤ 0 := ge_of_tendsto' hlim hbound
  exact hasDerivAt_of_cvDerivL_eq hW hx (by have := hJ0 x hx; simp only [J] at hJx this; linarith)

/-- **Exercise 13.5(b)** (differentiability). For every `z` and `x > 0`, `v(·, z)` is
differentiable at `x`: where `c(x, z) > 0` with `v₁(x, z) = U₁(c(x, z), z)` (the envelope
condition; this covers the point where the cash-in-advance constraint just binds, the book's
hint), and where `c(x, z) = 0` with `v₁(x, z) = βW′(x + y)`. -/
theorem ex_13_5b_deriv (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (cashV v z) (cvDerivR (cashV v z) x) x ∧
      (0 < x + y - cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z) →
        cvDerivR (cashV v z) x = U1 (x + y - cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z)) z) ∧
      ((cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z) : ℝ) = x + y →
        cvDerivR (cashV v z) x = β * cvDerivR (cashW μ v) (x + y)) := by
  have hφ := cashV_concave μ h hv z
  have hy := h.y_pos
  have hcorner : (cashPolicy μ U β y v (⟨x, mem_Ici.2 hx.le⟩, z) : ℝ) = x + y →
      cvDerivL (cashV v z) x = cvDerivR (cashV v z) x ∧
        cvDerivR (cashV v z) x = β * cvDerivR (cashW μ v) (x + y) :=
    fun hc => by
      obtain ⟨h1, h2⟩ := cash_envelope_corner μ h hv z hx hc
      have hWd := cashW_hasDerivAt μ h hd hv (x := x + y) (by linarith)
      have hLR : cvDerivL (cashW μ v) (x + y) = cvDerivR (cashW μ v) (x + y) := by
        have e1 := (hasDerivWithinAt_cvDerivL (cashW_concave μ h hv) (by linarith : 0 < x + y))
        exact e1.derivWithin (uniqueDiffWithinAt_Iio _) ▸
          (hWd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio _))
      have h3 := cvDerivR_le_cvDerivL hφ hx
      rw [hLR] at h1
      constructor <;> nlinarith
  refine ⟨?_, fun hc => (cash_envelope_pos μ h hd hv z hx hc).2.1, fun hc => (hcorner hc).2⟩
  obtain ⟨hg1, hg2, -, -⟩ := cashPolicy_spec μ h hv (⟨x, mem_Ici.2 hx.le⟩, z)
  dsimp only at hg2
  rcases (sub_nonneg.2 hg2).eq_or_lt with hc0 | hcpos
  · exact hasDerivAt_of_cvDerivL_eq hφ hx (hcorner (by linarith)).1
  · exact hasDerivAt_of_cvDerivL_eq hφ hx (cash_envelope_pos μ h hd hv z hx hcpos).2.2

/-- **The derivative of a differentiable concave function is continuous.** For `t > a`,
`slope φ t (2t − a) ≤ φ′(t) ≤ slope φ a t`, and for `a/2 < t < a`,
`slope φ t a ≤ φ′(t) ≤ slope φ (2t − a) t`; all four chord slopes tend to `φ′(a)`. -/
theorem currency_continuousAt_deriv {φ D : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ)
    (hD : ∀ t, 0 < t → HasDerivAt φ (D t) t) {a : ℝ} (ha : 0 < a) : ContinuousAt D a := by
  have hS : Tendsto (slope φ a) (𝓝[≠] a) (𝓝 (D a)) := hasDerivAt_iff_tendsto_slope.1 (hD a ha)
  have hmap : ∀ {l : Filter ℝ}, l ≤ 𝓝 a → (∀ᶠ t in l, t ≠ a) →
      Tendsto (fun t => 2 * t - a) l (𝓝[≠] a) := fun {l} hl hne => by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 2 * t - a) (𝓝 a) (𝓝 (2 * a - a)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto a
      rw [show 2 * a - a = a by ring] at this
      exact this.mono_left hl
    · filter_upwards [hne] with t ht
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      exact ht (by linarith)
  have hS2 : ∀ {l : Filter ℝ}, l ≤ 𝓝 a → (∀ᶠ t in l, t ≠ a) →
      Tendsto (fun t => 2 * slope φ a (2 * t - a) - slope φ a t) l (𝓝 (D a)) :=
    fun {l} hl hne => by
      have h1 := (hS.comp (hmap hl hne)).const_mul 2
      have h2 := hS.mono_left (le_inf hl (le_principal_iff.2 hne) : l ≤ 𝓝[≠] a)
      have := h1.sub h2
      rw [show 2 * D a - D a = D a by ring] at this
      exact this
  have hR : Tendsto D (𝓝[>] a) (𝓝 (D a)) := by
    have hne : ∀ᶠ t in 𝓝[>] a, t ≠ a := by
      filter_upwards [self_mem_nhdsWithin] with t ht using ne_of_gt ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hS2 nhdsWithin_le_nhds hne)
      (hS.mono_left (nhdsGT_le_nhdsNE a)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : a < t := ht
      have := hφ.slope_le_of_hasDerivAt (mem_Ici.2 (by linarith : (0 : ℝ) ≤ t))
        (mem_Ici.2 (by linarith : (0 : ℝ) ≤ 2 * t - a)) (by linarith) (hD t (by linarith))
      have e : slope φ t (2 * t - a) = 2 * slope φ a (2 * t - a) - slope φ a t := by
        simp only [slope_def_field]
        have h1 : t - a ≠ 0 := by linarith
        have h2 : 2 * t - a - a ≠ 0 := by linarith
        have h3 : 2 * t - a - t ≠ 0 := by linarith
        field_simp
        ring
      rw [← e]
      exact this
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : a < t := ht
      exact hφ.le_slope_of_hasDerivAt (mem_Ici.2 ha.le) (mem_Ici.2 (by linarith)) ht'
        (hD t (by linarith))
  have hL : Tendsto D (𝓝[<] a) (𝓝 (D a)) := by
    have hne : ∀ᶠ t in 𝓝[<] a, t ≠ a := by
      filter_upwards [self_mem_nhdsWithin] with t ht using ne_of_lt ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hS.mono_left (nhdsLT_le_nhdsNE a))
      (hS2 nhdsWithin_le_nhds hne) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (by linarith : a / 2 < a)] with t ht
      have := hφ.slope_le_of_hasDerivAt (mem_Ici.2 (by linarith [ht.1] : (0 : ℝ) ≤ t))
        (mem_Ici.2 ha.le) ht.2 (hD t (by linarith [ht.1]))
      rw [slope_comm] at this
      exact this
    · filter_upwards [Ioo_mem_nhdsLT (by linarith : a / 2 < a)] with t ht
      have := hφ.le_slope_of_hasDerivAt (mem_Ici.2 (by linarith [ht.1] : (0 : ℝ) ≤ 2 * t - a))
        (mem_Ici.2 (by linarith [ht.1] : (0 : ℝ) ≤ t)) (by linarith [ht.2])
        (hD t (by linarith [ht.1]))
      have e : slope φ (2 * t - a) t = 2 * slope φ a (2 * t - a) - slope φ a t := by
        simp only [slope_def_field]
        have h1 : t - a ≠ 0 := by linarith [ht.2]
        have h2 : 2 * t - a - a ≠ 0 := by linarith [ht.2]
        have h3 : t - (2 * t - a) ≠ 0 := by linarith [ht.2]
        field_simp
        ring
      rw [← e]
      exact this
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, ← nhdsLT_sup_nhdsGT]
  exact hL.sup hR

/-- **Exercise 13.5(b)** (continuous differentiability). `v(·, z)` is continuously differentiable
on `(0, ∞)`: it is differentiable there (`ex_13_5b_deriv`) and concave, and the derivative of a
differentiable concave function is continuous. -/
theorem ex_13_5b_C1 (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    (∀ x, 0 < x → HasDerivAt (cashV v z) (cvDerivR (cashV v z) x) x) ∧
      ContinuousOn (cvDerivR (cashV v z)) (Ioi 0) := by
  have hD : ∀ x, 0 < x → HasDerivAt (cashV v z) (cvDerivR (cashV v z) x) x := fun x hx =>
    (ex_13_5b_deriv μ h hd hv z hx).1
  exact ⟨hD, fun x hx => (currency_continuousAt_deriv (cashV_concave μ h hv z) hD
    hx).continuousWithinAt⟩

end StokeyLucasPrescott.ConvergenceApplications
