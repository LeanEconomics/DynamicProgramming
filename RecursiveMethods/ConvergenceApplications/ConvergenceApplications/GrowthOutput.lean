/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.GrowthPolicy

/-!
# The one-sector model of optimal growth with output as the state

SLP §13.3, pp. 391–393: `v(x) = max_{0 ≤ y ≤ x} [U(x − y) + β ∫ v(f(y) z) μ(dz)]` (1) on
`X = [0, x̄]`, with i.i.d. shocks `z ~ μ` on `Z = [1, z̄]`.

* **NOTEs on `x̄`** (p. 392): `x̄` is unique (`xbar_unique`: `z̄ f(x) − x` is concave and
  positive at `0`), but need not exist (`xbar_counterexample`, below); `modifiedT2_of_concave`
  checks the modified (T2) for concave `f`.
* **The operator** (a direct contraction on `C(X)`; the §9.2 machinery would carry a spurious
  shock coordinate): `OutputHyp` (the primitives), `outNext` (`f(y) z′ ∈ X`), `outObj`, `outT`
  (continuous by the Theorem of the Maximum), `exists_outT_argmax`, `outT_mono`,
  `outT_add_const`, `outT_contraction` (Blackwell), `SolvesOut` (equation (1) with `max`) and
  `outT_eq_iff` (fixed points of `T` = bounded continuous solutions of (1)).
* **Exercise 13.3a**: `ex_13_3a_exists` (existence, uniqueness, `Tⁿv₀ → v` at rate `βⁿ`),
  `outT_strictMono` (`Tw` is strictly increasing for every `w`), `outT_concave`,
  `out_concave`, `out_flat_step`, `out_strictConcave` and `ex_13_3a`. Assumption 9.10 fails
  (`U(x − y)` is not strictly concave jointly, and `f` is only concave), so strict concavity is
  proved by the chord argument of `growth_strictConcave`: on a chord where `v` were affine,
  consumption is constant and the chord is carried to chords `[f(y_a) z, f(y_b) z]` on which `v`
  is affine, with rise `β` times as large; the supremum `S` of the rises satisfies `S ≤ βS`.
* **Exercise 13.3b**: `out_W_strictConcave`, `out_uniqueArgmax`, `outPolicy` and `ex_13_3b`
  (the policy is a continuous nondecreasing function with `g(0) = 0`, and consumption is
  nondecreasing); `out_consumption_strictMono` (consumption is strictly increasing where it is
  positive, for `U` differentiable on `(0, ∞)`).
* **Exercise 13.3c**: `ex_13_3c` (`v′(x) = U′(x − g(x))` at interior `x` with `x − g(x) > 0`,
  by Benveniste–Scheinkman, Theorem 4.10) and `ex_13_3c_continuous` (the derivative is
  continuous there if `U′` is).

**Corrections.**
* **Existence of `x̄`** (NOTE p. 392). The modified (T2) controls `f(x) − x`, not `z̄ f(x) − x`.
  With `f(x) = 1 + 0.9x + 2(1 − e^{−x})`, `β = 1/2`, `z̄ = 2`: `f` is continuous, strictly
  increasing, concave, `C¹`, `f(0) = 1`, `βf′(0) = 1.45 > 1`, the modified (T2) holds, but
  `z̄ f(x) > x` for all `x ≥ 0` (`xbar_counterexample`, `noXbarF_T2`).
* **Exercise 13.3b.** "`0 < g(x) < x` for `0 < x ≤ x̄`" and "`g` strictly increasing" are false.
  With `U(c) = 1 − e^{−20c}`, `f(y) = 5/6 + 2y/(1 + y)`, `β = 3/4`, `z̄ = 2`, `x̄ = 5 = 2 f(5)` —
  which satisfy every assumption of §13.3 (`cexOut_hyp`, `cexOutU_props`, `cexOutF_props`,
  `cexOutF_T2`), with `U` `C¹` on `[0, ∞)` (no Inada condition) and `βf′(0) = 3/2 > 1` — and
  *any* `μ` (so also those satisfying (Z3)), the only optimal choice at `x ≤ 1/100` is `y = 0`
  (`ex_13_3b_counterexample`, `ex_13_3b_not_strictMono`). The proof bounds the marginal value of
  saving by concavity: `v(s′) − v(s) ≤ (24/5)(s′ − s)` on outputs `s ≥ f(0)`
  (`cexOut_lipschitz`, from `0 ≤ v ≤ 4`, `cexOut_bounds`). So the corner does not need an Inada
  condition (the NOTE's diagnosis): the claim fails under the book's own assumptions. The
  corrected statement (`ex_13_3b`) has `g` nondecreasing and `0 ≤ g(x) ≤ x`; consumption is
  strictly increasing only where it is positive (`out_consumption_strictMono`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-! ### The NOTEs on `x̄` -/

/-- **Uniqueness of `x̄`** (NOTE p. 392). If `f` is concave on `[0, ∞)` with `f(0) > 0` and
`z̄ > 0`, then `z̄ f(x) − x` (concave, positive at `0`) has at most one zero in `[0, ∞)`. -/
theorem xbar_unique {f : ℝ → ℝ} {zbar : ℝ} (hz : 0 < zbar) (hf : ConcaveOn ℝ (Ici 0) f)
    (hf0 : 0 < f 0) {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (e₁ : zbar * f x₁ = x₁)
    (e₂ : zbar * f x₂ = x₂) : x₁ = x₂ := by
  have key : ∀ a b : ℝ, 0 ≤ a → a < b → zbar * f a = a → zbar * f b = b → False := by
    intro a b ha hab ea eb
    have hb : 0 < b := ha.trans_lt hab
    have hapos : 0 < a := by
      rcases ha.eq_or_lt with h0 | h0
      · rw [← h0] at ea; nlinarith
      · exact h0
    set t := a / b
    have ht : t * b = a := div_mul_cancel₀ a hb.ne'
    have ht1 : t < 1 := (div_lt_one hb).2 hab
    have ht0 : 0 ≤ t := div_nonneg ha hb.le
    have hc := hf.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hb.le) (by linarith : (0 : ℝ) ≤ 1 - t) ht0
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hc
    rw [ht] at hc
    have := mul_le_mul_of_nonneg_left hc hz.le
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) (mul_pos hz hf0)]
  rcases lt_trichotomy x₁ x₂ with h | h | h
  · exact (key _ _ h₁ h e₁ e₂).elim
  · exact h
  · exact (key _ _ h₂ h e₂ e₁).elim

/-- The NOTE's production function `f(x) = 1 + 0.9x + k(1 − e^{−x})`, with `k = 2`. -/
noncomputable def noXbarF (x : ℝ) : ℝ := 1 + 9 / 10 * x + 2 * (1 - Real.exp (-x))

/-- `f′(x) = 0.9 + 2e^{−x}`. -/
theorem hasDerivAt_noXbarF (x : ℝ) :
    HasDerivAt noXbarF (9 / 10 + 2 * Real.exp (-x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have := (((hasDerivAt_id x).const_mul (9 / 10 : ℝ)).const_add 1).add
    ((h1.const_sub 1).const_mul 2)
  exact this.congr_deriv (by ring)

theorem noXbarF_strictMono : StrictMono noXbarF := fun x y hxy => by
  have := Real.exp_lt_exp.2 (neg_lt_neg hxy)
  simp only [noXbarF]
  nlinarith

theorem noXbarF_concave : ConcaveOn ℝ (Ici 0) noXbarF := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  have := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul, noXbarF] at this ⊢
  have e : a * -x + b * -y = -(a * x + b * y) := by ring
  rw [e] at this
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

/-- **The modified (T2)** for a concave `f` with `f(0) > 0` and `f(b) < b` for some `b > 0`: some
`x̂ > 0` has `x ≤ f(x) ≤ x̂` on `[0, x̂]` and `f(x) < x` for `x > x̂` (`f(x) − x` is concave,
positive at `0` and negative at `b`). -/
theorem modifiedT2_of_concave {f : ℝ → ℝ} (hcont : ContinuousOn f (Ici 0))
    (hmono : MonotoneOn f (Ici 0)) (hf : ConcaveOn ℝ (Ici 0) f) (hf0 : 0 < f 0) {b : ℝ}
    (hb : 0 < b) (hfb : f b < b) :
    ∃ xhat, 0 < xhat ∧ (∀ x, 0 ≤ x → x ≤ xhat → x ≤ f x ∧ f x ≤ xhat) ∧
      ∀ x, xhat < x → f x < x := by
  set hfun : ℝ → ℝ := fun x => f x - x
  have hc : ContinuousOn hfun (Icc 0 b) :=
    (hcont.mono Icc_subset_Ici_self).sub continuousOn_id
  have h0 : hfun 0 = f 0 := by simp [hfun]
  have hb' : hfun b < 0 := by simp only [hfun]; linarith
  have hconc : ConcaveOn ℝ (Ici 0) hfun := hf.sub (concaveOn_id (convex_Ici 0))
  obtain ⟨xhat, hxhat, hval⟩ := intermediate_value_Icc' hb.le hc ⟨hb'.le, by rw [h0]; exact hf0.le⟩
  have hpos : 0 < xhat := by
    rcases hxhat.1.eq_or_lt with h | h
    · rw [← h, h0] at hval; linarith
    · exact h
  -- on `(0, x̂)`, `hfun > 0`
  have hchord : ∀ a c : ℝ, 0 < a → a < c → hfun c = 0 → 0 < hfun a := by
    intro a c ha hac hc0
    have hc0' : 0 < c := ha.trans hac
    set t := a / c
    have ht : t * c = a := div_mul_cancel₀ a hc0'.ne'
    have ht1 : t < 1 := (div_lt_one hc0').2 hac
    have ht0 : 0 ≤ t := div_nonneg ha.le hc0'.le
    have hcc := hconc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hc0'.le) (by linarith : (0 : ℝ) ≤ 1 - t)
      ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hcc
    rw [ht, h0, hc0] at hcc
    nlinarith
  refine ⟨xhat, hpos, fun x hx hxx => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · rcases hx.eq_or_lt with h | h
    · rw [← h]; exact hf0.le
    rcases hxx.eq_or_lt with h' | h'
    · rw [h']; simp only [hfun] at hval; linarith
    have := hchord x xhat h h' hval
    simp only [hfun] at this; linarith
  · have := hmono (mem_Ici.2 hx) (mem_Ici.2 hpos.le) hxx
    simp only [hfun] at hval; linarith
  · by_contra hge
    replace hge := not_lt.1 hge
    -- `x̂` lies strictly between `0` and `x`
    set t := xhat / x
    have hx0 : 0 < x := hpos.trans hx
    have ht : t * x = xhat := div_mul_cancel₀ xhat hx0.ne'
    have ht1 : t < 1 := (div_lt_one hx0).2 hx
    have ht0 : 0 ≤ t := div_nonneg hpos.le hx0.le
    have hcc := hconc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hx0.le) (by linarith : (0 : ℝ) ≤ 1 - t)
      ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hcc
    rw [ht, h0, hval] at hcc
    have : 0 ≤ hfun x := by simp only [hfun]; linarith
    nlinarith

/-- `f(x) − x = 3 − 0.1x − 2e^{−x}` has a zero `x̂ > 0`, with `x ≤ f(x) ≤ x̂` on `[0, x̂]` and
`f(x) < x` beyond: the modified (T2). -/
theorem noXbarF_T2 : ∃ xhat, 0 < xhat ∧ (∀ x, 0 ≤ x → x ≤ xhat → x ≤ noXbarF x ∧
    noXbarF x ≤ xhat) ∧ ∀ x, xhat < x → noXbarF x < x := by
  have hcont : Continuous noXbarF :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_noXbarF x).continuousAt
  refine modifiedT2_of_concave hcont.continuousOn (noXbarF_strictMono.monotone.monotoneOn _)
    noXbarF_concave (by simp [noXbarF]) (b := 30) (by norm_num) ?_
  simp only [noXbarF]
  have := Real.exp_pos (-30)
  nlinarith

/-- **Existence of `x̄` fails** (NOTE p. 392). With `β = 1/2`, `k = 2 > 1/β − 0.9` and `z̄ = 2`,
`f(x) = 1 + 0.9x + k(1 − e^{−x})` is continuous, strictly increasing, concave and `C¹`, with
`f(0) = 1 > 0`, `βf′(0) = 1.45 > 1` and the modified (T2); but `z̄ f(x) > x` for all `x ≥ 0`,
so no `x̄ > 0` has `x̄ = z̄ f(x̄)` (or even `z̄ f(x̄) ≤ x̄`). -/
theorem xbar_counterexample :
    Continuous noXbarF ∧ StrictMono noXbarF ∧ ConcaveOn ℝ (Ici 0) noXbarF ∧
      (∀ x, HasDerivAt noXbarF (9 / 10 + 2 * Real.exp (-x)) x) ∧
      Continuous (fun x : ℝ => 9 / 10 + 2 * Real.exp (-x)) ∧
      0 < noXbarF 0 ∧ 1 < 1 / 2 * (9 / 10 + 2 * Real.exp (-0)) ∧
      (∃ xhat, 0 < xhat ∧ (∀ x, 0 ≤ x → x ≤ xhat → x ≤ noXbarF x ∧ noXbarF x ≤ xhat) ∧
        ∀ x, xhat < x → noXbarF x < x) ∧
      ∀ x, 0 ≤ x → x < 2 * noXbarF x := by
  refine ⟨continuous_iff_continuousAt.2 fun x => (hasDerivAt_noXbarF x).continuousAt,
    noXbarF_strictMono, noXbarF_concave, hasDerivAt_noXbarF,
    by fun_prop, by simp [noXbarF], by norm_num, noXbarF_T2, fun x hx => ?_⟩
  have h1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hx)
  simp only [noXbarF]
  nlinarith

/-! ### The problem in output: the operator `T` on `C(X)` -/

/-- The primitives of §13.3 (pp. 391–392): `0 < β < 1`; `U` continuous and strictly increasing
on `[0, ∞)`; `f` continuous and strictly increasing on `[0, ∞)` with `f(0) > 0`; `Z = [1, z̄]`
with `z̄ > 1`; and `X = [0, x̄]` with `z̄ f(x̄) ≤ x̄` (the book: `x̄ = z̄ f(x̄)`). Concavity and
differentiability are assumed where used. -/
structure OutputHyp (U f : ℝ → ℝ) (β xbar zbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f (Ici 0)
  f_mono : StrictMonoOn f (Ici 0)
  f_pos : 0 < f 0
  zbar_gt : 1 < zbar
  xbar_pos : 0 < xbar
  xbar_maintain : zbar * f xbar ≤ xbar

variable {U f : ℝ → ℝ} {β xbar zbar : ℝ}

namespace OutputHyp

variable (h : OutputHyp U f β xbar zbar)
include h

theorem f_ge {y : ℝ} (hy : 0 ≤ y) : f 0 ≤ f y :=
  h.f_mono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy

theorem f_pos' {y : ℝ} (hy : 0 ≤ y) : 0 < f y := h.f_pos.trans_le (h.f_ge hy)

/-- Next period's output `f(y) z` lies in `X`. -/
theorem next_mem {y z : ℝ} (hy : y ∈ Icc 0 xbar) (hz : z ∈ Icc 1 zbar) :
    f y * z ∈ Icc 0 xbar := by
  have hfy : f y ≤ f xbar := h.f_mono.monotoneOn (mem_Ici.2 hy.1) (mem_Ici.2 h.xbar_pos.le) hy.2
  refine ⟨mul_nonneg (h.f_pos' hy.1).le (by linarith [hz.1]), ?_⟩
  calc f y * z ≤ f xbar * zbar :=
        mul_le_mul hfy hz.2 (by linarith [hz.1]) ((h.f_pos' hy.1).le.trans hfy)
    _ = zbar * f xbar := mul_comm _ _
    _ ≤ xbar := h.xbar_maintain

/-- `U` is bounded on `[0, x̄]`. -/
theorem bddU : ∃ B, ∀ c ∈ Icc 0 xbar, |U c| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (h.U_cont.mono Icc_subset_Ici_self)
  exact ⟨B, fun c hc => by simpa [Real.norm_eq_abs] using hB c hc⟩

theorem max_mem (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar) :
    max (p.1.1 - p.2.1) 0 ∈ Icc 0 xbar :=
  ⟨le_max_right _ _, max_le (by linarith [p.1.2.2, p.2.2.1]) h.xbar_pos.le⟩

end OutputHyp

/-- Next period's output `f(y) z′ ∈ X`. -/
def outNext (h : OutputHyp U f β xbar zbar) (y : Icc (0 : ℝ) xbar) (z : Icc (1 : ℝ) zbar) :
    Icc (0 : ℝ) xbar :=
  ⟨f y.1 * z.1, h.next_mem y.2 z.2⟩

theorem continuous_outNext (h : OutputHyp U f β xbar zbar) :
    Continuous fun p : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar => outNext h p.1 p.2 :=
  ((h.f_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2.1).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The objective `U(x − y) + β ∫ w(f(y) z′) μ(dz′)` of (1), with consumption clamped at `0`
off the constraint set. -/
noncomputable def outObj (h : OutputHyp U f β xbar zbar) (μ : Measure (Icc (1 : ℝ) zbar))
    (w : Icc (0 : ℝ) xbar → ℝ) (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar) : ℝ :=
  U (max (p.1.1 - p.2.1) 0) + β * ∫ z, w (outNext h p.2 z) ∂μ

variable (h : OutputHyp U f β xbar zbar) (μ : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem outObj_of_le (w : Icc (0 : ℝ) xbar → ℝ) {x y : Icc (0 : ℝ) xbar} (hy : y.1 ≤ x.1) :
    outObj h μ w (x, y) = U (x.1 - y.1) + β * ∫ z, w (outNext h y z) ∂μ := by
  simp only [outObj, max_eq_left (sub_nonneg.2 hy)]

/-- `z′ ↦ w(f(y) z′)` is integrable. -/
theorem integrable_outNext (w : Icc (0 : ℝ) xbar →ᵇ ℝ) (y : Icc (0 : ℝ) xbar) :
    Integrable (fun z => w (outNext h y z)) μ :=
  BoundedContinuousFunction.integrable μ
    (w.compContinuous ⟨fun z => outNext h y z,
      (continuous_outNext h).comp (Continuous.prodMk_right y)⟩)

omit [IsProbabilityMeasure μ] in
theorem continuous_expOut [IsFiniteMeasure μ] (w : Icc (0 : ℝ) xbar →ᵇ ℝ) :
    Continuous fun y => ∫ z, w (outNext h y z) ∂μ :=
  continuous_integral_section μ (w.compContinuous ⟨fun p => outNext h p.1 p.2,
    continuous_outNext h⟩)

omit [IsProbabilityMeasure μ] in
theorem continuous_outObj [IsFiniteMeasure μ] (w : Icc (0 : ℝ) xbar →ᵇ ℝ) :
    Continuous (outObj h μ w) :=
  (h.U_cont.comp_continuous (((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).max continuous_const)
    fun _ => mem_Ici.2 (le_max_right _ _)).add
    (continuous_const.mul ((continuous_expOut h μ w).comp continuous_snd))

theorem outΓ_nonempty (s : Icc (0 : ℝ) xbar) : (outΓ xbar s).Nonempty :=
  ⟨⟨0, le_rfl, s.2.1.trans s.2.2⟩, s.2.1⟩

theorem outΓ_compact (s : Icc (0 : ℝ) xbar) : IsCompact (outΓ xbar s) :=
  IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const)

include h in
theorem outΓ_lhc (s : Icc (0 : ℝ) xbar) : IsLHC (outΓ xbar) s :=
  isLHC_Icc_le continuous_subtype_val (fun s => s.2.1) h.xbar_pos.le s

include h in
theorem outΓ_uhc (s : Icc (0 : ℝ) xbar) : IsUHC (outΓ xbar) s :=
  isUHC_Icc_le continuous_subtype_val (fun s => s.2.1) h.xbar_pos.le s

theorem abs_expOut_le (w : Icc (0 : ℝ) xbar →ᵇ ℝ) (y : Icc (0 : ℝ) xbar) :
    |∫ z, w (outNext h y z) ∂μ| ≤ ‖w‖ := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖w‖)
    (f := fun z => w (outNext h y z)) (Eventually.of_forall fun z => w.norm_coe_le_norm _)
  simpa [Real.norm_eq_abs, measureReal_def] using this

theorem bound_outT (w : Icc (0 : ℝ) xbar →ᵇ ℝ) (x : Icc (0 : ℝ) xbar) :
    ‖maxValue (outObj h μ w) (outΓ xbar) x‖ ≤ h.bddU.choose + β * ‖w‖ := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax (continuous_outObj h μ w).continuousOn
    (outΓ_compact x) (outΓ_nonempty x)
  rw [← hval, Real.norm_eq_abs, outObj]
  refine (abs_add_le _ _).trans (add_le_add (h.bddU.choose_spec _ (h.max_mem (x, y))) ?_)
  rw [abs_mul, abs_of_pos h.β_pos]
  exact mul_le_mul_of_nonneg_left (abs_expOut_le h μ w y) h.β_pos.le

/-- The operator `(Tw)(x) = max_{0 ≤ y ≤ x} [U(x − y) + β ∫ w(f(y) z) μ(dz)]` on `C(X)`;
`Tw` is continuous by the Theorem of the Maximum. -/
noncomputable def outT (w : Icc (0 : ℝ) xbar →ᵇ ℝ) : Icc (0 : ℝ) xbar →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (maxValue (outObj h μ w) (outΓ xbar))
    (theorem_3_6 (continuous_outObj h μ w).continuousOn outΓ_compact (outΓ_lhc h)
      (outΓ_uhc h)).1 (h.bddU.choose + β * ‖w‖) (bound_outT h μ w)

theorem outT_apply (w : Icc (0 : ℝ) xbar →ᵇ ℝ) (x : Icc (0 : ℝ) xbar) :
    outT h μ w x = maxValue (outObj h μ w) (outΓ xbar) x := rfl

/-- `Tw(x)` is attained at some feasible `y` and bounds the objective at every feasible `y`. -/
theorem exists_outT_argmax (w : Icc (0 : ℝ) xbar →ᵇ ℝ) (x : Icc (0 : ℝ) xbar) :
    ∃ y ∈ outΓ xbar x, outT h μ w x = outObj h μ w (x, y) ∧
      ∀ y' ∈ outΓ xbar x, outObj h μ w (x, y') ≤ outT h μ w x := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuous_outObj h μ w).continuousOn
    (outΓ_compact x) (outΓ_nonempty x)
  exact ⟨y, hy, hval.symm, fun y' hy' => (hmax y' hy').trans_eq hval⟩

theorem outT_mono {w w' : Icc (0 : ℝ) xbar →ᵇ ℝ} (hww : w ≤ w') : outT h μ w ≤ outT h μ w' :=
  fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_outT_argmax h μ w x
    obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax h μ w' x
    change outT h μ w x ≤ outT h μ w' x
    rw [hval]
    refine le_trans ?_ (hmax y hy)
    have hE : ∫ z, w (outNext h y z) ∂μ ≤ ∫ z, w' (outNext h y z) ∂μ :=
      integral_mono (integrable_outNext h μ w y) (integrable_outNext h μ w' y) fun z => hww _
    simp only [outObj]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE h.β_pos.le)

theorem outT_add_const (w : Icc (0 : ℝ) xbar →ᵇ ℝ) (a : ℝ) :
    outT h μ (w + const (Icc (0 : ℝ) xbar) a) =
      outT h μ w + const (Icc (0 : ℝ) xbar) (β * a) := by
  have hE : ∀ y, ∫ z, (w + const (Icc (0 : ℝ) xbar) a) (outNext h y z) ∂μ =
      ∫ z, w (outNext h y z) ∂μ + a :=
    fun y => by
      simp only [BoundedContinuousFunction.add_apply, const_apply]
      rw [integral_add (integrable_outNext h μ w y) (integrable_const a)]
      simp
  ext x
  obtain ⟨y, hy, hval, hmax⟩ := exists_outT_argmax h μ w x
  obtain ⟨y', hy', hval', hmax'⟩ := exists_outT_argmax h μ (w + const (Icc (0 : ℝ) xbar) a) x
  simp only [BoundedContinuousFunction.add_apply, const_apply]
  have i1 := hmax y' hy'
  have i2 := hmax' y hy
  simp only [outObj] at hval hval' i1 i2
  rw [hE] at i2 hval'
  refine le_antisymm ?_ ?_
  · rw [hval']; nlinarith
  · rw [hval]; nlinarith

/-- `T` is a contraction of modulus `β` (Blackwell's conditions). -/
theorem outT_contraction : IsContraction (outT h μ) β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => outT_mono h μ)
    (fun w a _ => (outT_add_const h μ w a).le)⟩

/-- `w` solves the functional equation (1): `w(x)` is the maximum of
`U(x − y) + β ∫ w(f(y) z) μ(dz)` over `0 ≤ y ≤ x`. -/
def SolvesOut (w : Icc (0 : ℝ) xbar → ℝ) : Prop :=
  ∀ x : Icc (0 : ℝ) xbar, IsGreatest ((fun y : Icc (0 : ℝ) xbar =>
    U (x.1 - y.1) + β * ∫ z, w (outNext h y z) ∂μ) '' {y | y.1 ≤ x.1}) (w x)

/-- The fixed points of `T` are the bounded continuous solutions of (1). -/
theorem outT_eq_iff (w : Icc (0 : ℝ) xbar →ᵇ ℝ) : outT h μ w = w ↔ SolvesOut h μ w := by
  constructor
  · intro hw x
    obtain ⟨y, hy, hval, hmax⟩ := exists_outT_argmax h μ w x
    rw [hw, outObj_of_le h μ w hy] at hval
    refine ⟨⟨y, hy, hval.symm⟩, ?_⟩
    rintro _ ⟨y', hy', rfl⟩
    have := hmax y' hy'
    rwa [hw, outObj_of_le h μ w hy'] at this
  · intro hw
    ext x
    rw [outT_apply, maxValue]
    have : (fun y => outObj h μ w (x, y)) '' outΓ xbar x = (fun y : Icc (0 : ℝ) xbar =>
        U (x.1 - y.1) + β * ∫ z, w (outNext h y z) ∂μ) '' {y | y.1 ≤ x.1} :=
      Set.image_congr fun y hy => outObj_of_le h μ w hy
    rw [this, (hw x).csSup_eq]

/-- **Exercise 13.3a** (existence and uniqueness). There is exactly one bounded continuous
`v : X → ℝ` satisfying (1), and `Tⁿv₀ → v` at rate `βⁿ` for every `v₀ ∈ C(X)`. -/
theorem ex_13_3a_exists :
    ∃ v : Icc (0 : ℝ) xbar →ᵇ ℝ, SolvesOut h μ v ∧ outT h μ v = v ∧
      (∀ w : Icc (0 : ℝ) xbar →ᵇ ℝ, SolvesOut h μ w → w = v) ∧
      ∀ v₀ (n : ℕ), dist ((outT h μ)^[n] v₀) v ≤ β ^ n * dist v₀ v := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 (outT_contraction h μ)
  exact ⟨v, (outT_eq_iff h μ v).1 hv, hv, fun w hw => huniq w ((outT_eq_iff h μ w).2 hw),
    hrate⟩

/-- `Tw` is strictly increasing for every `w` (the expectation does not depend on `x`, and
`U` is strictly increasing), so the solution `v` of (1) is strictly increasing. -/
theorem outT_strictMono (w : Icc (0 : ℝ) xbar →ᵇ ℝ) : StrictMono (outT h μ w) := by
  intro x x' hxx'
  obtain ⟨y, hy, hval, -⟩ := exists_outT_argmax h μ w x
  obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax h μ w x'
  have hxx : x.1 < x'.1 := hxx'
  have hy' : y ∈ outΓ xbar x' := show y.1 ≤ x'.1 from le_trans hy hxx.le
  rw [hval]
  refine lt_of_lt_of_le ?_ (hmax y hy')
  rw [outObj_of_le h μ w hy, outObj_of_le h μ w hy']
  have hy0 : y.1 ≤ x.1 := hy
  exact add_lt_add_left (h.U_mono (mem_Ici.2 (sub_nonneg.2 hy0))
    (mem_Ici.2 (by linarith)) (by linarith)) _

/-- **`T` preserves concavity** (with `U`, `f` concave): along `x_θ = θx₀ + (1 − θ)x₁` the
choice `y_θ` is feasible, `U(x_θ − y_θ) ≥ θU(x₀ − y₀) + (1 − θ)U(x₁ − y₁)`, and, `w` being
nondecreasing and concave and `f` concave, `w(f(y_θ) z) ≥ θ w(f(y₀) z) + (1 − θ) w(f(y₁) z)`. -/
theorem outT_concave (hU : ConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {w : Icc (0 : ℝ) xbar →ᵇ ℝ} (hwm : Monotone w) (hwc : IsConcaveS (convex_Icc 0 xbar) w) :
    IsConcaveS (convex_Icc 0 xbar) (outT h μ w) := by
  intro x₀ x₁ θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_outT_argmax h μ w x₀
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_outT_argmax h μ w x₁
  obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax h μ w (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁)
  have e0 : y₀.1 ≤ x₀.1 := hy₀
  have e1 : y₁.1 ≤ x₁.1 := hy₁
  have h1' : 0 ≤ 1 - θ := by linarith
  have hyθ : (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 ≤ (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁).1 := by
    rw [cmb_val, cmb_val]; nlinarith
  have hm := hmax _ hyθ
  rw [outObj_of_le h μ w hyθ] at hm
  rw [outObj_of_le h μ w hy₀] at hv₀
  rw [outObj_of_le h μ w hy₁] at hv₁
  -- the return
  have hUc := hU.2 (mem_Ici.2 (sub_nonneg.2 e0)) (mem_Ici.2 (sub_nonneg.2 e1)) h0 h1' (by ring)
  simp only [smul_eq_mul] at hUc
  have hc : θ * (x₀.1 - y₀.1) + (1 - θ) * (x₁.1 - y₁.1) =
      (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁).1 - (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 := by
    rw [cmb_val, cmb_val]; ring
  rw [hc] at hUc
  -- the expectation
  have hpt : ∀ z, θ * w (outNext h y₀ z) + (1 - θ) * w (outNext h y₁ z) ≤
      w (outNext h (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁) z) := fun z => by
    refine (hwc _ _ θ h0 h1).trans (hwm ?_)
    change (cmb (convex_Icc 0 xbar) h0 h1 (outNext h y₀ z) (outNext h y₁ z)).1 ≤
      f (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 * z.1
    rw [cmb_val]
    have := growth_zf_cmb hf y₀ y₁ z h0 h1
    simp only [outNext]
    nlinarith
  have hE : θ * ∫ z, w (outNext h y₀ z) ∂μ + (1 - θ) * ∫ z, w (outNext h y₁ z) ∂μ ≤
      ∫ z, w (outNext h (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁) z) ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((integrable_outNext h μ w y₀).const_mul θ) ((integrable_outNext h μ w y₁).const_mul _)]
    exact integral_mono (((integrable_outNext h μ w y₀).const_mul θ).add
      ((integrable_outNext h μ w y₁).const_mul _)) (integrable_outNext h μ w _) hpt
  rw [hv₀, hv₁]
  have := mul_le_mul_of_nonneg_left hE h.β_pos.le
  nlinarith

theorem isClosed_monotone_concave :
    IsClosed {w : Icc (0 : ℝ) xbar →ᵇ ℝ | Monotone w ∧ IsConcaveS (convex_Icc 0 xbar) w} := by
  have h1 : {w : Icc (0 : ℝ) xbar →ᵇ ℝ | Monotone w} =
      ⋂ x, ⋂ x', ⋂ _ : x ≤ x', {w : Icc (0 : ℝ) xbar →ᵇ ℝ | w x ≤ w x'} := by
    ext w; simp only [mem_iInter]
    exact ⟨fun hw x x' hxx' => hw hxx', fun hw x x' hxx' => hw x x' hxx'⟩
  have h2 : {w : Icc (0 : ℝ) xbar →ᵇ ℝ | IsConcaveS (convex_Icc 0 xbar) w} =
      ⋂ x, ⋂ x', ⋂ θ : ℝ, ⋂ h0 : 0 ≤ θ, ⋂ h1 : θ ≤ 1, {w : Icc (0 : ℝ) xbar →ᵇ ℝ |
        θ * w x + (1 - θ) * w x' ≤ w (cmb (convex_Icc 0 xbar) h0 h1 x x')} := by
    ext w; simp only [mem_iInter]; exact Iff.rfl
  have : {w : Icc (0 : ℝ) xbar →ᵇ ℝ | Monotone w ∧ IsConcaveS (convex_Icc 0 xbar) w} =
      {w : Icc (0 : ℝ) xbar →ᵇ ℝ | Monotone w} ∩
        {w : Icc (0 : ℝ) xbar →ᵇ ℝ | IsConcaveS (convex_Icc 0 xbar) w} := rfl
  rw [this, h1, h2]
  refine (isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_iInter fun _ =>
    isClosed_le (continuous_eval_const _) (continuous_eval_const _)).inter
    (isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_iInter fun θ =>
      isClosed_iInter fun h0 => isClosed_iInter fun h1 => isClosed_le ?_ (continuous_eval_const _))
  exact (continuous_const.mul (continuous_eval_const _)).add
    (continuous_const.mul (continuous_eval_const _))

/-- **Exercise 13.3a** (concavity, with `U` and `f` concave): the solution `v` of (1) is
concave (Corollary 1 to the Contraction Mapping Theorem: `T` maps the closed set of
nondecreasing concave functions into itself). -/
theorem out_concave (hU : ConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v) : IsConcaveS (convex_Icc 0 xbar) v := by
  set C := {w : Icc (0 : ℝ) xbar →ᵇ ℝ | Monotone w ∧ IsConcaveS (convex_Icc 0 xbar) w}
  have hmaps : MapsTo (outT h μ) C C :=
    fun w hw => ⟨(outT_strictMono h μ w).monotone, outT_concave h μ hU hf hw.1 hw.2⟩
  have hne : C.Nonempty := ⟨0, fun _ _ _ => le_rfl, fun _ _ _ _ _ => by simp⟩
  exact (corollary_1 (outT_contraction h μ) hv hne isClosed_monotone_concave hmaps
    hmaps).1.2

/-! ### Strict concavity, the policy function and consumption -/

theorem integrable_comp_cont (w : Icc (0 : ℝ) xbar →ᵇ ℝ) {φ : Icc (1 : ℝ) zbar → Icc (0 : ℝ) xbar}
    (hφ : Continuous φ) : Integrable (fun z => w (φ z)) μ :=
  BoundedContinuousFunction.integrable μ (w.compContinuous ⟨φ, hφ⟩)

theorem continuous_outNext_z (y : Icc (0 : ℝ) xbar) : Continuous fun z => outNext h y z :=
  (continuous_outNext h).comp (Continuous.prodMk_right y)

theorem continuous_cmb_next {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ya yb : Icc (0 : ℝ) xbar) :
    Continuous fun z => cmb (convex_Icc 0 xbar) h0 h1 (outNext h ya z) (outNext h yb z) := by
  have hc : Continuous fun z => θ • (outNext h ya z).1 + (1 - θ) • (outNext h yb z).1 :=
    ((continuous_subtype_val.comp (continuous_outNext_z h ya)).const_smul θ).add
      ((continuous_subtype_val.comp (continuous_outNext_z h yb)).const_smul (1 - θ))
  exact continuous_induced_rng.2 hc

/-- **The step of the chord argument** (as in `growth_flat_step` for §10.1). If `v` is affine on
a chord `[a, b]`, consumption is the same at `a` and `b`, the optimal `y_a < y_b`, `v` is affine
on the chord `[f(y_a) z, f(y_b) z]` (same weight `θ`) for `μ`-almost every `z`, and
`v(b) − v(a) = β ∫ [v(f(y_b) z) − v(f(y_a) z)] μ(dz)`. -/
theorem out_flat_step (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v) {a b : Icc (0 : ℝ) xbar} (hab : a < b)
    {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (heq : v (cmb (convex_Icc 0 xbar) h0.le h1.le a b) = θ * v a + (1 - θ) * v b) :
    ∃ ya yb : Icc (0 : ℝ) xbar, ya < yb ∧
      (∀ᵐ z ∂μ, v (cmb (convex_Icc 0 xbar) h0.le h1.le (outNext h ya z) (outNext h yb z)) =
        θ * v (outNext h ya z) + (1 - θ) * v (outNext h yb z)) ∧
      v b - v a = β * ∫ z, (v (outNext h yb z) - v (outNext h ya z)) ∂μ := by
  have hvm : Monotone v := by rw [← hv]; exact (outT_strictMono h μ v).monotone
  have hvc := out_concave h μ hU.concaveOn hf hv
  obtain ⟨ya, hya, hva, -⟩ := exists_outT_argmax h μ v a
  obtain ⟨yb, hyb, hvb, -⟩ := exists_outT_argmax h μ v b
  obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax h μ v (cmb (convex_Icc 0 xbar) h0.le h1.le a b)
  rw [hv] at hva hvb hmax
  have ea : ya.1 ≤ a.1 := hya
  have eb : yb.1 ≤ b.1 := hyb
  have h1' : 0 < 1 - θ := by linarith
  set yθ := cmb (convex_Icc 0 xbar) h0.le h1.le ya yb
  have hyθ : yθ.1 ≤ (cmb (convex_Icc 0 xbar) h0.le h1.le a b).1 := by
    simp only [yθ]; rw [cmb_val, cmb_val]; nlinarith
  have hm := hmax yθ hyθ
  rw [outObj_of_le h μ v hyθ] at hm
  rw [outObj_of_le h μ v hya] at hva
  rw [outObj_of_le h μ v hyb] at hvb
  -- the pointwise gaps
  set C : Icc (1 : ℝ) zbar → Icc (0 : ℝ) xbar :=
    fun z => cmb (convex_Icc 0 xbar) h0.le h1.le (outNext h ya z) (outNext h yb z)
  have hC := continuous_cmb_next h h0.le h1.le ya yb
  have hg1 : ∀ z, θ * v (outNext h ya z) + (1 - θ) * v (outNext h yb z) ≤ v (C z) :=
    fun z => hvc _ _ θ h0.le h1.le
  have hg2 : ∀ z, v (C z) ≤ v (outNext h yθ z) := fun z => hvm (by
    change (C z).1 ≤ f yθ.1 * z.1
    simp only [C]
    rw [cmb_val]
    have := growth_zf_cmb hf ya yb z h0.le h1.le
    simp only [outNext]
    nlinarith)
  have hia := integrable_outNext h μ v ya
  have hib := integrable_outNext h μ v yb
  have hiθ := integrable_outNext h μ v yθ
  have hiC := integrable_comp_cont μ v hC
  have hI : Integrable (fun z => θ * v (outNext h ya z) + (1 - θ) * v (outNext h yb z)) μ :=
    (hia.const_mul θ).add (hib.const_mul (1 - θ))
  set Ea := ∫ z, v (outNext h ya z) ∂μ
  set Eb := ∫ z, v (outNext h yb z) ∂μ
  set Eθ := ∫ z, v (outNext h yθ z) ∂μ
  set EC := ∫ z, v (C z) ∂μ
  have hlin : ∫ z, (θ * v (outNext h ya z) + (1 - θ) * v (outNext h yb z)) ∂μ =
      θ * Ea + (1 - θ) * Eb := by
    rw [integral_add (hia.const_mul θ) (hib.const_mul (1 - θ)), integral_const_mul,
      integral_const_mul]
  have hgap1 : ∫ z, (v (C z) - (θ * v (outNext h ya z) + (1 - θ) * v (outNext h yb z))) ∂μ =
      EC - (θ * Ea + (1 - θ) * Eb) := by
    rw [integral_sub hiC hI, hlin]
  have hE1 : 0 ≤ EC - (θ * Ea + (1 - θ) * Eb) := by
    rw [← hgap1]; exact integral_nonneg fun z => sub_nonneg.2 (hg1 z)
  have hE2 : EC ≤ Eθ := integral_mono hiC hiθ hg2
  -- the returns
  set ca := a.1 - ya.1
  set cb := b.1 - yb.1
  have hca : 0 ≤ ca := sub_nonneg.2 ea
  have hcb : 0 ≤ cb := sub_nonneg.2 eb
  have hUc := hU.concaveOn.2 (mem_Ici.2 hca) (mem_Ici.2 hcb) h0.le h1'.le (by ring)
  simp only [smul_eq_mul] at hUc
  have hcθ : θ * ca + (1 - θ) * cb =
      (cmb (convex_Icc 0 xbar) h0.le h1.le a b).1 - yθ.1 := by
    simp only [yθ, ca, cb]; rw [cmb_val, cmb_val]; ring
  rw [hcθ] at hUc
  have hβ := h.β_pos
  -- all the inequalities are equalities
  have hgapU : θ * U ca + (1 - θ) * U cb =
      U ((cmb (convex_Icc 0 xbar) h0.le h1.le a b).1 - yθ.1) := by
    nlinarith [mul_nonneg hβ.le hE1, mul_le_mul_of_nonneg_left hE2 hβ.le]
  have hceq : ca = cb := by
    by_contra hne
    have := hU.2 (mem_Ici.2 hca) (mem_Ici.2 hcb) hne h0 h1' (by ring)
    simp only [smul_eq_mul] at this
    rw [hcθ] at this
    linarith
  have hEeq : EC - (θ * Ea + (1 - θ) * Eb) = 0 := by
    nlinarith [mul_nonneg hβ.le hE1, mul_le_mul_of_nonneg_left hE2 hβ.le]
  refine ⟨ya, yb, ?_, ?_, ?_⟩
  · change ya.1 < yb.1
    have : a.1 < b.1 := hab
    have : a.1 - ya.1 = b.1 - yb.1 := hceq
    linarith
  · have hzero := (integral_eq_zero_iff_of_nonneg (fun z => sub_nonneg.2 (hg1 z))
      (hiC.sub hI)).1 (by rw [hgap1, hEeq])
    filter_upwards [hzero] with z hz
    simp only [Pi.zero_apply] at hz
    change v (C z) = _
    linarith
  · rw [integral_sub hib hia, hva, hvb]
    have : U (a.1 - ya.1) = U (b.1 - yb.1) := congrArg U hceq
    rw [this]
    ring

/-- **Exercise 13.3a** (strict concavity, with `U` strictly concave and `f` only concave): `v` is
strictly concave. As for §10.1 (`growth_strictConcave`): Assumption 9.10 fails, since
`U(x − y)` is not strictly concave jointly; if `v` were affine on some chord, let `S` be the
supremum of the rises `v(b) − v(a) > 0` over such chords; `out_flat_step` bounds each rise by
`βS`. -/
theorem out_strictConcave (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v := by
  have hvc := out_concave h μ hU.concaveOn hf hv
  have hmono : StrictMono v := by rw [← hv]; exact outT_strictMono h μ v
  set D : Set ℝ := {d | ∃ a b : Icc (0 : ℝ) xbar, ∃ θ : ℝ, ∃ h0 : 0 < θ, ∃ h1 : θ < 1, a < b ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le a b) = θ * v a + (1 - θ) * v b ∧ d = v b - v a}
  have hD : D = ∅ := by
    by_contra hne
    obtain ⟨d₀, hd₀⟩ := nonempty_iff_ne_empty.2 hne
    have hbdd : BddAbove D := ⟨2 * ‖v‖, by
      rintro _ ⟨a, b, θ, h0, h1, -, -, rfl⟩
      have := v.dist_le_two_norm b a
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this⟩
    have hle : ∀ d ∈ D, d ≤ β * sSup D := by
      rintro _ ⟨a, b, θ, h0, h1, hab, heq, rfl⟩
      obtain ⟨ya, yb, hlt, hae, hdiff⟩ := out_flat_step h μ hU hf hv hab h0 h1 heq
      rw [hdiff]
      refine mul_le_mul_of_nonneg_left ?_ h.β_pos.le
      have hnext : ∀ z, outNext h ya z < outNext h yb z := fun z => by
        change f ya.1 * z.1 < f yb.1 * z.1
        exact mul_lt_mul_of_pos_right (h.f_mono (mem_Ici.2 ya.2.1) (mem_Ici.2 yb.2.1) hlt)
          (by linarith [z.2.1])
      have := integral_mono_ae ((integrable_outNext h μ v yb).sub (integrable_outNext h μ v ya))
        (integrable_const (sSup D))
        (hae.mono fun z hz => le_csSup hbdd ⟨_, _, θ, h0, h1, hnext z, hz, rfl⟩)
      simpa using this
    have hS : sSup D ≤ β * sSup D := csSup_le ⟨d₀, hd₀⟩ hle
    have hpos : 0 < d₀ := by
      obtain ⟨a, b, θ, h0, h1, hab, -, rfl⟩ := hd₀
      exact sub_pos.2 (hmono hab)
    have := lt_of_lt_of_le hpos (le_csSup hbdd hd₀)
    nlinarith [h.β_lt]
  intro x x' hne θ h0 h1
  refine lt_of_le_of_ne (hvc x x' θ h0.le h1.le) fun heq => ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmem : v x' - v x ∈ D := ⟨x, x', θ, h0, h1, hlt, heq.symm, rfl⟩
    rw [hD] at hmem
    exact hmem
  · have h0' : 0 < 1 - θ := by linarith
    have h1' : 1 - θ < 1 := by linarith
    have hc : cmb (convex_Icc 0 xbar) h0'.le h1'.le x' x =
        cmb (convex_Icc 0 xbar) h0.le h1.le x x' := by
      ext1
      rw [cmb_val, cmb_val]
      ring
    have hmem : v x - v x' ∈ D := ⟨x', x, 1 - θ, h0', h1', hlt, by
      rw [hc, ← heq]; ring, rfl⟩
    rw [hD] at hmem
    exact hmem

/-- **Exercise 13.3a.** With `U` strictly concave and `f` concave, there is a unique bounded
continuous `v : X → ℝ` satisfying (1), and `v` is strictly increasing and strictly concave. -/
theorem ex_13_3a (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f) :
    ∃ v : Icc (0 : ℝ) xbar →ᵇ ℝ, SolvesOut h μ v ∧
      (∀ w : Icc (0 : ℝ) xbar →ᵇ ℝ, SolvesOut h μ w → w = v) ∧ StrictMono v ∧
      IsStrictConcaveS (convex_Icc 0 xbar) v := by
  obtain ⟨v, hsol, hv, huniq, -⟩ := ex_13_3a_exists h μ
  refine ⟨v, hsol, huniq, ?_, out_strictConcave h μ hU hf hv⟩
  rw [← hv]
  exact outT_strictMono h μ v

/-- `W(y) = ∫ v(f(y) z) μ(dz)` is strictly concave: `v` is strictly concave and nondecreasing,
`f` is concave and injective. -/
theorem out_W_strictConcave (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) fun y => ∫ z, v (outNext h y z) ∂μ := by
  have hvs := out_strictConcave h μ hU hf hv
  have hvm : Monotone v := by rw [← hv]; exact (outT_strictMono h μ v).monotone
  intro y y' hne θ h0 h1
  have hia := integrable_outNext h μ v y
  have hib := integrable_outNext h μ v y'
  change θ * ∫ z, v (outNext h y z) ∂μ + (1 - θ) * ∫ z, v (outNext h y' z) ∂μ <
    ∫ z, v (outNext h (cmb (convex_Icc 0 xbar) h0.le h1.le y y') z) ∂μ
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hia.const_mul θ) (hib.const_mul _)]
  refine integral_lt_integral_of_forall_lt ((hia.const_mul θ).add (hib.const_mul _))
    (integrable_outNext h μ v _) fun z => ?_
  have hne' : outNext h y z ≠ outNext h y' z := fun heq => hne (by
    have h1 : f y.1 * z.1 = f y'.1 * z.1 := congrArg Subtype.val heq
    have := mul_right_cancel₀ (by linarith [z.2.1] : (0 : ℝ) < z.1).ne' h1
    exact Subtype.ext (h.f_mono.injOn (mem_Ici.2 y.2.1) (mem_Ici.2 y'.2.1) this))
  refine lt_of_lt_of_le (hvs _ _ hne' θ h0 h1) (hvm ?_)
  change (cmb (convex_Icc 0 xbar) h0.le h1.le (outNext h y z) (outNext h y' z)).1 ≤
    f (cmb (convex_Icc 0 xbar) h0.le h1.le y y').1 * z.1
  rw [cmb_val]
  have := growth_zf_cmb hf y y' z h0.le h1.le
  simp only [outNext]
  nlinarith

/-- The problem in (1) has a unique maximizer at every `x`. -/
theorem out_uniqueArgmax (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v) :
    UniqueArgmax (outΓ xbar) (outObj h μ v) := by
  have hW := out_W_strictConcave h μ hU hf hv
  have hc : ContinuousOn (outObj h μ v) (graph (outΓ xbar)) :=
    (continuous_outObj h μ v).continuousOn
  refine ⟨outΓ_nonempty, outΓ_compact, outΓ_lhc h, outΓ_uhc h, hc,
    fun x y₁ hy₁ y₂ hy₂ => ?_⟩
  have hle := fun y (hy : y ∈ outΓ xbar x) => le_maxValue hc (outΓ_compact x) hy
  refine growth_argmax_unique hU.concaveOn h.β_pos
    (W := fun y => ∫ z, v (outNext h y z) ∂μ) hW hy₁.1 hy₂.1 (fun y hy => ?_) (fun y hy => ?_)
  · have := hle y hy
    rw [← hy₁.2] at this
    exact this
  · have := hle y hy
    rw [← hy₂.2] at this
    exact this

/-- The policy function `g(x) = argmax_{0 ≤ y ≤ x} [U(x − y) + β ∫ v(f(y) z) μ(dz)]`. -/
noncomputable def outPolicy [Nonempty (Icc (0 : ℝ) xbar)] (v : Icc (0 : ℝ) xbar →ᵇ ℝ) :
    Icc (0 : ℝ) xbar → Icc (0 : ℝ) xbar :=
  argmaxFn (outΓ xbar) (outObj h μ v)

/-- **Exercise 13.3b** (corrected). With `U` strictly concave and `f` concave, the policy
correspondence is single-valued, `G(x) = {g(x)}`, with `0 ≤ g(x) ≤ x`, `g(0) = 0` and
`v(x) = U(x − g(x)) + β ∫ v(f(g(x)) z) μ(dz)`; `g` is continuous and nondecreasing, and
consumption `c(x) = x − g(x)` is nondecreasing (exchange arguments, as in `ex_10_1d`).
**Correction:** "`0 < g(x) < x` for `x > 0`" and "`g` strictly increasing" fail in general
(`ex_13_3b_counterexample`); for strict monotonicity of `c` see `out_consumption_strictMono`. -/
theorem ex_13_3b [Nonempty (Icc (0 : ℝ) xbar)] (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v) :
    (∀ x, argmax (outObj h μ v) (outΓ xbar) x = {outPolicy h μ v x}) ∧
      (∀ x, (outPolicy h μ v x).1 ≤ x.1 ∧
        v x = U (x.1 - (outPolicy h μ v x).1) + β * ∫ z, v (outNext h (outPolicy h μ v x) z) ∂μ) ∧
      (outPolicy h μ v ⟨0, le_rfl, h.xbar_pos.le⟩).1 = 0 ∧
      Continuous (outPolicy h μ v) ∧ Monotone (outPolicy h μ v) ∧
      Monotone fun x => x.1 - (outPolicy h μ v x).1 := by
  have hO := out_uniqueArgmax h μ hU hf hv
  set g := outPolicy h μ v
  have hgm : ∀ s, g s ∈ argmax (outObj h μ v) (outΓ xbar) s := hO.argmaxFn_mem
  have hmem : ∀ s, (g s).1 ≤ s.1 := fun s => (hgm s).1
  have hopt : ∀ s y, y ∈ outΓ xbar s → outObj h μ v (s, y) ≤ outObj h μ v (s, g s) :=
    fun s y hy => by
      rw [(hgm s).2]
      exact le_maxValue hO.cont (hO.compact s) hy
  have hval : ∀ s y : Icc (0 : ℝ) xbar, y.1 ≤ s.1 →
      outObj h μ v (s, y) = U (s.1 - y.1) + β * ∫ z, v (outNext h y z) ∂μ :=
    fun s y hy => outObj_of_le h μ v hy
  have hlt_of : ∀ s s' : Icc (0 : ℝ) xbar, s ≤ s' → s ≠ s' → s.1 < s'.1 := fun s s' hle hne =>
    lt_of_le_of_ne hle fun heq => hne (Subtype.ext heq)
  have hfix : ∀ x, v x = U (x.1 - (g x).1) + β * ∫ z, v (outNext h (g x) z) ∂μ := fun x => by
    have := (hgm x).2
    rw [← outT_apply, hv, hval x _ (hmem x)] at this
    exact this.symm
  -- `g` is nondecreasing
  have hmono : Monotone g := by
    intro s s' hss'
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hlt' : (g s').1 < (g s).1 := hlt
    have hss : s.1 < s'.1 := hlt_of s s' hss' fun heq => by subst heq; exact lt_irrefl _ hlt
    have h1 := hopt s (g s') (show (g s').1 ≤ s.1 by linarith [hmem s])
    have h2 := hopt s' (g s) (show (g s).1 ≤ s'.1 by linarith [hmem s])
    rw [hval s _ (by linarith [hmem s]), hval s _ (hmem s)] at h1
    rw [hval s' _ (by linarith [hmem s]), hval s' _ (hmem s')] at h2
    have := strictConcave_exchange hU (p := s.1 - (g s).1) (q := s.1 - (g s').1)
      (r := s'.1 - (g s).1) (t := s'.1 - (g s').1) (sub_nonneg.2 (hmem s))
      (sub_nonneg.2 (hmem s')) (by linarith) (by linarith) (by ring)
    linarith
  -- consumption `x − g(x)` is nondecreasing
  have hW := strictConcaveOn_liftS (out_W_strictConcave h μ hU hf hv)
  have hWv : ∀ y : Icc (0 : ℝ) xbar, liftS (fun y => ∫ z, v (outNext h y z) ∂μ) y.1 =
      ∫ z, v (outNext h y z) ∂μ := fun y => liftS_of_mem _ y.2
  have hcons : Monotone fun s => s.1 - (g s).1 := by
    intro s s' hss'
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hss : s.1 < s'.1 := hlt_of s s' hss' fun heq => by subst heq; exact lt_irrefl _ hlt
    have hms := hmem s
    have hms' := hmem s'
    have hy0 := (g s).2.1
    have hy0' := (g s').2.1
    set y₁ : Icc (0 : ℝ) xbar := ⟨s.1 - (s'.1 - (g s').1), by
      constructor <;> linarith [s.2.2]⟩
    set y₂ : Icc (0 : ℝ) xbar := ⟨s'.1 - (s.1 - (g s).1), by
      constructor <;> linarith [s'.2.2]⟩
    have h1 := hopt s y₁ (show y₁.1 ≤ s.1 by simp only [y₁]; linarith)
    have h2 := hopt s' y₂ (show y₂.1 ≤ s'.1 by simp only [y₂]; linarith)
    rw [hval s _ (show y₁.1 ≤ s.1 by simp only [y₁]; linarith), hval s _ hms] at h1
    rw [hval s' _ (show y₂.1 ≤ s'.1 by simp only [y₂]; linarith), hval s' _ hms'] at h2
    have e1 : s.1 - y₁.1 = s'.1 - (g s').1 := by simp only [y₁]; ring
    have e2 : s'.1 - y₂.1 = s.1 - (g s).1 := by simp only [y₂]; ring
    rw [e1] at h1
    rw [e2] at h2
    have hex := strictConcave_exchange hW (p := (g s).1) (q := y₁.1) (r := y₂.1)
      (t := (g s').1) (g s).2 (g s').2 (by simp only [y₁]; linarith)
      (by simp only [y₁]; linarith) (by simp only [y₁, y₂]; ring)
    rw [hWv, hWv, hWv, hWv] at hex
    nlinarith [h.β_pos]
  have hg0 : (g ⟨0, le_rfl, h.xbar_pos.le⟩).1 = 0 :=
    le_antisymm (hmem _) (g ⟨0, le_rfl, h.xbar_pos.le⟩).2.1
  exact ⟨hO.argmax_eq, fun x => ⟨hmem x, hfix x⟩, hg0, hO.continuous_argmaxFn, hmono, hcons⟩

/-- **Exercise 13.3c** (Benveniste–Scheinkman, Theorem 4.10). If `0 < x₀ < x̄`, consumption
`c(x₀) = x₀ − g(x₀) > 0` and `U` is differentiable at `c(x₀)`, then `v` is differentiable at
`x₀` with `v′(x₀) = U′(x₀ − g(x₀))`. (`v` is extended off `X` by `liftS`.) Only `c(x₀) > 0` is
needed, not `g(x₀) > 0`. -/
theorem ex_13_3c [Nonempty (Icc (0 : ℝ) xbar)] (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v)
    {x₀ : Icc (0 : ℝ) xbar} (hx0 : 0 < x₀.1) (hx1 : x₀.1 < xbar)
    (hc : (outPolicy h μ v x₀).1 < x₀.1) {U' : ℝ}
    (hU' : HasDerivAt U U' (x₀.1 - (outPolicy h μ v x₀).1)) :
    HasDerivAt (liftS v) U' x₀.1 := by
  obtain ⟨-, hfix, -⟩ := ex_13_3b h μ hU hf hv
  set g₀ := outPolicy h μ v x₀
  have hvc := out_concave h μ hU.concaveOn hf hv
  have hS : Icc (0 : ℝ) xbar ∈ 𝓝 x₀.1 := Icc_mem_nhds hx0 hx1
  have hL : HasDerivAt (fun x => U (x - g₀.1) + β * ∫ z, v (outNext h g₀ z) ∂μ) U' x₀.1 := by
    have := (hU'.comp x₀.1 ((hasDerivAt_id x₀.1).sub_const g₀.1)).add_const
      (β * ∫ z, v (outNext h g₀ z) ∂μ)
    simpa using this
  refine hasDerivAt_of_concaveOn_of_le (concaveOn_liftS hvc) hS hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2]
    exact ((hfix x₀).2).symm
  · have hev : ∀ᶠ x in 𝓝 x₀.1, g₀.1 < x := lt_mem_nhds hc
    filter_upwards [hev, hS] with x hx hxS
    rw [liftS_of_mem _ hxS]
    obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax h μ v ⟨x, hxS⟩
    have := hmax g₀ (show g₀.1 ≤ x from hx.le)
    rw [hv, outObj_of_le h μ v (show g₀.1 ≤ x from hx.le)] at this
    exact this

/-- **Exercise 13.3c** (continuity of the derivative): if `U′` is continuous on `(0, ∞)`, then
`x ↦ U′(x − g(x))` is continuous where consumption is positive. -/
theorem ex_13_3c_continuous [Nonempty (Icc (0 : ℝ) xbar)] (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT h μ v = v)
    {dU : ℝ → ℝ} (hdU : ContinuousOn dU (Ioi 0)) :
    ContinuousOn (fun x : Icc (0 : ℝ) xbar => dU (x.1 - (outPolicy h μ v x).1))
      {x | (outPolicy h μ v x).1 < x.1} := by
  obtain ⟨-, -, -, hgc, -⟩ := ex_13_3b h μ hU hf hv
  exact hdU.comp (continuous_subtype_val.sub (continuous_subtype_val.comp hgc)).continuousOn
    fun x hx => mem_Ioi.2 (sub_pos.2 hx)

/-- **Consumption is strictly increasing where it is positive** (Ex. 13.3b, corrected), if `U`
is differentiable on `(0, ∞)`: for `x < x′` with `c(x′) > 0`, `c(x) < c(x′)`. Otherwise
`c(x) = c(x′) = c₀ > 0` and `g(x) < g(x′)`; the deviations `y = g(x) + ε` at `x` and
`y = g(x′) − ε` at `x′` give `[U(c₀ + ε) − U(c₀)]/ε − [U(c₀) − U(c₀ − ε)]/ε ≤ −βκ` for small
`ε > 0`, where `κ > 0` measures the strict concavity of `W(y) = ∫ v(f(y) z) μ(dz)` on
`[g(x), g(x′)]`; the left side tends to `U′(c₀) − U′(c₀) = 0`. (At `c = 0` this can fail: with
`U′(0) < ∞`, zero consumption may be optimal on an interval.) -/
theorem out_consumption_strictMono [Nonempty (Icc (0 : ℝ) xbar)]
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : outT h μ v = v) {dU : ℝ → ℝ} (hdU : ∀ c, 0 < c → HasDerivAt U (dU c) c)
    {x x' : Icc (0 : ℝ) xbar} (hxx : x < x') (hc' : 0 < x'.1 - (outPolicy h μ v x').1) :
    x.1 - (outPolicy h μ v x).1 < x'.1 - (outPolicy h μ v x').1 := by
  obtain ⟨-, hfix, -, -, -, hcons⟩ := ex_13_3b h μ hU hf hv
  set g := outPolicy h μ v
  by_contra hge
  have heq : x.1 - (g x).1 = x'.1 - (g x').1 := le_antisymm (hcons hxx.le) (not_lt.1 hge)
  set c₀ := x'.1 - (g x').1
  set a := (g x).1
  set b := (g x').1
  have hxx' : x.1 < x'.1 := hxx
  have hab : a < b := by linarith
  have ha0 : 0 ≤ a := (g x).2.1
  have hbx : b ≤ xbar := (g x').2.2
  -- the continuation value `W` and its strict concavity on `[a, b]`
  set W : Icc (0 : ℝ) xbar → ℝ := fun y => ∫ z, v (outNext h y z) ∂μ
  have hWs := strictConcaveOn_liftS (out_W_strictConcave h μ hU hf hv)
  set Wl := liftS W
  have hWl : ∀ y (hy : y ∈ Icc 0 xbar), Wl y = W ⟨y, hy⟩ := fun y hy => liftS_of_mem W hy
  set m := (a + b) / 2
  set d := (b - a) / 2
  have hd : 0 < d := by simp only [d]; linarith
  have hamem : a ∈ Icc 0 xbar := (g x).2
  have hbmem : b ∈ Icc 0 xbar := (g x').2
  have hmmem : m ∈ Icc 0 xbar := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hmid := hWs.2 hamem hbmem hab.ne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show 1 / 2 * a + 1 / 2 * b = m by simp only [m]; ring] at hmid
  set K₁ := Wl m - Wl a
  set K₂ := Wl b - Wl m
  have hK : K₂ < K₁ := by simp only [K₁, K₂]; linarith
  have hcv := hWs.concaveOn.neg
  -- the optimality inequalities at a small `ε`
  have hbound : ∀ ε, 0 < ε → ε < c₀ → ε < d →
      (U (c₀ + ε) - U c₀) / ε - (U c₀ - U (c₀ - ε)) / ε ≤ β * (K₂ - K₁) / d := by
    intro ε hε hεc hεd
    have hy1 : a + ε ∈ Icc 0 xbar := ⟨by linarith, by linarith [x.2.2]⟩
    have hy2 : b - ε ∈ Icc 0 xbar := ⟨by simp only [d] at hεd; linarith, by linarith⟩
    -- at `x`, `y = a + ε`
    obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax h μ v x
    have h1 := hmax ⟨a + ε, hy1⟩ (show a + ε ≤ x.1 by linarith)
    rw [hv, outObj_of_le h μ v (show a + ε ≤ x.1 by linarith), hfix x |>.2] at h1
    -- at `x′`, `y = b − ε`
    obtain ⟨-, -, -, hmax'⟩ := exists_outT_argmax h μ v x'
    have h2 := hmax' ⟨b - ε, hy2⟩ (show b - ε ≤ x'.1 by linarith)
    rw [hv, outObj_of_le h μ v (show b - ε ≤ x'.1 by linarith), hfix x' |>.2] at h2
    have e1 : x.1 - (a + ε) = c₀ - ε := by simp only [c₀, a] at heq ⊢; linarith
    have e2 : x'.1 - (b - ε) = c₀ + ε := by simp only [c₀, b]; ring
    have e3 : x.1 - a = c₀ := heq
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h1
    -- chord inequalities for `W`
    have hW1 : d * (Wl (a + ε) - Wl a) ≥ ε * K₁ := by
      have := hcv.secant_mono_aux1 (x := a) (y := a + ε) (z := m) hamem hmmem (by linarith)
        (by simp only [m]; simp only [d] at hεd; linarith)
      simp only [Pi.neg_apply] at this
      simp only [K₁, d, m] at this ⊢
      nlinarith
    have hW2 : d * (Wl b - Wl (b - ε)) ≤ ε * K₂ := by
      have := hcv.secant_mono_aux1 (x := m) (y := b - ε) (z := b) hmmem hbmem
        (by simp only [m]; simp only [d] at hεd; linarith) (by linarith)
      simp only [Pi.neg_apply] at this
      simp only [K₂, d, m] at this ⊢
      nlinarith
    rw [hWl _ hy1, hWl _ hamem] at hW1
    rw [hWl _ hbmem, hWl _ hy2] at hW2
    have hβ := h.β_pos
    have i1 : U c₀ - U (c₀ - ε) ≥ β * (W ⟨a + ε, hy1⟩ - W ⟨a, hamem⟩) := by
      have : W ⟨a, hamem⟩ = ∫ z, v (outNext h (g x) z) ∂μ := rfl
      linarith
    have i2 : U (c₀ + ε) - U c₀ ≤ β * (W ⟨b, hbmem⟩ - W ⟨b - ε, hy2⟩) := by
      have : W ⟨b, hbmem⟩ = ∫ z, v (outNext h (g x') z) ∂μ := rfl
      linarith
    rw [div_sub_div_same, div_le_div_iff₀ hε hd]
    have j1 := mul_le_mul_of_nonneg_left hW2 hβ.le
    have j2 := mul_le_mul_of_nonneg_left hW1.le hβ.le
    nlinarith
  -- the limit `ε → 0+`
  have hc₀ : 0 < c₀ := hc'
  have hR := (hdU c₀ hc₀).tendsto_slope_zero_right
  have hL := (hdU c₀ hc₀).tendsto_slope_zero_left
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[<] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using ((continuous_neg.tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds), eventually_nhdsWithin_of_forall fun ε hε => mem_Iio.2 (neg_lt_zero.2 hε)⟩
  have hlim := hR.sub (hL.comp hneg)
  rw [sub_self] at hlim
  have hthr : β * (K₂ - K₁) / d < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h.β_pos (by linarith)) hd
  obtain ⟨ε, hε1, hε2⟩ := ((hlim.eventually (lt_mem_nhds hthr)).and
    (Ioo_mem_nhdsGT (lt_min hc₀ hd))).exists
  have := hbound ε hε2.1 (hε2.2.trans_le (min_le_left _ _)) (hε2.2.trans_le (min_le_right _ _))
  simp only [Function.comp, smul_eq_mul] at hε1
  have e : (-ε)⁻¹ * (U (c₀ + -ε) - U c₀) = (U c₀ - U (c₀ - ε)) / ε := by
    rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]; ring
  rw [e, ← div_eq_inv_mul] at hε1
  linarith

/-! ### Exercise 13.3b: a corner `g = 0` at low output -/

/-- `U(c) = 1 − e^{−20c}`. -/
noncomputable def cexOutU (c : ℝ) : ℝ := 1 - Real.exp (-(20 * c))

/-- `f(y) = 5/6 + 2y/(1 + y)`. -/
noncomputable def cexOutF (y : ℝ) : ℝ := 5 / 6 + cexf y

/-- The example satisfies the primitives, with `β = 3/4`, `z̄ = 2`, `x̄ = 5 = 2 f(5)`. -/
theorem cexOut_hyp : OutputHyp cexOutU cexOutF (3 / 4) 5 2 where
  β_pos := by norm_num
  β_lt := by norm_num
  U_cont := (continuous_const.sub (Real.continuous_exp.comp
    (continuous_const.mul continuous_id).neg)).continuousOn
  U_mono := fun c _ c' _ hcc' => by
    simp only [cexOutU]
    have := Real.exp_lt_exp.2 (show -(20 * c') < -(20 * c) by linarith)
    linarith
  f_cont := continuousOn_const.add cex_hyp.f_cont
  f_mono := fun x hx x' hx' hxx' => by
    simp only [cexOutF]
    linarith [cex_hyp.f_mono hx hx' hxx']
  f_pos := by norm_num [cexOutF, cexf]
  zbar_gt := by norm_num
  xbar_pos := by norm_num
  xbar_maintain := by norm_num [cexOutF, cexf]

/-- `U` is strictly concave, with `U′(c) = 20 e^{−20c}` (continuous, finite at `0`: no Inada
condition is needed for the counterexample). -/
theorem cexOutU_props : StrictConcaveOn ℝ (Ici 0) cexOutU ∧
    ∀ c, HasDerivAt cexOutU (20 * Real.exp (-(20 * c))) c := by
  refine ⟨⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩, fun c => ?_⟩
  · have := strictConvexOn_exp.2 (mem_univ (-(20 * x))) (mem_univ (-(20 * y)))
      (fun h => hxy (by linarith [h])) ha hb hab
    simp only [smul_eq_mul, cexOutU] at this ⊢
    have e : a * -(20 * x) + b * -(20 * y) = -(20 * (a * x + b * y)) := by ring
    rw [e] at this
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
  · have h1 : HasDerivAt (fun c : ℝ => -(20 * c)) (-(20 * 1)) c :=
      ((hasDerivAt_id c).const_mul 20).neg
    have := ((Real.hasDerivAt_exp (-(20 * c))).comp c h1).const_sub 1
    exact this.congr_deriv (by ring)

/-- `f` is concave and `C¹` on `(−1, ∞)`, with `f′(y) = 2/(1 + y)²`, so `βf′(0) = 3/2 > 1`. -/
theorem cexOutF_props : ConcaveOn ℝ (Ici 0) cexOutF ∧
    (∀ y, -1 < y → HasDerivAt cexOutF (2 / (1 + y) ^ 2) y) ∧
      (1 : ℝ) < 3 / 4 * (2 / (1 + 0) ^ 2) := by
  refine ⟨(concaveOn_const _ (convex_Ici 0)).add cexf_concave, fun y hy => ?_, by norm_num⟩
  have hne : (1 + y) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by
    simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := by
    simpa using (hasDerivAt_id y).const_add (1 : ℝ)
  have := (h1.div h2 hne).const_add (5 / 6 : ℝ)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- The example's `f` satisfies the modified (T2) (`f(5) = 5/2 < 5`). -/
theorem cexOutF_T2 : ∃ xhat, 0 < xhat ∧ (∀ x, 0 ≤ x → x ≤ xhat → x ≤ cexOutF x ∧
    cexOutF x ≤ xhat) ∧ ∀ x, xhat < x → cexOutF x < x :=
  modifiedT2_of_concave cexOut_hyp.f_cont cexOut_hyp.f_mono.monotoneOn cexOutF_props.1
    cexOut_hyp.f_pos (b := 5) (by norm_num) (by norm_num [cexOutF, cexf])

/-- In the example the solution of (1) satisfies `0 ≤ v ≤ 4 = 1/(1 − β)`. -/
theorem cexOut_bounds (μ : Measure (Icc (1 : ℝ) 2)) [IsProbabilityMeasure μ]
    {v : Icc (0 : ℝ) 5 →ᵇ ℝ} (hv : outT cexOut_hyp μ v = v) (x : Icc (0 : ℝ) 5) :
    0 ≤ v x ∧ v x ≤ 4 := by
  set C := {w : Icc (0 : ℝ) 5 →ᵇ ℝ | ∀ x, 0 ≤ w x ∧ w x ≤ 4}
  have hclosed : IsClosed C := by
    have : C = ⋂ x, ({w : Icc (0 : ℝ) 5 →ᵇ ℝ | 0 ≤ w x} ∩ {w | w x ≤ 4}) := by
      ext w; simp only [C, mem_iInter, mem_inter_iff]; exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun x => (isClosed_le continuous_const (continuous_eval_const _)).inter
      (isClosed_le (continuous_eval_const _) continuous_const)
  have hU : ∀ c, 0 ≤ c → 0 ≤ cexOutU c ∧ cexOutU c ≤ 1 := fun c hc => by
    simp only [cexOutU]
    have h1 := Real.exp_pos (-(20 * c))
    have h2 := Real.exp_le_one_iff.2 (show -(20 * c) ≤ 0 by linarith)
    constructor <;> linarith
  have hmaps : MapsTo (outT cexOut_hyp μ) C C := by
    intro w hw x
    obtain ⟨y, hy, hval, hmax⟩ := exists_outT_argmax cexOut_hyp μ w x
    have hint := integrable_outNext cexOut_hyp μ w
    have hE : ∀ y, 0 ≤ ∫ z, w (outNext cexOut_hyp y z) ∂μ ∧
        ∫ z, w (outNext cexOut_hyp y z) ∂μ ≤ 4 := fun y => by
      refine ⟨integral_nonneg fun z => (hw _).1, ?_⟩
      have := integral_mono (hint y) (integrable_const (4 : ℝ)) fun z => (hw _).2
      simpa using this
    have h0 : (⟨0, le_rfl, by norm_num⟩ : Icc (0 : ℝ) 5) ∈ outΓ 5 x := x.2.1
    have hm := hmax _ h0
    rw [outObj_of_le cexOut_hyp μ w h0] at hm
    rw [outObj_of_le cexOut_hyp μ w hy] at hval
    have hy' : y.1 ≤ x.1 := hy
    have hU0 := hU (x.1 - 0) (by linarith [x.2.1])
    have hUy := hU (x.1 - y.1) (by linarith)
    have hE0 := hE ⟨0, le_rfl, by norm_num⟩
    have hEy := hE y
    constructor <;> nlinarith
  have hne : C.Nonempty := ⟨const _ 0, fun _ => by simp⟩
  exact (corollary_1 (outT_contraction cexOut_hyp μ) hv hne hclosed hmaps hmaps).1 x

/-- In the example `v` is Lipschitz with constant `24/5` on outputs `s ≥ f(0) = 5/6`: by
concavity, `s (v(s′) − v(s)) ≤ (s′ − s)(v(s) − v(0)) ≤ 4(s′ − s)`. -/
theorem cexOut_lipschitz (μ : Measure (Icc (1 : ℝ) 2)) [IsProbabilityMeasure μ]
    {v : Icc (0 : ℝ) 5 →ᵇ ℝ} (hv : outT cexOut_hyp μ v = v) {s s' : Icc (0 : ℝ) 5}
    (hs : 5 / 6 ≤ s.1) (hss : s.1 ≤ s'.1) : v s' - v s ≤ 24 / 5 * (s'.1 - s.1) := by
  have hvc := out_concave cexOut_hyp μ cexOutU_props.1.concaveOn cexOutF_props.1 hv
  have hs' : 0 < s'.1 := by linarith
  set θ := s.1 / s'.1
  have hθ : θ * s'.1 = s.1 := div_mul_cancel₀ _ hs'.ne'
  have h0 : 0 ≤ θ := div_nonneg (by linarith) hs'.le
  have h1 : θ ≤ 1 := (div_le_one hs').2 hss
  have hc := hvc s' ⟨0, le_rfl, by norm_num⟩ θ h0 h1
  have hcm : cmb (convex_Icc 0 5) h0 h1 s' ⟨0, le_rfl, by norm_num⟩ = s := by
    ext1; rw [cmb_val]; simp [hθ]
  rw [hcm] at hc
  have hb := cexOut_bounds μ hv s
  have hb0 := cexOut_bounds μ hv ⟨0, le_rfl, by norm_num⟩
  have key : s.1 * (v s' - v s) ≤ (s'.1 - s.1) * 4 := by
    have h1 := mul_le_mul_of_nonneg_left hc hs'.le
    have e1 : s'.1 * (θ * v s' + (1 - θ) * v ⟨0, le_rfl, by norm_num⟩) =
        s.1 * v s' + (s'.1 - s.1) * v ⟨0, le_rfl, by norm_num⟩ := by
      rw [← hθ]; ring
    rw [e1] at h1
    have h2 := mul_le_mul_of_nonneg_left
      (show v s - v ⟨0, le_rfl, by norm_num⟩ ≤ 4 by linarith [hb.2, hb0.1]) (sub_nonneg.2 hss)
    nlinarith
  by_cases hd : v s' - v s ≤ 0
  · nlinarith
  · nlinarith

/-- **Exercise 13.3b, counterexample** (NOTE p. 392). With `U(c) = 1 − e^{−20c}`,
`f(y) = 5/6 + 2y/(1 + y)`, `β = 3/4`, `z̄ = 2`, `x̄ = 5` — which satisfy every assumption of
§13.3, including `U` `C¹` on `[0, ∞)`, `f(0) > 0`, `βf′(0) = 3/2 > 1` and `x̄ = z̄ f(x̄)` — and
any shock distribution `μ`, the only optimal choice at output `x ≤ 1/100` is `y = 0` (any `y`
attaining `v(x)` is `0`): the
marginal utility `20e^{−20x} ≥ 16` exceeds the bound `β · (24/5) · z̄ · f′(0) = 72/5` on the
marginal value of saving. -/
theorem ex_13_3b_counterexample (μ : Measure (Icc (1 : ℝ) 2)) [IsProbabilityMeasure μ]
    {v : Icc (0 : ℝ) 5 →ᵇ ℝ} (hv : outT cexOut_hyp μ v = v) {x y : Icc (0 : ℝ) 5}
    (hx : x.1 ≤ 1 / 100)
    (hopt : v x = cexOutU (x.1 - y.1) + 3 / 4 * ∫ z, v (outNext cexOut_hyp y z) ∂μ) :
    y.1 = 0 := by
  set y0 : Icc (0 : ℝ) 5 := ⟨0, le_rfl, by norm_num⟩
  have h0 : y0.1 ≤ x.1 := x.2.1
  obtain ⟨-, -, -, hmax⟩ := exists_outT_argmax cexOut_hyp μ v x
  have hm := hmax y0 h0
  rw [outObj_of_le cexOut_hyp μ v h0, hv] at hm
  have hint := integrable_outNext cexOut_hyp μ v
  -- the marginal value of saving
  have hpt : ∀ z, v (outNext cexOut_hyp y z) - v (outNext cexOut_hyp y0 z) ≤ 96 / 5 * y.1 := by
    intro z
    have hz1 := z.2.1
    have hz2 := z.2.2
    have hfy : cexf y.1 ≤ 2 * y.1 :=
      div_le_self (by linarith [y.2.1]) (by linarith [y.2.1])
    have hfy0 : 0 ≤ cexf y.1 := by simp only [cexf]; have := y.2.1; positivity
    have hs : 5 / 6 ≤ (outNext cexOut_hyp y0 z).1 := by
      change 5 / 6 ≤ cexOutF 0 * z.1
      simp only [cexOutF, cexf]
      nlinarith
    have hss : (outNext cexOut_hyp y0 z).1 ≤ (outNext cexOut_hyp y z).1 := by
      change cexOutF 0 * z.1 ≤ cexOutF y.1 * z.1
      have : cexf 0 = 0 := by simp [cexf]
      simp only [cexOutF, this, add_zero]
      nlinarith
    have := cexOut_lipschitz μ hv hs hss
    have e : (outNext cexOut_hyp y z).1 - (outNext cexOut_hyp y0 z).1 = cexf y.1 * z.1 := by
      change cexOutF y.1 * z.1 - cexOutF 0 * z.1 = _
      simp only [cexOutF, cexf]
      ring
    rw [e] at this
    nlinarith
  have hE : ∫ z, v (outNext cexOut_hyp y z) ∂μ - ∫ z, v (outNext cexOut_hyp y0 z) ∂μ ≤
      96 / 5 * y.1 := by
    rw [← integral_sub (hint y) (hint y0)]
    have := integral_mono ((hint y).sub (hint y0)) (integrable_const (96 / 5 * y.1)) hpt
    simpa using this
  -- the marginal utility of consumption
  have hU : 16 * y.1 ≤ cexOutU (x.1 - 0) - cexOutU (x.1 - y.1) := by
    simp only [cexOutU, sub_zero]
    have e : Real.exp (-(20 * (x.1 - y.1))) = Real.exp (-(20 * x.1)) * Real.exp (20 * y.1) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h1 : 4 / 5 ≤ Real.exp (-(20 * x.1)) := by
      linarith [Real.add_one_le_exp (-(20 * x.1))]
    have h2 : 20 * y.1 ≤ Real.exp (20 * y.1) - 1 := by linarith [Real.add_one_le_exp (20 * y.1)]
    have hy0 : 0 ≤ y.1 := y.2.1
    nlinarith
  have : y.1 ≤ 0 := by nlinarith
  exact le_antisymm this y.2.1

/-- **Exercise 13.3b, corrected.** In the example every selection `g` from the policy
correspondence has `g(x) = 0` on `[0, 1/100]`: so `0 < g(x)` fails for `0 < x ≤ 1/100` and `g`
is not strictly increasing. -/
theorem ex_13_3b_not_strictMono (μ : Measure (Icc (1 : ℝ) 2)) [IsProbabilityMeasure μ]
    {v : Icc (0 : ℝ) 5 →ᵇ ℝ} (hv : outT cexOut_hyp μ v = v) {g : Icc (0 : ℝ) 5 → Icc (0 : ℝ) 5}
    (hg : ∀ x, (g x).1 ≤ x.1 ∧
      v x = cexOutU (x.1 - (g x).1) + 3 / 4 * ∫ z, v (outNext cexOut_hyp (g x) z) ∂μ) :
    (∀ x : Icc (0 : ℝ) 5, x.1 ≤ 1 / 100 → (g x).1 = 0) ∧ ¬ StrictMono g ∧
      ¬ ∀ x : Icc (0 : ℝ) 5, 0 < x.1 → 0 < (g x).1 := by
  have hz : ∀ x : Icc (0 : ℝ) 5, x.1 ≤ 1 / 100 → (g x).1 = 0 := fun x hx =>
    ex_13_3b_counterexample μ hv hx (hg x).2
  refine ⟨hz, fun hmono => ?_, fun hpos => ?_⟩
  · have hlt : (⟨0, le_rfl, by norm_num⟩ : Icc (0 : ℝ) 5) < ⟨1 / 100, by norm_num, by norm_num⟩ :=
      show (0 : ℝ) < 1 / 100 by norm_num
    have := hmono hlt
    have h1 := hz ⟨0, le_rfl, by norm_num⟩ (by norm_num)
    have h2 := hz ⟨1 / 100, by norm_num, by norm_num⟩ le_rfl
    have : (g ⟨0, le_rfl, by norm_num⟩).1 < (g ⟨1 / 100, by norm_num, by norm_num⟩).1 := this
    linarith
  · have := hpos ⟨1 / 100, by norm_num, by norm_num⟩ (by norm_num)
    rw [hz _ le_rfl] at this
    exact lt_irrefl _ this

end StokeyLucasPrescott.ConvergenceApplications
