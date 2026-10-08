/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Power means

The Kreps–Porteus certainty equivalent `M_p(v) = (∫ v^p dμ)^{1/p}`, `p ≠ 0`, on positive bounded
measurable functions, for a probability measure `μ`. It is monotone, fixes constants and is
positively homogeneous; it is superadditive, hence concave, for `p ≤ 1`, and subadditive, hence
convex, for `p ≥ 1`. The proof normalises `v` and `w` to unit power mean and applies the
concavity (`0 < p ≤ 1`) or convexity (`p < 0`, `p ≥ 1`) of `t ↦ t^p` to the convex combination
`(v + w)/(a + b) = (a/(a + b))(v/a) + (b/(a + b))(w/b)`.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

/-- `t ↦ t^p` is convex on `(0, ∞)` for `p < 0`. -/
theorem convexOn_rpow_of_neg {p : ℝ} (hp : p < 0) : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ p := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    (fun t ht =>
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).continuousAt.continuousWithinAt)
    (by
      rw [interior_Ioi]
      exact fun t ht =>
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).differentiableAt.differentiableWithinAt)
    ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  rw [Real.deriv_rpow_const, Real.deriv_rpow_const]
  have h1 : t ^ (p - 1) ≤ s ^ (p - 1) := Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Positive, bounded, bounded-away-from-zero measurable functions. -/
def PosBdd (v : Ω → ℝ) : Prop :=
  Measurable v ∧ ∃ lo hi : ℝ, 0 < lo ∧ ∀ x, v x ∈ Icc lo hi

/-- The power mean `M_p(v) = (∫ v^p dμ)^{1/p}`. -/
noncomputable def pmean (p : ℝ) (v : Ω → ℝ) : ℝ := (∫ x, v x ^ p ∂μ) ^ p⁻¹

variable {μ}

theorem PosBdd.pos {v : Ω → ℝ} (hv : PosBdd v) (x : Ω) : 0 < v x := by
  obtain ⟨-, lo, hi, hlo, h⟩ := hv
  exact hlo.trans_le (h x).1

theorem PosBdd.integrable_rpow {v : Ω → ℝ} (hv : PosBdd v) (p : ℝ) :
    Integrable (fun x => v x ^ p) μ := by
  obtain ⟨hm, lo, hi, hlo, h⟩ := hv
  refine Integrable.of_bound (hm.pow_const p).aestronglyMeasurable (lo ^ p + hi ^ p)
    (Eventually.of_forall fun x => ?_)
  have hx := h x
  have hpos : 0 < v x := hlo.trans_le hx.1
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  rcases le_total 0 p with hp | hp
  · exact (Real.rpow_le_rpow hpos.le hx.2 hp).trans
      (le_add_of_nonneg_left (Real.rpow_pos_of_pos hlo _).le)
  · exact (Real.rpow_le_rpow_of_nonpos hlo hx.1 hp).trans
      (le_add_of_nonneg_right (Real.rpow_pos_of_pos (hlo.trans_le (hx.1.trans hx.2)) _).le)

theorem PosBdd.integral_rpow_pos {v : Ω → ℝ} (hv : PosBdd v) (p : ℝ) :
    0 < ∫ x, v x ^ p ∂μ := by
  have heq : (fun x => v x ^ p) = fun x => Real.exp (Real.log (v x) * p) :=
    funext fun x => Real.rpow_def_of_pos (hv.pos x) p
  rw [heq]
  exact integral_exp_pos (by rw [← heq]; exact hv.integrable_rpow p)

theorem PosBdd.pmean_pos {v : Ω → ℝ} (hv : PosBdd v) (p : ℝ) : 0 < pmean μ p v :=
  Real.rpow_pos_of_pos (hv.integral_rpow_pos p) _

theorem PosBdd.add {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) : PosBdd (v + w) := by
  obtain ⟨hm, lo, hi, hlo, h⟩ := hv
  obtain ⟨hm', lo', hi', hlo', h'⟩ := hw
  exact ⟨hm.add hm', lo + lo', hi + hi', by linarith, fun x =>
    ⟨add_le_add (h x).1 (h' x).1, add_le_add (h x).2 (h' x).2⟩⟩

theorem PosBdd.smul {v : Ω → ℝ} (hv : PosBdd v) {c : ℝ} (hc : 0 < c) : PosBdd (c • v) := by
  obtain ⟨hm, lo, hi, hlo, h⟩ := hv
  exact ⟨hm.const_smul c, c * lo, c * hi, mul_pos hc hlo, fun x =>
    ⟨mul_le_mul_of_nonneg_left (h x).1 hc.le, mul_le_mul_of_nonneg_left (h x).2 hc.le⟩⟩

theorem posBdd_const {c : ℝ} (hc : 0 < c) : PosBdd (fun _ : Ω => c) :=
  ⟨measurable_const, c, c, hc, fun _ => ⟨le_rfl, le_rfl⟩⟩

/-- `M_p` fixes constants. -/
theorem pmean_const {p : ℝ} (hp : p ≠ 0) {c : ℝ} (hc : 0 < c) :
    pmean μ p (fun _ => c) = c := by
  rw [pmean, integral_const, probReal_univ, one_smul, Real.rpow_rpow_inv hc.le hp]

/-- `M_p` is monotone. -/
theorem pmean_mono {p : ℝ} (hp : p ≠ 0) {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w)
    (h : v ≤ w) : pmean μ p v ≤ pmean μ p w := by
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have hle : ∫ x, w x ^ p ∂μ ≤ ∫ x, v x ^ p ∂μ :=
      integral_mono (hw.integrable_rpow p) (hv.integrable_rpow p) fun x =>
        Real.rpow_le_rpow_of_nonpos (hv.pos x) (h x) hneg.le
    exact Real.rpow_le_rpow_of_nonpos (hw.integral_rpow_pos p) hle (inv_nonpos.2 hneg.le)
  · have hle : ∫ x, v x ^ p ∂μ ≤ ∫ x, w x ^ p ∂μ :=
      integral_mono (hv.integrable_rpow p) (hw.integrable_rpow p) fun x =>
        Real.rpow_le_rpow (hv.pos x).le (h x) hpos.le
    exact Real.rpow_le_rpow (hv.integral_rpow_pos p).le hle (inv_nonneg.2 hpos.le)

/-- `M_p` is positively homogeneous. -/
theorem pmean_smul {p : ℝ} (hp : p ≠ 0) {v : Ω → ℝ} (hv : PosBdd v) {c : ℝ} (hc : 0 < c) :
    pmean μ p (c • v) = c * pmean μ p v := by
  have heq : (fun x => (c • v) x ^ p) = fun x => c ^ p * v x ^ p := funext fun x => by
    rw [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hc.le (hv.pos x).le]
  rw [pmean, pmean, heq, integral_const_mul,
    Real.mul_rpow (Real.rpow_pos_of_pos hc _).le (hv.integral_rpow_pos p).le,
    Real.rpow_rpow_inv hc.le hp]

/-- The normalised power mean: `∫ (v/a)^p = 1` for `a = M_p(v)`. -/
theorem integral_rpow_normalize {p : ℝ} (hp : p ≠ 0) {v : Ω → ℝ} (hv : PosBdd v) :
    ∫ x, ((pmean μ p v)⁻¹ * v x) ^ p ∂μ = 1 := by
  have ha := hv.pmean_pos (μ := μ) p
  have heq : (fun x => ((pmean μ p v)⁻¹ * v x) ^ p) =
      fun x => ((pmean μ p v) ^ p)⁻¹ * v x ^ p := funext fun x => by
    rw [Real.mul_rpow (inv_pos.2 ha).le (hv.pos x).le, Real.inv_rpow ha.le]
  rw [heq, integral_const_mul, pmean, Real.rpow_inv_rpow (hv.integral_rpow_pos p).le hp,
    inv_mul_cancel₀ (hv.integral_rpow_pos p).ne']

/-- The level-set inequality: if `t ↦ t^p` is convex on `(0, ∞)`, then
`∫ (v + w)^p ≤ (M_p v + M_p w)^p`. -/
theorem integral_rpow_add_le {p : ℝ} (hp : p ≠ 0) (hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ p)
    {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) :
    ∫ x, (v x + w x) ^ p ∂μ ≤ (pmean μ p v + pmean μ p w) ^ p := by
  set a := pmean μ p v
  set b := pmean μ p w
  have ha : 0 < a := hv.pmean_pos p
  have hb : 0 < b := hw.pmean_pos p
  have hab : 0 < a + b := by linarith
  have hpt : ∀ x, ((a + b)⁻¹ * (v x + w x)) ^ p ≤
      a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p := fun x => by
    have hcomb : (a + b)⁻¹ * (v x + w x) =
        a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := by field_simp
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv.pos x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw.pos x))
      (by positivity) (by positivity) (by field_simp)
  have hiv : Integrable (fun x => (a⁻¹ * v x) ^ p) μ := (hv.smul (inv_pos.2 ha)).integrable_rpow p
  have hiw : Integrable (fun x => (b⁻¹ * w x) ^ p) μ := (hw.smul (inv_pos.2 hb)).integrable_rpow p
  have hivw : Integrable (fun x => ((a + b)⁻¹ * (v x + w x)) ^ p) μ :=
    ((hv.add hw).smul (inv_pos.2 hab)).integrable_rpow p
  have hint : ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ ≤
      ∫ x, (a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p) ∂μ :=
    integral_mono hivw ((hiv.const_mul _).add (hiw.const_mul _)) hpt
  rw [integral_add (hiv.const_mul _) (hiw.const_mul _), integral_const_mul, integral_const_mul,
    integral_rpow_normalize hp hv, integral_rpow_normalize hp hw] at hint
  have h1 : ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ =
      ((a + b) ^ p)⁻¹ * ∫ x, (v x + w x) ^ p ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ((a + b)⁻¹ * (v x + w x)) ^ p = ((a + b) ^ p)⁻¹ * (v x + w x) ^ p
    rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv.pos x) (hw.pos x)).le, Real.inv_rpow hab.le]
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2] at hint
  have h3 : 0 < (a + b) ^ p := Real.rpow_pos_of_pos hab _
  rwa [inv_mul_le_iff₀ h3, mul_one] at hint

/-- The concave counterpart: if `t ↦ t^p` is concave on `(0, ∞)`, then
`(M_p v + M_p w)^p ≤ ∫ (v + w)^p`. -/
theorem le_integral_rpow_add {p : ℝ} (hp : p ≠ 0) (hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ p)
    {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) :
    (pmean μ p v + pmean μ p w) ^ p ≤ ∫ x, (v x + w x) ^ p ∂μ := by
  set a := pmean μ p v
  set b := pmean μ p w
  have ha : 0 < a := hv.pmean_pos p
  have hb : 0 < b := hw.pmean_pos p
  have hab : 0 < a + b := by linarith
  have hpt : ∀ x, a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p ≤
      ((a + b)⁻¹ * (v x + w x)) ^ p := fun x => by
    have hcomb : (a + b)⁻¹ * (v x + w x) =
        a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := by field_simp
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv.pos x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw.pos x))
      (by positivity) (by positivity) (by field_simp)
  have hiv : Integrable (fun x => (a⁻¹ * v x) ^ p) μ := (hv.smul (inv_pos.2 ha)).integrable_rpow p
  have hiw : Integrable (fun x => (b⁻¹ * w x) ^ p) μ := (hw.smul (inv_pos.2 hb)).integrable_rpow p
  have hivw : Integrable (fun x => ((a + b)⁻¹ * (v x + w x)) ^ p) μ :=
    ((hv.add hw).smul (inv_pos.2 hab)).integrable_rpow p
  have hint : ∫ x, (a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p) ∂μ ≤
      ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ :=
    integral_mono ((hiv.const_mul _).add (hiw.const_mul _)) hivw hpt
  rw [integral_add (hiv.const_mul _) (hiw.const_mul _), integral_const_mul, integral_const_mul,
    integral_rpow_normalize hp hv, integral_rpow_normalize hp hw] at hint
  have h1 : ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ =
      ((a + b) ^ p)⁻¹ * ∫ x, (v x + w x) ^ p ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ((a + b)⁻¹ * (v x + w x)) ^ p = ((a + b) ^ p)⁻¹ * (v x + w x) ^ p
    rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv.pos x) (hw.pos x)).le, Real.inv_rpow hab.le]
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2] at hint
  have h3 : 0 < (a + b) ^ p := Real.rpow_pos_of_pos hab _
  rwa [le_inv_mul_iff₀ h3, mul_one] at hint

/-- `M_p` is superadditive for `p ≤ 1`, `p ≠ 0`. -/
theorem pmean_add_ge {p : ℝ} (hp : p ≠ 0) (hp1 : p ≤ 1) {v w : Ω → ℝ} (hv : PosBdd v)
    (hw : PosBdd w) : pmean μ p v + pmean μ p w ≤ pmean μ p (v + w) := by
  have hab : 0 < pmean μ p v + pmean μ p w := add_pos (hv.pmean_pos p) (hw.pmean_pos p)
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have h1 := integral_rpow_add_le hp (convexOn_rpow_of_neg hneg) hv hw (μ := μ)
    have h2 := Real.rpow_le_rpow_of_nonpos ((hv.add hw).integral_rpow_pos p) h1
      (inv_nonpos.2 hneg.le)
    rwa [Real.rpow_rpow_inv hab.le hp] at h2
  · have hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ p :=
      (Real.concaveOn_rpow hpos.le hp1).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h1 := le_integral_rpow_add hp hφ hv hw (μ := μ)
    have h2 := Real.rpow_le_rpow (Real.rpow_pos_of_pos hab _).le h1 (inv_nonneg.2 hpos.le)
    rwa [Real.rpow_rpow_inv hab.le hp] at h2

/-- `M_p` is subadditive for `p ≥ 1` (Minkowski). -/
theorem pmean_add_le {p : ℝ} (hp1 : 1 ≤ p) {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) :
    pmean μ p (v + w) ≤ pmean μ p v + pmean μ p w := by
  have hp : p ≠ 0 := by linarith
  have hab : 0 < pmean μ p v + pmean μ p w := add_pos (hv.pmean_pos p) (hw.pmean_pos p)
  have hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ p :=
    (convexOn_rpow hp1).subset Ioi_subset_Ici_self (convex_Ioi 0)
  have h1 := integral_rpow_add_le hp hφ hv hw (μ := μ)
  have h2 := Real.rpow_le_rpow ((hv.add hw).integral_rpow_pos p).le h1
    (inv_nonneg.2 (zero_le_one.trans hp1))
  rwa [Real.rpow_rpow_inv hab.le hp] at h2

/-- Concavity of `M_p` along a convex combination, `p ≤ 1`, `p ≠ 0`. -/
theorem pmean_concave {p : ℝ} (hp : p ≠ 0) (hp1 : p ≤ 1) {v w : Ω → ℝ} (hv : PosBdd v)
    (hw : PosBdd w) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * pmean μ p v + b * pmean μ p w ≤ pmean μ p (a • v + b • w) := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h := pmean_add_ge hp hp1 (hv.smul ha') (hw.smul hb') (μ := μ)
      rwa [pmean_smul hp hv ha', pmean_smul hp hw hb'] at h
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-- Convexity of `M_p` along a convex combination, `p ≥ 1`. -/
theorem pmean_convex {p : ℝ} (hp1 : 1 ≤ p) {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    pmean μ p (a • v + b • w) ≤ a * pmean μ p v + b * pmean μ p w := by
  have hp : p ≠ 0 := by linarith
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h := pmean_add_le hp1 (hv.smul ha') (hw.smul hb') (μ := μ)
      rwa [pmean_smul hp hv ha', pmean_smul hp hw hb'] at h
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

end SargentStachurski.AdditionalApplications
