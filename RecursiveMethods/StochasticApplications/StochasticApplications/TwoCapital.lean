/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.GrowthPolicy

/-!
# Optimal growth with two capital goods

SLP §10.2, p. 290: one output `z f(x₁, x₂)`, consumed or invested in either capital good, which
depreciates fully: `0 ≤ y₁, y₂` and `y₁ + y₂ ≤ z f(x₁, x₂)`. The capital stocks lie in
`X = {x ≥ 0 : x₁ + x₂ ≤ x̄}` and the shocks in `Z = [1, z̄]`, with any Feller transition `Q`.

* **Exercise 10.2a** (`ex_10_2a`): if `z̄ f(x) < x₁ + x₂` whenever `x₁ + x₂ > x̄` (the analogue of
  (T2)), the set of sustainable stocks `{x ≥ 0 : x₁ + x₂ ≤ z̄ f(x)}` is compact and lies in `X`.
  The analysis on `X` uses `z̄ f(x) ≤ x̄` on `X` (`TwoHyp`).
* **Exercise 10.2b** (`two_boundedDP`, `ex_10_2b`, `ex_10_2b_diff`). The hypotheses of §9.2
  hold, so (2) has a unique bounded continuous solution `v`; it is strictly increasing. If `f` is
  strictly concave, `v(·, z)` is strictly concave, the policy is a continuous function `g`, the
  plans it generates are optimal (`v = v*`), and `v` is differentiable where consumption is
  positive, with `Dv(x, z) = U′(c) z Df(x)`. **Correction:** (T4) asks only that `f` be concave,
  and then both claims fail. With `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)` (`ex_10_2b_counterexample`),
  `v(x, z)` depends on `x` only through `x₁ + x₂`, so `v(·, z)` is affine along
  `x₁ + x₂ = 1`; and at `x = (3, 0)`, `z = 2`, saving is optimal, and any optimal saving `k > 0`
  can be held as `(k, 0)` or `(0, k)`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The nonnegative quadrant `ℝ²₊`. -/
def quadrant : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

/-- The capital stocks `X = {x ∈ ℝ²₊ : x₁ + x₂ ≤ x̄}`. -/
def twoX (xbar : ℝ) : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ xbar}

theorem convex_quadrant : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb _
  exact ⟨by simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; nlinarith [hx.1, hy.1],
    by simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; nlinarith [hx.2, hy.2]⟩

theorem convex_twoX (xbar : ℝ) : Convex ℝ (twoX xbar) := by
  intro x hx y hy a b ha hb hab
  simp only [twoX, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith

theorem isCompact_twoX (xbar : ℝ) : IsCompact (twoX xbar) := by
  have hb : Bornology.IsBounded (twoX xbar) :=
    (Metric.isBounded_Icc ((0, 0) : ℝ × ℝ) (xbar, xbar)).subset fun x hx =>
      ⟨⟨hx.1, hx.2.1⟩, ⟨by linarith [hx.2.2, hx.2.1], by linarith [hx.2.2, hx.1]⟩⟩
  have hc : IsClosed (twoX xbar) := by
    have h1 : IsClosed {b : ℝ × ℝ | 0 ≤ b.1} := isClosed_le continuous_const continuous_fst
    have h2 : IsClosed {b : ℝ × ℝ | 0 ≤ b.2} := isClosed_le continuous_const continuous_snd
    have h3 : IsClosed {b : ℝ × ℝ | b.1 + b.2 ≤ xbar} :=
      isClosed_le (by fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  exact Metric.isCompact_of_isClosed_isBounded hc hb

theorem twoX_subset_quadrant {xbar : ℝ} {x : ℝ × ℝ} (hx : x ∈ twoX xbar) : x ∈ quadrant :=
  ⟨hx.1, hx.2.1⟩

/-- (U1)–(U3), (T1) and (T3) for `f : ℝ²₊ → ℝ`, (Z1), and the answer to Exercise 10.2a in the form
used: `z̄ f(x) ≤ x̄` on `X`. -/
structure TwoHyp (U : ℝ → ℝ) (f : ℝ × ℝ → ℝ) (β xbar zbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f quadrant
  f_zero : f 0 = 0
  f_mono : ∀ x x' : ℝ × ℝ, x ∈ quadrant → x ≤ x' → x ≠ x' → f x < f x'
  zbar_gt : 1 < zbar
  xbar_pos : 0 < xbar
  f_bound : ∀ x ∈ twoX xbar, zbar * f x ≤ xbar

variable {U : ℝ → ℝ} {f : ℝ × ℝ → ℝ} {β xbar zbar : ℝ}

theorem TwoHyp.f_le (h : TwoHyp U f β xbar zbar) {x x' : ℝ × ℝ} (hx : x ∈ quadrant)
    (hxx' : x ≤ x') : f x ≤ f x' := by
  rcases eq_or_ne x x' with rfl | hne
  · exact le_rfl
  · exact (h.f_mono x x' hx hxx' hne).le

theorem TwoHyp.f_nonneg (h : TwoHyp U f β xbar zbar) {x : ℝ × ℝ} (hx : x ∈ quadrant) :
    0 ≤ f x := by
  have := h.f_le (show (0 : ℝ × ℝ) ∈ quadrant from ⟨le_rfl, le_rfl⟩)
    (show (0 : ℝ × ℝ) ≤ x from ⟨hx.1, hx.2⟩)
  rwa [h.f_zero] at this

theorem TwoHyp.continuous_f (h : TwoHyp U f β xbar zbar) :
    Continuous fun x : twoX xbar => f x.1 :=
  h.f_cont.comp_continuous continuous_subtype_val fun x => twoX_subset_quadrant x.2

theorem TwoHyp.zf_nonneg (h : TwoHyp U f β xbar zbar) (s : twoX xbar × Icc (1 : ℝ) zbar) :
    0 ≤ s.2.1 * f s.1.1 :=
  mul_nonneg (by linarith [s.2.2.1]) (h.f_nonneg (twoX_subset_quadrant s.1.2))

theorem TwoHyp.zf_le (h : TwoHyp U f β xbar zbar) (s : twoX xbar × Icc (1 : ℝ) zbar) :
    s.2.1 * f s.1.1 ≤ xbar :=
  (mul_le_mul_of_nonneg_right s.2.2.2 (h.f_nonneg (twoX_subset_quadrant s.1.2))).trans
    (h.f_bound _ s.1.2)

/-- `Γ(x, z) = {y ∈ X : y₁ + y₂ ≤ z f(x)}`. -/
def twoΓ (f : ℝ × ℝ → ℝ) (xbar zbar : ℝ) (s : twoX xbar × Icc (1 : ℝ) zbar) : Set (twoX xbar) :=
  {y | y.1.1 + y.1.2 ≤ s.2.1 * f s.1.1}

/-- `F(x, y, z) = U[z f(x) − y₁ − y₂]`, with consumption clamped at `0` off the graph. -/
def twoF (U : ℝ → ℝ) (f : ℝ × ℝ → ℝ) (xbar zbar : ℝ)
    (p : twoX xbar × twoX xbar × Icc (1 : ℝ) zbar) : ℝ :=
  U (max (p.2.2.1 * f p.1.1 - (p.2.1.1.1 + p.2.1.1.2)) 0)

/-- The two-capital model in the first formulation of Chapter 9. -/
abbrev twoModel (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) (U : ℝ → ℝ)
    (f : ℝ × ℝ → ℝ) (β xbar : ℝ) : Model (twoX xbar) (twoX xbar) (Icc (1 : ℝ) zbar) :=
  Model.first Q (twoΓ f xbar zbar) (twoF U f xbar zbar) β

theorem twoF_of_mem {x y : twoX xbar} {z : Icc (1 : ℝ) zbar} (hy : y ∈ twoΓ f xbar zbar (x, z)) :
    twoF U f xbar zbar (x, y, z) = U (z.1 * f x.1 - (y.1.1 + y.1.2)) := by
  have : 0 ≤ z.1 * f x.1 - (y.1.1 + y.1.2) := sub_nonneg.2 hy
  simp only [twoF, max_eq_left this]

theorem TwoHyp.continuous_F (h : TwoHyp U f β xbar zbar) : Continuous (twoF U f xbar zbar) :=
  h.U_cont.comp_continuous ((((continuous_subtype_val.comp continuous_snd.snd).mul
    (h.continuous_f.comp continuous_fst)).sub
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd.fst)).add
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd.fst)))).max
    continuous_const) fun _ => mem_Ici.2 (le_max_right _ _)

/-- The correspondence `s ↦ {y ∈ X : y₁ + y₂ ≤ c(s)}`, for continuous `c ≥ 0`, is l.h.c.: scale
`y` down by `min{1, c(sₙ)/(y₁ + y₂)}`. -/
theorem isLHC_twoX_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsLHC (fun s => {y : twoX xbar | y.1.1 + y.1.2 ≤ c s}) s := by
  refine ⟨⟨⟨0, le_rfl, le_rfl, by simpa using hx⟩, by simpa using h0 s⟩, fun y hy xs hxs => ?_⟩
  have hy' : y.1.1 + y.1.2 ≤ c s := hy
  rcases (add_nonneg y.2.1 y.2.2.1).lt_or_eq with hσ | hσ
  · set σ := y.1.1 + y.1.2
    set t : ℕ → ℝ := fun n => min 1 (c (xs n) / σ)
    have ht0 : ∀ n, 0 ≤ t n := fun n => le_min zero_le_one (div_nonneg (h0 _) hσ.le)
    have ht1 : ∀ n, t n ≤ 1 := fun n => min_le_left _ _
    have hmem : ∀ n, t n • y.1 ∈ twoX xbar := fun n => by
      simp only [twoX, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      refine ⟨mul_nonneg (ht0 n) y.2.1, mul_nonneg (ht0 n) y.2.2.1, ?_⟩
      have := y.2.2.2
      nlinarith [ht0 n, ht1 n]
    refine ⟨0, fun n => ⟨t n • y.1, hmem n⟩, fun n _ => ?_, ?_⟩
    · change (t n • y.1).1 + (t n • y.1).2 ≤ c (xs n)
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 : t n ≤ c (xs n) / σ := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 hσ.le
      rw [div_mul_cancel₀ _ hσ.ne'] at h2
      linarith
    · have htl : Tendsto t atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).min (((hc.tendsto s).comp hxs).div_const σ)
        rwa [min_eq_left ((one_le_div hσ).2 hy')] at this
      refine tendsto_subtype_rng.2 ?_
      simpa using htl.smul_const y.1
  · refine ⟨0, fun _ => y, fun n _ => ?_, tendsto_const_nhds⟩
    change y.1.1 + y.1.2 ≤ c (xs n)
    rw [← hσ]
    exact h0 _

/-- The correspondence `s ↦ {y ∈ X : y₁ + y₂ ≤ c(s)}`, for continuous `c ≥ 0`, is u.h.c. -/
theorem isUHC_twoX_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsUHC (fun s => {y : twoX xbar | y.1.1 + y.1.2 ≤ c s}) s := by
  have : CompactSpace (twoX xbar) := isCompact_iff_compactSpace.1 (isCompact_twoX xbar)
  refine ⟨⟨⟨0, le_rfl, le_rfl, by simpa using hx⟩, by simpa using h0 s⟩, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  refine ⟨y, ?_, φ, hφ, hlim⟩
  have hc' : Continuous fun y : twoX xbar => y.1.1 + y.1.2 :=
    (continuous_fst.comp continuous_subtype_val).add (continuous_snd.comp continuous_subtype_val)
  exact le_of_tendsto_of_tendsto ((hc'.tendsto y).comp hlim)
    ((hc.tendsto s).comp (hxs.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n => hys (φ n))

/-- The hypotheses of §9.2 hold for the two-capital model (Exercise 10.2b). -/
theorem two_boundedDP (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    BoundedDP (twoModel Q U f β xbar) := by
  have : CompactSpace (twoX xbar) := isCompact_iff_compactSpace.1 (isCompact_twoX xbar)
  have hzf : Continuous fun s : twoX xbar × Icc (1 : ℝ) zbar => s.2.1 * f s.1.1 :=
    (continuous_subtype_val.comp continuous_snd).mul (h.continuous_f.comp continuous_fst)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous_F.continuousOn
  exact ⟨fun s => ⟨⟨0, le_rfl, le_rfl, by simpa using h.xbar_pos.le⟩, by
      change (0 : ℝ) + 0 ≤ _; simpa using h.zf_nonneg s⟩,
    fun _ => IsClosed.isCompact (isClosed_le ((continuous_fst.comp continuous_subtype_val).add
      (continuous_snd.comp continuous_subtype_val)) continuous_const),
    isLHC_twoX_le hzf h.zf_nonneg h.xbar_pos.le, isUHC_twoX_le hzf h.zf_nonneg h.xbar_pos.le,
    h.continuous_F.continuousOn,
    ⟨B, fun p _ => by simpa [Real.norm_eq_abs] using hB p (mem_univ _)⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn, contExp_first Q _ _ β (lemma_9_5_compact Q hQ)⟩

/-- **Exercise 10.2a.** If `z̄ f(x) < x₁ + x₂` whenever `x ≥ 0` and `x₁ + x₂ > x̄`, the set of
sustainable capital stocks `{x ≥ 0 : x₁ + x₂ ≤ z̄ f(x)}` is compact and contained in `X`. -/
theorem ex_10_2a (hf : ContinuousOn f quadrant)
    (hT2 : ∀ x ∈ quadrant, xbar < x.1 + x.2 → zbar * f x < x.1 + x.2) :
    {x | x ∈ quadrant ∧ x.1 + x.2 ≤ zbar * f x} ⊆ twoX xbar ∧
      IsCompact {x | x ∈ quadrant ∧ x.1 + x.2 ≤ zbar * f x} := by
  have hsub : {x | x ∈ quadrant ∧ x.1 + x.2 ≤ zbar * f x} ⊆ twoX xbar := fun x hx => by
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    by_contra hlt
    have := hT2 x hx.1 (not_le.1 hlt)
    linarith [hx.2]
  refine ⟨hsub, (isCompact_twoX xbar).of_isClosed_subset ?_ hsub⟩
  have hq : IsClosed quadrant :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  have := (hf.const_smul zbar).sub (continuous_fst.add continuous_snd).continuousOn
    |>.preimage_isClosed_of_isClosed hq (isClosed_Ici (a := (0 : ℝ)))
  convert this using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici, Pi.sub_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, sub_nonneg]

/-! ### Exercise 10.2b -/

/-- **Exercise 10.2b** (monotonicity, Theorem 9.7): `v(·, z)` is strictly increasing. -/
theorem two_strictMono (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v = v) (z : Icc (1 : ℝ) zbar) :
    StrictMono fun x => v (x, z) := by
  refine theorem_9_7 Q _ _ β (two_boundedDP h Q hQ) (fun x x' y z hxx' hy => ?_)
    (fun x x' z hxx' y hy => ?_) hv z
  · have hy' : y.1.1 + y.1.2 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 < f x'.1 := h.f_mono x.1 x'.1 (twoX_subset_quadrant x.2) hxx'.le
      fun he => hxx'.ne (Subtype.ext he)
    have hz : 0 < z.1 := by linarith [z.2.1]
    have hlt : z.1 * f x.1 < z.1 * f x'.1 := mul_lt_mul_of_pos_left hfx hz
    rw [twoF_of_mem hy, twoF_of_mem (show y.1.1 + y.1.2 ≤ z.1 * f x'.1 by linarith)]
    exact h.U_mono (mem_Ici.2 (sub_nonneg.2 hy')) (mem_Ici.2 (by linarith)) (by linarith)
  · have hy' : y.1.1 + y.1.2 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 ≤ f x'.1 := h.f_le (twoX_subset_quadrant x.2) hxx'
    exact hy'.trans (mul_le_mul_of_nonneg_left hfx (by linarith [z.2.1]))

theorem two_cmb_val {x₀ x₁ : twoX xbar} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_twoX xbar) h0 h1 x₀ x₁).1.1 = θ * x₀.1.1 + (1 - θ) * x₁.1.1 ∧
      (cmb (convex_twoX xbar) h0 h1 x₀ x₁).1.2 = θ * x₀.1.2 + (1 - θ) * x₁.1.2 := by
  simp [cmb]

/-- Assumptions 9.10 and 9.11 hold when `U` is concave and `f` is strictly concave. -/
theorem two_assumptions (h : TwoHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : StrictConcaveOn ℝ quadrant f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) :
    Assumption910 (convex_twoX xbar) (convex_twoX xbar) (twoModel Q U f β xbar) ∧
      Assumption911 (convex_twoX xbar) (convex_twoX xbar) (twoModel Q U f β xbar) := by
  -- output at the mixture is at least the mixture of outputs
  have hout : ∀ (x x' : twoX xbar) (z : Icc (1 : ℝ) zbar) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * (z.1 * f x.1) + (1 - θ) * (z.1 * f x'.1) ≤
        z.1 * f (cmb (convex_twoX xbar) h0 h1 x x').1 := by
    intro x x' z θ h0 h1
    have hc := hf.concaveOn.2 (twoX_subset_quadrant x.2) (twoX_subset_quadrant x'.2) h0
      (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
    simp only [smul_eq_mul] at hc
    have hz : 0 ≤ z.1 := by linarith [z.2.1]
    change _ ≤ z.1 * f (θ • x.1 + (1 - θ) • x'.1)
    nlinarith [mul_le_mul_of_nonneg_left hc hz]
  have hmem : Assumption911 (convex_twoX xbar) (convex_twoX xbar) (twoModel Q U f β xbar) := by
    intro z x y x' y' hy hy' θ h0 h1
    have e := hout x x' z θ h0 h1
    have e0 : y.1.1 + y.1.2 ≤ z.1 * f x.1 := hy
    have e1 : y'.1.1 + y'.1.2 ≤ z.1 * f x'.1 := hy'
    change (cmb (convex_twoX xbar) h0 h1 y y').1.1 + (cmb (convex_twoX xbar) h0 h1 y y').1.2 ≤ _
    rw [(two_cmb_val h0 h1).1, (two_cmb_val h0 h1).2]
    nlinarith
  refine ⟨fun z x y x' y' hy hy' θ h0 h1 => ?_, hmem⟩
  have hyθ := hmem z x y x' y' hy hy' θ h0.le h1.le
  have e0 : 0 ≤ z.1 * f x.1 - (y.1.1 + y.1.2) := sub_nonneg.2 hy
  have e1 : 0 ≤ z.1 * f x'.1 - (y'.1.1 + y'.1.2) := sub_nonneg.2 hy'
  have hsum : (cmb (convex_twoX xbar) h0.le h1.le y y').1.1 +
      (cmb (convex_twoX xbar) h0.le h1.le y y').1.2 =
      θ * (y.1.1 + y.1.2) + (1 - θ) * (y'.1.1 + y'.1.2) := by
    rw [(two_cmb_val h0.le h1.le).1, (two_cmb_val h0.le h1.le).2]; ring
  have hUc := hU.2 e0 e1 h0.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hUc
  change θ * twoF U f xbar zbar (x, y, z) + (1 - θ) * twoF U f xbar zbar (x', y', z) ≤
      twoF U f xbar zbar (cmb (convex_twoX xbar) h0.le h1.le x x',
        cmb (convex_twoX xbar) h0.le h1.le y y', z) ∧
    (x ≠ x' → θ * twoF U f xbar zbar (x, y, z) + (1 - θ) * twoF U f xbar zbar (x', y', z) <
      twoF U f xbar zbar (cmb (convex_twoX xbar) h0.le h1.le x x',
        cmb (convex_twoX xbar) h0.le h1.le y y', z))
  rw [twoF_of_mem hy, twoF_of_mem hy', twoF_of_mem hyθ, hsum]
  have hθ0 : 0 ≤ θ * (z.1 * f x.1 - (y.1.1 + y.1.2)) +
      (1 - θ) * (z.1 * f x'.1 - (y'.1.1 + y'.1.2)) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have e := hout x x' z θ h0.le h1.le
  refine ⟨hUc.trans (h.U_mono.monotoneOn hθ0 ?_ ?_), fun hne => hUc.trans_lt (h.U_mono hθ0 ?_ ?_)⟩
  · simp only [mem_Ici]; nlinarith
  · nlinarith
  · simp only [mem_Ici]; nlinarith
  · have hfs := hf.2 (twoX_subset_quadrant x.2) (twoX_subset_quadrant x'.2)
      (fun he => hne (Subtype.ext he)) h0 (by linarith : (0 : ℝ) < 1 - θ) (by ring)
    simp only [smul_eq_mul] at hfs
    have hz : 0 < z.1 := by linarith [z.2.1]
    have := mul_lt_mul_of_pos_left hfs hz
    change _ < z.1 * f (θ • x.1 + (1 - θ) • x'.1) - _
    nlinarith

/-- **Exercise 10.2b.** With `U` concave and `f` strictly concave, there is a unique bounded
continuous solution `v` of the functional equation; `v(·, z)` is strictly increasing and strictly
concave; the policy correspondence is a continuous function `g`; and `v = v*`, attained by the
plans that `g` generates. -/
theorem ex_10_2b [Nonempty (twoX xbar)] (h : TwoHyp U f β xbar zbar)
    (hU : ConcaveOn ℝ (Ici 0) U) (hf : StrictConcaveOn ℝ quadrant f)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ,
      bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v = v ∧
      (∀ w, bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) w = w → w = v) ∧
      (∀ z, StrictMono fun x => v (x, z)) ∧
      (∀ z, IsStrictConcaveS (convex_twoX xbar) fun x => v (x, z)) ∧
      (∀ s, policy (twoModel Q U f β xbar) v s =
        {argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) s}) ∧
      Continuous (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v)) ∧
      ∀ s₀, vStar (twoModel Q U f β xbar) s₀ = v s₀ ∧
        planValue (twoModel Q U f β xbar) s₀ (genPlan (twoModel Q U f β xbar) s₀ fun _ =>
          argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v)) = v s₀ := by
  set M := twoModel Q U f β xbar
  have hb := two_boundedDP h Q hQ
  obtain ⟨v, hv, huniq, -, -⟩ := ex_9_7b M hb
  obtain ⟨h910, h911⟩ := two_assumptions h hU hf Q
  obtain ⟨hsc, hpol, hcont⟩ := theorem_9_8 Q _ _ β hb h910 h911 hv
  have hgG : ∀ s, argmaxFn (twoΓ f xbar zbar) (objG M v) s ∈ policy M v s := fun s => by
    rw [hpol s]; exact rfl
  have hopt := fun s₀ => bounded_vStar M hb measurable_snd.fst h.continuous_F.measurable hv
    (g := fun _ => argmaxFn (twoΓ f xbar zbar) (objG M v)) (fun _ => hcont.measurable)
    (fun _ => hgG) s₀
  exact ⟨v, hv, huniq, two_strictMono h Q hQ hv, hsc, hpol, hcont,
    fun s₀ => ⟨(hopt s₀).2.2, (hopt s₀).2.1⟩⟩

/-- **Exercise 10.2b** (differentiability, Theorem 9.10). With `f` strictly concave, at an interior
`x₀` where consumption `c = z₀ f(x₀) − g₁ − g₂` is positive, `U` is differentiable at `c` and `f`
at `x₀`: `Dv(x₀, z₀) = U′(c) z₀ Df(x₀)`. -/
theorem ex_10_2b_diff [Nonempty (twoX xbar)] (h : TwoHyp U f β xbar zbar)
    (hU : ConcaveOn ℝ (Ici 0) U) (hf : StrictConcaveOn ℝ quadrant f)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v = v) {x₀ : twoX xbar}
    {z₀ : Icc (1 : ℝ) zbar} (hint : twoX xbar ∈ 𝓝 x₀.1)
    (hc : (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.1 +
      (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.2 <
        z₀.1 * f x₀.1)
    {U' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 -
      ((argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.1 +
        (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.2)))
    {Df : ℝ × ℝ →L[ℝ] ℝ} (hf' : HasFDerivAt f Df x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) ((U' * z₀.1) • Df) x₀.1 := by
  set M := twoModel Q U f β xbar
  have hb := two_boundedDP h Q hQ
  obtain ⟨h910, h911⟩ := two_assumptions h hU hf Q
  set g₀ := argmaxFn (twoΓ f xbar zbar) (objG M v) (x₀, z₀)
  set k₀ := g₀.1.1 + g₀.1.2
  have hev : ∀ᶠ x in 𝓝 x₀, g₀ ∈ M.Γ (x, z₀) := by
    have := ((continuous_const.mul h.continuous_f).tendsto x₀).eventually (lt_mem_nhds hc)
    exact this.mono fun x hx => hx.le
  have hL : HasFDerivAt (fun x => U (z₀.1 * f x - k₀)) ((U' * z₀.1) • Df) x₀.1 := by
    have := hU'.comp_hasFDerivAt x₀.1 ((hf'.const_mul z₀.1).sub_const k₀)
    rwa [smul_smul] at this
  refine ex_9_7f' M hb h910 h911 (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ hne => hne) hv
    (fun _ _ _ _ => rfl) hint hev (hL.congr_of_eventuallyEq ?_)
  have hev' : ∀ᶠ x in 𝓝 x₀.1, k₀ < z₀.1 * f x :=
    ((hf'.continuousAt.const_mul z₀.1).eventually (lt_mem_nhds hc))
  filter_upwards [hev', hint] with x hx hxS
  rw [liftS_of_mem _ hxS]
  exact twoF_of_mem (x := ⟨x, hxS⟩) (z := z₀) (y := g₀) hx.le

/-! ### Weakly concave `f`: a counterexample -/

/-- `T` sees the capital stock only through output: if `f(x) = f(x′)` then
`(Tw)(x, z) = (Tw)(x′, z)`. -/
theorem two_bellman_eq_of_f_eq (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (w : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ) {x x' : twoX xbar} (hxx' : f x.1 = f x'.1)
    (z : Icc (1 : ℝ) zbar) :
    bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) w (x, z) =
      bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) w (x', z) := by
  simp only [bellman_apply, maxValue, objG, rhs, expV, twoΓ, twoF, hxx']

/-- `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)`: concave and strictly increasing, but not strictly
concave. -/
noncomputable def cexf2 (x : ℝ × ℝ) : ℝ := cexf (x.1 + x.2)

theorem cexf2_hyp : TwoHyp cexU cexf2 (1 / 10) 3 2 where
  β_pos := by norm_num
  β_lt := by norm_num
  U_cont := cex_hyp.U_cont
  U_mono := cex_hyp.U_mono
  f_cont := cex_hyp.f_cont.comp (continuous_fst.add continuous_snd).continuousOn
    fun x hx => mem_Ici.2 (add_nonneg hx.1 hx.2)
  f_zero := by simp [cexf2, cexf]
  f_mono := fun x x' hx hxx' hne => by
    have hlt : x.1 + x.2 < x'.1 + x'.2 := by
      rcases hxx'.1.lt_or_eq with h1 | h1
      · linarith [hxx'.2]
      · rcases hxx'.2.lt_or_eq with h2 | h2
        · linarith
        · exact absurd (Prod.ext h1 h2) hne
    exact cex_hyp.f_mono (mem_Ici.2 (add_nonneg hx.1 hx.2))
      (mem_Ici.2 (by linarith [hx.1, hx.2])) hlt
  zbar_gt := by norm_num
  xbar_pos := by norm_num
  f_bound := fun x hx => by
    have := cex_hyp.f_mono.monotoneOn (mem_Ici.2 (add_nonneg hx.1 hx.2.1))
      (mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 3)) hx.2.2
    have h3 : (2 : ℝ) * cexf 3 ≤ 3 := by norm_num [cexf]
    change 2 * cexf (x.1 + x.2) ≤ 3
    linarith

theorem cexf2_concave : ConcaveOn ℝ quadrant cexf2 := by
  refine ⟨convex_quadrant, fun x hx y hy a b ha hb hab => ?_⟩
  have := cexf_concave.2 (mem_Ici.2 (add_nonneg hx.1 hx.2)) (mem_Ici.2 (add_nonneg hy.1 hy.2))
    ha hb hab
  simp only [smul_eq_mul] at this ⊢
  simp only [cexf2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  convert this using 2
  ring

/-- `e^{−3} − e^{−2.9} + (1 − e^{−2/11})/10 > 0`. -/
theorem cex2_numeric : 0 < Real.exp (-3) - Real.exp (-(29 / 10)) +
    1 / 10 * (1 - Real.exp (-(2 / 11))) := by
  have e1 : Real.exp (-(29 / 10)) = Real.exp (-3) * Real.exp (1 / 10) := by
    rw [← Real.exp_add]; norm_num
  have h1 : Real.exp (1 / 10) ≤ 10 / 9 := by
    have := Real.add_one_le_exp (-(1 / 10))
    have hp := Real.exp_pos (1 / 10)
    have : Real.exp (1 / 10) * Real.exp (-(1 / 10)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h3 : Real.exp (-3) ≤ 2 / 17 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
    have : Real.exp 3 * Real.exp (-3) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos (-3)
    nlinarith
  have h4 : Real.exp (-(2 / 11)) ≤ 11 / 13 := by
    have := Real.add_one_le_exp (2 / 11)
    have : Real.exp (2 / 11) * Real.exp (-(2 / 11)) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos (-(2 / 11))
    nlinarith
  rw [e1]
  have hp := Real.exp_pos (-3)
  nlinarith

/-- **Exercise 10.2b, corrected.** With `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)` (concave, as (T4)
allows), `U(c) = 1 − e^{−c}`, `β = 1/10`, `x̄ = 3`, `z̄ = 2` and any Feller `Q`:
`v(·, z)` is not strictly concave, and at `x = (3, 0)`, `z = 2` the policy correspondence
contains two distinct points. -/
theorem ex_10_2b_counterexample (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : twoX 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (twoModel Q cexU cexf2 (1 / 10) 3) (two_boundedDP cexf2_hyp Q hQ) v = v) :
    (∀ z, ¬ IsStrictConcaveS (convex_twoX 3) fun x => v (x, z)) ∧
      ∃ y y' : twoX 3, y ≠ y' ∧
        y ∈ policy (twoModel Q cexU cexf2 (1 / 10) 3) v (⟨(3, 0), by norm_num [twoX]⟩, ⟨2, by
          norm_num⟩) ∧
        y' ∈ policy (twoModel Q cexU cexf2 (1 / 10) 3) v (⟨(3, 0), by norm_num [twoX]⟩, ⟨2, by
          norm_num⟩) := by
  set M := twoModel Q cexU cexf2 (1 / 10) 3
  have hb := two_boundedDP cexf2_hyp Q hQ
  have hveq : ∀ (x x' : twoX 3) z, x.1.1 + x.1.2 = x'.1.1 + x'.1.2 → v (x, z) = v (x', z) :=
    fun x x' z hs => by
      rw [← hv]
      exact two_bellman_eq_of_f_eq cexf2_hyp Q hQ v (by simp only [cexf2, hs]) z
  refine ⟨fun z hsc => ?_, ?_⟩
  · -- `v` is constant along `x₁ + x₂ = 1`
    set a : twoX 3 := ⟨(1, 0), by norm_num [twoX]⟩
    set b : twoX 3 := ⟨(0, 1), by norm_num [twoX]⟩
    have hab : a ≠ b := fun he => by
      have := congrArg (fun p : twoX 3 => p.1.1) he
      norm_num [a, b] at this
    have h0 : (0 : ℝ) < 1 / 2 := by norm_num
    have h1 : (1 / 2 : ℝ) < 1 := by norm_num
    have := hsc a b hab (1 / 2) h0 h1
    have e1 := hveq a b z (by norm_num [a, b])
    have e2 := hveq (cmb (convex_twoX 3) h0.le h1.le a b) a z (by
      rw [(two_cmb_val h0.le h1.le).1, (two_cmb_val h0.le h1.le).2]; norm_num [a, b])
    dsimp only at this
    rw [e2, e1] at this
    linarith
  · set x₀ : twoX 3 := ⟨(3, 0), by norm_num [twoX]⟩
    set z₂ : Icc (1 : ℝ) 2 := ⟨2, by norm_num⟩
    set o : twoX 3 := ⟨(0, 0), by norm_num [twoX]⟩
    set y₁ : twoX 3 := ⟨(1 / 10, 0), by norm_num [twoX]⟩
    have hzf : z₂.1 * cexf2 x₀.1 = 3 := by norm_num [z₂, x₀, cexf2, cexf]
    -- `v(o, z′)` is the return to saving nothing from nothing
    have hvo : ∀ z', v (o, z') = 1 / 10 * ∫ z'', v (o, z'') ∂Q z' := fun z' => by
      obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb v (o, z')
      rw [hv] at hval
      have hy' : y.1.1 + y.1.2 ≤ z'.1 * cexf2 o.1 := hy
      have hyo : y = o := by
        have h0 : cexf2 o.1 = 0 := by norm_num [o, cexf2, cexf]
        rw [h0, mul_zero] at hy'
        ext <;> simp [o] <;> linarith [y.2.1, y.2.2.1]
      rw [hyo] at hy hval
      simp only [rhs, expV] at hval
      change v (o, z') = twoF cexU cexf2 3 2 (o, o, z') + 1 / 10 * ∫ z'', v (o, z'') ∂Q z'
        at hval
      rw [twoF_of_mem hy] at hval
      have h0 : cexU (z'.1 * cexf2 o.1 - (o.1.1 + o.1.2)) = 0 := by
        norm_num [o, cexf2, cexf, cexU]
      rw [h0, zero_add] at hval
      exact hval
    have hgain : ∀ z', cexU (2 / 11) ≤ v (y₁, z') - v (o, z') := fun z' => by
      obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb v (y₁, z')
      have ho : o ∈ M.Γ (y₁, z') := by
        change (0 : ℝ) + 0 ≤ z'.1 * cexf2 (1 / 10, 0)
        norm_num [cexf2, cexf]
        linarith [z'.2.1]
      have := hmax o ho
      rw [hv] at this
      simp only [rhs, expV] at this
      change twoF cexU cexf2 3 2 (y₁, o, z') + 1 / 10 * ∫ z'', v (o, z'') ∂Q z' ≤ _ at this
      rw [twoF_of_mem ho, ← hvo] at this
      have hf : cexf2 y₁.1 = 2 / 11 := by norm_num [y₁, cexf2, cexf]
      rw [hf] at this
      have hU : cexU (2 / 11) ≤ cexU (z'.1 * (2 / 11) - (o.1.1 + o.1.2)) := by
        have : (o.1.1 + o.1.2) = 0 := by norm_num [o]
        rw [this, sub_zero]
        exact cex_hyp.U_mono.monotoneOn (mem_Ici.2 (by norm_num))
          (mem_Ici.2 (by linarith [z'.2.1])) (by linarith [z'.2.1])
      linarith
    -- saving `1/10` beats saving nothing at `(x₀, 2)`
    obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M hb v (x₀, z₂)
    rw [hv] at hval hmax
    have hy₁ : y₁ ∈ M.Γ (x₀, z₂) := by
      change (1 / 10 : ℝ) + 0 ≤ _
      rw [hzf]; norm_num
    have ho : o ∈ M.Γ (x₀, z₂) := by
      change (0 : ℝ) + 0 ≤ _
      rw [hzf]; norm_num
    have hint := integrable_section_v (Q z₂) v
    have hcmp : rhs M v (x₀, z₂) o < rhs M v (x₀, z₂) y₁ := by
      simp only [rhs, expV]
      change twoF cexU cexf2 3 2 (x₀, o, z₂) + 1 / 10 * ∫ z', v (o, z') ∂Q z₂ <
        twoF cexU cexf2 3 2 (x₀, y₁, z₂) + 1 / 10 * ∫ z', v (y₁, z') ∂Q z₂
      rw [twoF_of_mem ho, twoF_of_mem hy₁, hzf]
      have hE : cexU (2 / 11) ≤ ∫ z', v (y₁, z') ∂Q z₂ - ∫ z', v (o, z') ∂Q z₂ := by
        rw [← integral_sub (hint y₁) (hint o)]
        have := integral_mono (μ := Q z₂) (integrable_const (cexU (2 / 11)))
          ((hint y₁).sub (hint o)) hgain
        simpa using this
      have := cex2_numeric
      simp only [cexU] at hE ⊢
      norm_num [o, y₁] at hE ⊢
      nlinarith
    -- an optimal `y` saves `k > 0`, which can be held as `(k, 0)` or `(0, k)`
    have hk : 0 < y.1.1 + y.1.2 := by
      rcases (add_nonneg y.2.1 y.2.2.1).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hyo : y = o := by
          ext <;> simp [o] <;> linarith [y.2.1, y.2.2.1]
        have := hmax y₁ hy₁
        rw [hval, hyo] at this
        linarith
    set k := y.1.1 + y.1.2
    have hk3 : k ≤ 3 := y.2.2.2
    set p : twoX 3 := ⟨(k, 0), ⟨hk.le, le_rfl, by simp only; linarith⟩⟩
    set q : twoX 3 := ⟨(0, k), ⟨le_rfl, hk.le, by simp only; linarith⟩⟩
    have hrhs : ∀ y' : twoX 3, y'.1.1 + y'.1.2 = k → rhs M v (x₀, z₂) y' = rhs M v (x₀, z₂) y :=
      fun y' hy' => by
        simp only [rhs, expV]
        change twoF cexU cexf2 3 2 (x₀, y', z₂) + 1 / 10 * ∫ z', v (y', z') ∂Q z₂ =
          twoF cexU cexf2 3 2 (x₀, y, z₂) + 1 / 10 * ∫ z', v (y, z') ∂Q z₂
        simp only [twoF, hy']
        congr 2
        exact integral_congr_ae (Eventually.of_forall fun z' => hveq y' y z' hy')
    have hyk : k ≤ z₂.1 * cexf2 x₀.1 := hy
    have hp : p ∈ policy M v (x₀, z₂) :=
      ⟨show k + 0 ≤ _ by linarith, by rw [hrhs p (by simp [p]), ← hval]⟩
    have hq : q ∈ policy M v (x₀, z₂) :=
      ⟨show 0 + k ≤ _ by linarith, by rw [hrhs q (by simp [q]), ← hval]⟩
    refine ⟨p, q, fun he => ?_, hp, hq⟩
    have := congrArg (fun r : twoX 3 => r.1.1) he
    simp only [p, q] at this
    linarith

end StokeyLucasPrescott.StochasticApplications
