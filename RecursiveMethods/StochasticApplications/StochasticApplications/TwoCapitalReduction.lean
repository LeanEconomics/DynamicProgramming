/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.TwoCapital

/-!
# Two capital goods: reduction to one endogenous state

SLP §10.2, Exercise 10.2d, p. 290. Output is `z f(x₁, x₂)` whatever the split, and next period's
output from total saving `k` is at most `z′ φ(k)`, `φ(k) = max_{y ≥ 0, y₁ + y₂ = k} f(y)`, with
equality at the best split (which does not depend on `z′`, since the shock is multiplicative).
So the model is the one-sector model of §10.1 with production function `φ`.

* `twoφ`, `continuous_twoφ`, `twoφ_attain`, `le_twoφ`: `φ`, computed over the shares
  `t ∈ [0, 1]`, is continuous and attained.
* `twoφ_hyp`, `twoφ_concave`: `φ` satisfies (T1)–(T3) and `z̄ φ(x̄) ≤ x̄`, and is concave if `f`
  is, so the analysis of Exercise 10.1 applies to it.
* **Exercise 10.2d** (`ex_10_2d`): if `v₂` solves the two-capital functional equation and `v₁`
  the one-sector equation with production `φ`, then `v₂(x, z) = v₁(k, z)` whenever
  `f(x) = φ(k)`, and every `x` has such a `k`. The proof shows that
  `w(x, z) = max_{0 ≤ k ≤ z f(x)} {U[z f(x) − k] + β ∫ v₁(k, z′) Q(z, dz′)}` is a fixed point of
  the two-capital operator.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {U : ℝ → ℝ} {f : ℝ × ℝ → ℝ} {β xbar zbar : ℝ}

/-- `φ(k) = max_{t ∈ [0, 1]} f(tk, (1 − t)k)` (the arguments clamped at `0`, so that `φ` is defined
and continuous on all of `ℝ`). -/
noncomputable def twoφ (f : ℝ × ℝ → ℝ) (k : ℝ) : ℝ :=
  sSup ((fun t : ℝ => f (max (t * k) 0, max ((1 - t) * k) 0)) '' Icc 0 1)

theorem continuous_twoφ_aux (h : TwoHyp U f β xbar zbar) :
    Continuous fun p : ℝ × ℝ => f (max (p.2 * p.1) 0, max ((1 - p.2) * p.1) 0) :=
  h.f_cont.comp_continuous (by fun_prop) fun _ => ⟨le_max_right _ _, le_max_right _ _⟩

theorem continuous_twoφ (h : TwoHyp U f β xbar zbar) : Continuous (twoφ f) :=
  isCompact_Icc.continuous_sSup (f := fun k t => f (max (t * k) 0, max ((1 - t) * k) 0))
    (continuous_twoφ_aux h)

theorem continuous_twoφ_section (h : TwoHyp U f β xbar zbar) (k : ℝ) :
    Continuous fun t : ℝ => f (max (t * k) 0, max ((1 - t) * k) 0) :=
  (continuous_twoφ_aux h).comp
    (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (k, t))

theorem twoφ_bdd (h : TwoHyp U f β xbar zbar) (k : ℝ) :
    BddAbove ((fun t : ℝ => f (max (t * k) 0, max ((1 - t) * k) 0)) '' Icc 0 1) :=
  (isCompact_Icc.image (continuous_twoφ_section h k)).bddAbove

/-- `φ(k)` is attained at some share `t ∈ [0, 1]`. -/
theorem twoφ_attain (h : TwoHyp U f β xbar zbar) {k : ℝ} (hk : 0 ≤ k) :
    ∃ t ∈ Icc (0 : ℝ) 1, twoφ f k = f (t * k, (1 - t) * k) := by
  obtain ⟨t, ht, he⟩ := (isCompact_Icc.image (continuous_twoφ_section h k)).sSup_mem
    ((nonempty_Icc.2 zero_le_one).image _)
  refine ⟨t, ht, ?_⟩
  rw [twoφ, ← he]
  simp only [max_eq_left (mul_nonneg ht.1 hk), max_eq_left (mul_nonneg (sub_nonneg.2 ht.2) hk)]

/-- `f(y) ≤ φ(y₁ + y₂)` on `ℝ²₊`. -/
theorem le_twoφ (h : TwoHyp U f β xbar zbar) {y : ℝ × ℝ} (hy : y ∈ quadrant) :
    f y ≤ twoφ f (y.1 + y.2) := by
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h1, h2⟩ := hy
  simp only at h1 h2 ⊢
  rcases (add_nonneg h1 h2).lt_or_eq with hk | hk
  · refine le_csSup (twoφ_bdd h _) ⟨y1 / (y1 + y2), ⟨div_nonneg h1 hk.le,
      (div_le_one hk).2 (by linarith)⟩, ?_⟩
    have e1 : y1 / (y1 + y2) * (y1 + y2) = y1 := div_mul_cancel₀ _ hk.ne'
    have e2 : (1 - y1 / (y1 + y2)) * (y1 + y2) = y2 := by
      rw [sub_mul, e1, one_mul]; ring
    simp only [e1, e2, max_eq_left h1, max_eq_left h2]
  · have hy1 : y1 = 0 := by linarith
    have hy2 : y2 = 0 := by linarith
    subst hy1 hy2
    refine le_csSup (twoφ_bdd h _) ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp

theorem twoφ_zero (h : TwoHyp U f β xbar zbar) : twoφ f 0 = 0 := by
  obtain ⟨t, -, ht⟩ := twoφ_attain h le_rfl
  rw [ht, mul_zero, mul_zero]
  exact h.f_zero

/-- `φ` satisfies (T1)–(T3) and `z̄ φ(x̄) ≤ x̄`: the hypotheses of §10.1. -/
theorem twoφ_hyp (h : TwoHyp U f β xbar zbar) : GrowthHyp U (twoφ f) β xbar zbar where
  β_pos := h.β_pos
  β_lt := h.β_lt
  U_cont := h.U_cont
  U_mono := h.U_mono
  f_cont := (continuous_twoφ h).continuousOn
  f_zero := twoφ_zero h
  f_mono := fun k hk k' hk' hkk' => by
    have hk0 : (0 : ℝ) ≤ k := hk
    obtain ⟨t, ht, he⟩ := twoφ_attain h hk0
    rw [he]
    have hq : (t * k, (1 - t) * k) ∈ quadrant :=
      ⟨mul_nonneg ht.1 hk0, mul_nonneg (sub_nonneg.2 ht.2) hk0⟩
    have hle : (t * k, (1 - t) * k) ≤ (t * k', (1 - t) * k') :=
      ⟨mul_le_mul_of_nonneg_left hkk'.le ht.1,
        mul_le_mul_of_nonneg_left hkk'.le (sub_nonneg.2 ht.2)⟩
    have hne : (t * k, (1 - t) * k) ≠ (t * k', (1 - t) * k') := fun he' => by
      have h1 := congrArg Prod.fst he'
      have h2 := congrArg Prod.snd he'
      simp only at h1 h2
      linarith
    refine (h.f_mono _ _ hq hle hne).trans_le ?_
    have := le_twoφ h (y := (t * k', (1 - t) * k')) ⟨mul_nonneg ht.1 (by linarith),
      mul_nonneg (sub_nonneg.2 ht.2) (by linarith)⟩
    simpa [← add_mul] using this
  zbar_gt := h.zbar_gt
  xbar_pos := h.xbar_pos
  xbar_maintain := by
    obtain ⟨t, ht, he⟩ := twoφ_attain h h.xbar_pos.le
    rw [he]
    refine h.f_bound _ ⟨mul_nonneg ht.1 h.xbar_pos.le,
      mul_nonneg (sub_nonneg.2 ht.2) h.xbar_pos.le, ?_⟩
    simp only
    linarith

/-- (T4) passes to `φ`: if `f` is concave on `ℝ²₊`, `φ` is concave on `[0, ∞)`. -/
theorem twoφ_concave (h : TwoHyp U f β xbar zbar) (hf : ConcaveOn ℝ quadrant f) :
    ConcaveOn ℝ (Ici 0) (twoφ f) := by
  refine ⟨convex_Ici 0, fun k hk k' hk' a b ha hb hab => ?_⟩
  have hk0 : (0 : ℝ) ≤ k := hk
  have hk0' : (0 : ℝ) ≤ k' := hk'
  obtain ⟨t, ht, he⟩ := twoφ_attain h hk0
  obtain ⟨t', ht', he'⟩ := twoφ_attain h hk0'
  have hq : (t * k, (1 - t) * k) ∈ quadrant :=
    ⟨mul_nonneg ht.1 hk0, mul_nonneg (sub_nonneg.2 ht.2) hk0⟩
  have hq' : (t' * k', (1 - t') * k') ∈ quadrant :=
    ⟨mul_nonneg ht'.1 hk0', mul_nonneg (sub_nonneg.2 ht'.2) hk0'⟩
  have hc := hf.2 hq hq' ha hb hab
  have hmix := convex_quadrant hq hq' ha hb hab
  have hle := le_twoφ h hmix
  rw [he, he', smul_eq_mul, smul_eq_mul]
  refine hc.trans (hle.trans_eq ?_)
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Total capital `y₁ + y₂` as a point of `[0, x̄]`. -/
def twoσ (y : twoX xbar) : Icc (0 : ℝ) xbar := ⟨y.1.1 + y.1.2, add_nonneg y.2.1 y.2.2.1, y.2.2.2⟩

/-- **Exercise 10.2d.** The two-capital model is the one-sector model with production
`φ(k) = max_{y₁ + y₂ = k} f(y)`: `φ` satisfies the hypotheses of §10.1 (and (T4) if `f` does),
and if `v₂` and `v₁` are the fixed points of the two operators, `v₂(x, z) = v₁(k, z)` whenever
`f(x) = φ(k)`; every `x` has such a `k ≤ x₁ + x₂`. -/
theorem ex_10_2d (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v₂ : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv₂ : bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v₂ = v₂)
    {v₁ : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv₁ : bellman (growthModel Q U (twoφ f) β xbar) (growth_boundedDP (twoφ_hyp h) Q hQ) v₁ =
      v₁) :
    (∀ x : twoX xbar, ∃ k : Icc (0 : ℝ) xbar, k.1 ≤ x.1.1 + x.1.2 ∧ twoφ f k.1 = f x.1) ∧
      ∀ (x : twoX xbar) (k : Icc (0 : ℝ) xbar) (z : Icc (1 : ℝ) zbar),
        f x.1 = twoφ f k.1 → v₂ (x, z) = v₁ (k, z) := by
  set M₂ := twoModel Q U f β xbar
  have hb₂ := two_boundedDP h Q hQ
  set M₁ := growthModel Q U (twoφ f) β xbar
  have hb₁ := growth_boundedDP (twoφ_hyp h) Q hQ
  have : CompactSpace (twoX xbar) := isCompact_iff_compactSpace.1 (isCompact_twoX xbar)
  -- the auxiliary problem: choose total saving `k ≤ z f(x)`
  set Γw : twoX xbar × Icc (1 : ℝ) zbar → Set (Icc (0 : ℝ) xbar) :=
    fun s => {k | k.1 ≤ s.2.1 * f s.1.1}
  set Hw : (twoX xbar × Icc (1 : ℝ) zbar) × Icc (0 : ℝ) xbar → ℝ :=
    fun p => U (max (p.1.2.1 * f p.1.1.1 - p.2.1) 0) + β * ∫ z', v₁ (p.2, z') ∂Q p.1.2
  have hzf : Continuous fun s : twoX xbar × Icc (1 : ℝ) zbar => s.2.1 * f s.1.1 :=
    (continuous_subtype_val.comp continuous_snd).mul (h.continuous_f.comp continuous_fst)
  have hΓl := isLHC_Icc_le hzf h.zf_nonneg h.xbar_pos.le
  have hΓu := isUHC_Icc_le hzf h.zf_nonneg h.xbar_pos.le
  have hΓc : ∀ s, IsCompact (Γw s) := fun _ =>
    IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const)
  have hmop := lemma_9_5_compact (W := Icc (0 : ℝ) xbar) Q hQ v₁ v₁.continuous
    ⟨‖v₁‖, fun p => by rw [← Real.norm_eq_abs]; exact v₁.norm_coe_le_norm p⟩
  have hHc : Continuous Hw :=
    (h.U_cont.comp_continuous ((((continuous_subtype_val.comp continuous_fst.snd).mul
      (h.continuous_f.comp continuous_fst.fst)).sub
      (continuous_subtype_val.comp continuous_snd)).max continuous_const)
      fun _ => mem_Ici.2 (le_max_right _ _)).add
      (continuous_const.mul (hmop.comp (continuous_snd.prodMk continuous_fst.snd)))
  have h36 := theorem_3_6 hHc.continuousOn hΓc hΓl hΓu
  set w : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ :=
    mkOfCompact ⟨fun s => maxValue Hw Γw s, h36.1⟩
  have hwv : ∀ s, w s = maxValue Hw Γw s := fun _ => rfl
  have hΓne : ∀ s, (Γw s).Nonempty := fun s => (hΓl s).1
  -- `w(y, z′) ≤ v₁(y₁ + y₂, z′)`
  have hw_le : ∀ (y : twoX xbar) (z' : Icc (1 : ℝ) zbar), w (y, z') ≤ v₁ (twoσ y, z') := by
    intro y z'
    obtain ⟨k, hk, hval, -⟩ := exists_argmax hHc.continuousOn (hΓc (y, z')) (hΓne (y, z'))
    rw [hwv, ← hval]
    have hk' : k.1 ≤ z'.1 * f y.1 := hk
    have hfφ : f y.1 ≤ twoφ f (twoσ y).1 := le_twoφ h (twoX_subset_quadrant y.2)
    have hz : 0 ≤ z'.1 := by linarith [z'.2.1]
    have hkφ : k ∈ growthΓ (twoφ f) xbar zbar (twoσ y, z') :=
      show k.1 ≤ z'.1 * twoφ f (twoσ y).1 from hk'.trans (mul_le_mul_of_nonneg_left hfφ hz)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M₁ hb₁ v₁ (twoσ y, z')
    have := hmax k hkφ
    rw [hv₁] at this
    refine le_trans ?_ this
    change U (max (z'.1 * f y.1 - k.1) 0) + β * _ ≤
      U (max (z'.1 * twoφ f (twoσ y).1 - k.1) 0) + β * _
    gcongr ?_ + _
    refine h.U_mono.monotoneOn (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 (le_max_right _ _)) ?_
    exact max_le_max (by nlinarith) le_rfl
  -- `w(x, z) = v₁(k, z)` when `f(x) = φ(k)`
  have hw_eq : ∀ (x : twoX xbar) (k : Icc (0 : ℝ) xbar) (z : Icc (1 : ℝ) zbar),
      f x.1 = twoφ f k.1 → w (x, z) = v₁ (k, z) := by
    intro x k z hfk
    rw [hwv, ← hv₁, bellman_apply]
    simp only [maxValue, Hw, Γw, objG, rhs, expV, growthΓ, growthF, hfk]
  -- `w` is a fixed point of the two-capital operator
  have hfix : bellman M₂ hb₂ w = w := by
    ext ⟨x, z⟩
    obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M₂ hb₂ w (x, z)
    have hint := integrable_section_v (Q z) w
    have hint₁ := integrable_section_v (Q z) v₁
    apply le_antisymm
    · rw [hval]
      have hyσ : twoσ y ∈ Γw (x, z) := hy
      have hle := le_maxValue hHc.continuousOn (hΓc (x, z)) hyσ
      rw [← hwv] at hle
      refine le_trans ?_ hle
      simp only [rhs, expV]
      change twoF U f xbar zbar (x, y, z) + β * ∫ z', w (y, z') ∂Q z ≤
        U (max (z.1 * f x.1 - (twoσ y).1) 0) + β * ∫ z', v₁ (twoσ y, z') ∂Q z
      have e : ((twoσ y : Icc (0 : ℝ) xbar) : ℝ) = y.1.1 + y.1.2 := rfl
      rw [twoF_of_mem hy, e, max_eq_left (sub_nonneg.2 hy)]
      have hI := integral_mono (hint y) (hint₁ _) fun z' => hw_le y z'
      have := mul_le_mul_of_nonneg_left hI h.β_pos.le
      linarith
    · obtain ⟨k, hk, hkval, -⟩ := exists_argmax hHc.continuousOn (hΓc (x, z)) (hΓne (x, z))
      obtain ⟨t, ht, he⟩ := twoφ_attain h k.2.1
      set a : twoX xbar := ⟨(t * k.1, (1 - t) * k.1), mul_nonneg ht.1 k.2.1,
        mul_nonneg (sub_nonneg.2 ht.2) k.2.1, by simp only; linarith [k.2.2]⟩
      have hsum : a.1.1 + a.1.2 = k.1 := by simp only [a]; ring
      have ha : a ∈ M₂.Γ (x, z) := show a.1.1 + a.1.2 ≤ z.1 * f x.1 by rw [hsum]; exact hk
      have := hmax a ha
      rw [hwv, ← hkval]
      refine le_trans (le_of_eq ?_) this
      simp only [rhs, expV]
      change U (max (z.1 * f x.1 - k.1) 0) + β * ∫ z', v₁ (k, z') ∂Q z =
        twoF U f xbar zbar (x, a, z) + β * ∫ z', w (a, z') ∂Q z
      rw [twoF_of_mem ha, hsum, max_eq_left (sub_nonneg.2 hk)]
      congr 2
      exact integral_congr_ae (Eventually.of_forall fun z' => (hw_eq a k z' he.symm).symm)
  obtain ⟨v, -, huniq, -, -⟩ := ex_9_7b M₂ hb₂
  have hwv₂ : w = v₂ := (huniq w hfix).trans (huniq v₂ hv₂).symm
  refine ⟨fun x => ?_, fun x k z hfk => by rw [← hwv₂]; exact hw_eq x k z hfk⟩
  -- the intermediate value theorem
  have hs := add_nonneg x.2.1 x.2.2.1
  have hivt := intermediate_value_Icc hs (continuous_twoφ h).continuousOn
  rw [twoφ_zero h] at hivt
  obtain ⟨k, hk, hke⟩ := hivt ⟨h.f_nonneg (twoX_subset_quadrant x.2),
    le_twoφ h (twoX_subset_quadrant x.2)⟩
  exact ⟨⟨k, hk.1, hk.2.trans x.2.2.2⟩, hk.2, hke⟩

end StokeyLucasPrescott.StochasticApplications
