/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.UpperBounded

/-!
# Industry investment under uncertainty: the model

SLP §10.4, pp. 292–296. Industry capital `x ∈ X = (0, ∞)`, demand shocks `z ∈ Z = [z₁, z₂]` with a
Feller transition `Q`, consumers' surplus `U(x, z)`, and adjustment cost `x c(y/x)` for next
period's capital `y`, where `c = 0` on `[0, 1 − δ]` and `c` is strictly increasing and strictly
convex beyond. The modified problem (2′) restricts `y` to
`Γ(x) = [(1 − δ′)x, max{M, x}]` (`indΓ`), with `δ < δ′ < 1`.

* `ind_upperDP`: returns are bounded above by `A` and `y = (1 − δ)x` costs nothing, so the
  results of `UpperBounded` apply.
* **Corrections.** The manual verifies Assumptions 9.6–9.11 for (2′). Three of them fail:
  `F` is unbounded below on the graph of `Γ` (`ind_F_unbounded`, with `c(a) = (a − ½)²` beyond
  `½`), so Assumption 9.7 fails; `Γ(x) ⊄ Γ(x′)` for `x < x′` (`ind_Γ_not_mono`), so
  Assumption 9.9 fails; and the graph of `Γ` is not convex (`ind_Γ_not_convex`), so
  Assumption 9.11 fails. The conclusions are recovered in `IndustryInvestmentResults`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-- The hypotheses of SLP §10.4 on surplus `U` (from the demand curve), costs `c`, and the
constants (`r > 0`, `0 < δ < δ′ < 1`, `M > 0`, `U ≤ A`, `Z = [z₁, z₂]`). `M` is chosen large:
`M c(1) > A/(1 − β)` with `β = 1/(1 + r)`. -/
structure IndHyp (U : ℝ → ℝ → ℝ) (c : ℝ → ℝ) (δ δ' M r A z₁ z₂ : ℝ) : Prop where
  r_pos : 0 < r
  δ_pos : 0 < δ
  δ_lt : δ < δ'
  δ'_lt : δ' < 1
  M_pos : 0 < M
  z_le : z₁ ≤ z₂
  U_cont : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Ici 0 ×ˢ Icc z₁ z₂)
  U_nonneg : ∀ q z, 0 ≤ q → z ∈ Icc z₁ z₂ → 0 ≤ U q z
  U_le : ∀ q z, 0 ≤ q → z ∈ Icc z₁ z₂ → U q z ≤ A
  U_mono : ∀ z ∈ Icc z₁ z₂, StrictMonoOn (fun q => U q z) (Ici 0)
  U_conc : ∀ z ∈ Icc z₁ z₂, StrictConcaveOn ℝ (Ici 0) fun q => U q z
  U_mono_z : ∀ q, 0 < q → StrictMonoOn (U q) (Icc z₁ z₂)
  c_cont : ContinuousOn c (Ici 0)
  c_zero : ∀ a, 0 ≤ a → a ≤ 1 - δ → c a = 0
  c_conv : ConvexOn ℝ (Ici 0) c
  c_mono : StrictMonoOn c (Ici (1 - δ))
  c_sconv : StrictConvexOn ℝ (Ici (1 - δ)) c
  M_big : A / (1 - 1 / (1 + r)) < M * c 1

variable {U : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {δ δ' M r A z₁ z₂ : ℝ}

/-- `Γ(x) = [(1 − δ′)x, max{M, x}]`. -/
def indΓ (δ' M : ℝ) (s : Ioi (0 : ℝ) × Icc z₁ z₂) : Set (Ioi (0 : ℝ)) :=
  {y | (1 - δ') * s.1.1 ≤ y.1 ∧ y.1 ≤ max M s.1.1}

/-- `F(x, y, z) = U(x, z) − x c(y/x)`. -/
noncomputable def indF (U : ℝ → ℝ → ℝ) (c : ℝ → ℝ) (p : Ioi (0 : ℝ) × Ioi (0 : ℝ) × Icc z₁ z₂) :
    ℝ :=
  U p.1.1 p.2.2.1 - p.1.1 * c (p.2.1.1 / p.1.1)

/-- The problem (2′) in the first formulation of Chapter 9, with `β = 1/(1 + r)`. -/
noncomputable abbrev indModel (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (U : ℝ → ℝ → ℝ) (c : ℝ → ℝ)
    (δ' M r : ℝ) :
    Model (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) (Icc z₁ z₂) :=
  Model.first Q (indΓ δ' M) (indF U c) (1 / (1 + r))

namespace IndHyp

variable (h : IndHyp U c δ δ' M r A z₁ z₂)
include h

theorem one_sub_δ_nonneg : 0 ≤ 1 - δ := by linarith [h.δ_lt, h.δ'_lt]

theorem c_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ c a := by
  rcases le_or_gt a (1 - δ) with h1 | h1
  · exact (h.c_zero a ha h1).symm.le
  · have h2 : c (1 - δ) < c a := h.c_mono (mem_Ici.2 le_rfl) (mem_Ici.2 h1.le) h1
    rw [h.c_zero _ h.one_sub_δ_nonneg le_rfl] at h2
    exact h2.le

theorem c_one_pos : 0 < c 1 := by
  have h1 : 1 - δ < 1 := by linarith [h.δ_pos]
  have h2 : c (1 - δ) < c 1 := h.c_mono (mem_Ici.2 le_rfl) (mem_Ici.2 h1.le) h1
  rwa [h.c_zero _ h.one_sub_δ_nonneg le_rfl] at h2

/-- `c(ta) ≤ t c(a)` for `t ∈ [0, 1]` (convexity and `c(0) = 0`). -/
theorem c_mul_le {a t : ℝ} (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : c (t * a) ≤ t * c a := by
  have hz : c 0 = 0 := h.c_zero 0 le_rfl (by linarith [h.δ_lt, h.δ'_lt])
  have := h.c_conv.2 (mem_Ici.2 ha) (mem_Ici.2 (le_refl (0 : ℝ))) ht0 (by linarith : 0 ≤ 1 - t)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hz] at this
  exact this

/-- `a c(1) ≤ c(a)` for `a ≥ 1`. -/
theorem c_ge_mul {a : ℝ} (ha : 1 ≤ a) : a * c 1 ≤ c a := by
  have hpos : 0 < a := by linarith
  have := h.c_mul_le (a := a) (t := 1 / a) hpos.le (by positivity) ((div_le_one hpos).2 ha)
  rw [one_div, inv_mul_cancel₀ hpos.ne'] at this
  have h2 := mul_le_mul_of_nonneg_left this hpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2

/-- The adjustment cost `x c(y/x)` is nonincreasing in `x`. -/
theorem persp_anti {x x' y : ℝ} (hx : 0 < x) (hxx' : x ≤ x') (hy : 0 ≤ y) :
    x' * c (y / x') ≤ x * c (y / x) := by
  have hx' : 0 < x' := hx.trans_le hxx'
  have e : y / x' = x / x' * (y / x) := by field_simp
  have := h.c_mul_le (a := y / x) (t := x / x') (by positivity) (by positivity)
    ((div_le_one hx').2 hxx')
  rw [e]
  calc x' * c (x / x' * (y / x)) ≤ x' * (x / x' * c (y / x)) :=
        mul_le_mul_of_nonneg_left this hx'.le
    _ = x * c (y / x) := by field_simp

/-- The adjustment cost `x c(y/x)` is jointly convex (the perspective of a convex function). -/
theorem persp_convex {x x' y y' θ : ℝ} (hx : 0 < x) (hx' : 0 < x') (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (θ * x + (1 - θ) * x') * c ((θ * y + (1 - θ) * y') / (θ * x + (1 - θ) * x')) ≤
      θ * (x * c (y / x)) + (1 - θ) * (x' * c (y' / x')) := by
  have h1' : 0 ≤ 1 - θ := by linarith
  have hxθ : 0 < θ * x + (1 - θ) * x' := by
    rcases h0.lt_or_eq with h0' | h0'
    · have : 0 ≤ (1 - θ) * x' := mul_nonneg h1' hx'.le
      nlinarith
    · subst h0'; linarith
  obtain ⟨xθ, hxθe⟩ : ∃ xθ, xθ = θ * x + (1 - θ) * x' := ⟨_, rfl⟩
  rw [← hxθe] at hxθ ⊢
  obtain ⟨w, hw⟩ : ∃ w, w = θ * x / xθ := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw1 : 1 - w = (1 - θ) * x' / xθ := by
    rw [hw, eq_div_iff hxθ.ne', sub_mul, div_mul_cancel₀ _ hxθ.ne', hxθe]; ring
  have hw1' : 0 ≤ 1 - w := by rw [hw1]; positivity
  have e : (θ * y + (1 - θ) * y') / xθ = w * (y / x) + (1 - w) * (y' / x') := by
    rw [hw1, hw]; field_simp
  have hc := h.c_conv.2 (mem_Ici.2 (div_nonneg hy hx.le)) (mem_Ici.2 (div_nonneg hy' hx'.le))
    hw0 hw1' (by ring)
  simp only [smul_eq_mul] at hc
  rw [e]
  calc xθ * c (w * (y / x) + (1 - w) * (y' / x')) ≤
        xθ * (w * c (y / x) + (1 - w) * c (y' / x')) := mul_le_mul_of_nonneg_left hc hxθ.le
    _ = θ * (x * c (y / x)) + (1 - θ) * (x' * c (y' / x')) := by
        rw [hw1, hw]; field_simp

end IndHyp

/-! ### The corrections -/

/-- The quadratic adjustment cost `c(a) = max{a − ½, 0}²` (`δ = ½`). -/
noncomputable def cq (a : ℝ) : ℝ := max (a - 1 / 2) 0 ^ 2

/-- `cq` satisfies the hypotheses on `c` with `δ = ½`. -/
theorem cq_props : ContinuousOn cq (Ici 0) ∧ (∀ a, 0 ≤ a → a ≤ 1 - 1 / 2 → cq a = 0) ∧
    ConvexOn ℝ (Ici 0) cq ∧ StrictMonoOn cq (Ici (1 - 1 / 2)) ∧
    StrictConvexOn ℝ (Ici (1 - 1 / 2)) cq := by
  have hge : ∀ a, 1 - 1 / 2 ≤ a → cq a = (a - 1 / 2) ^ 2 := fun a ha => by
    simp only [cq, max_eq_left (by linarith : (0 : ℝ) ≤ a - 1 / 2)]
  refine ⟨(((continuous_id.sub continuous_const).max continuous_const).pow 2).continuousOn,
    fun a _ ha => ?_,
    ⟨convex_Ici 0, fun a _ b _ θ η hθ hη hθη => ?_⟩, fun a ha b hb hab => ?_,
    ⟨convex_Ici _, fun a ha b hb hne θ η hθ hη hθη => ?_⟩⟩
  · simp only [cq, max_eq_right (by linarith : a - 1 / 2 ≤ 0)]; norm_num
  · simp only [cq, smul_eq_mul]
    set p := max (a - 1 / 2) 0
    set q := max (b - 1 / 2) 0
    have hp : 0 ≤ p := le_max_right _ _
    have hq : 0 ≤ q := le_max_right _ _
    have hm : max (θ * a + η * b - 1 / 2) 0 ≤ θ * p + η * q := by
      refine max_le ?_ (by positivity)
      have : θ * a + η * b - 1 / 2 = θ * (a - 1 / 2) + η * (b - 1 / 2) := by
        linear_combination (1 / 2 : ℝ) * hθη
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hη)
    have h0 : 0 ≤ max (θ * a + η * b - 1 / 2) 0 := le_max_right _ _
    calc max (θ * a + η * b - 1 / 2) 0 ^ 2 ≤ (θ * p + η * q) ^ 2 := pow_le_pow_left₀ h0 hm 2
      _ ≤ θ * p ^ 2 + η * q ^ 2 := by
        have : η = 1 - θ := by linarith
        subst this
        nlinarith [sq_nonneg (p - q), mul_nonneg hθ hη]
  · rw [hge a ha, hge b hb]
    have : (1 : ℝ) - 1 / 2 ≤ a := ha
    nlinarith
  · simp only [smul_eq_mul]
    rw [hge a ha, hge b hb, hge _ (by
      have : (1 : ℝ) - 1 / 2 ≤ a := ha
      have : (1 : ℝ) - 1 / 2 ≤ b := hb
      nlinarith)]
    have : η = 1 - θ := by linarith
    subst this
    have hab : 0 < (a - b) ^ 2 := by positivity
    nlinarith [mul_pos hθ hη]

/-- **Assumption 9.7 fails** for (2′): with `c = cq`, `x c(M/x) ≥ M²/(4x)` for small `x`, so `F`
is unbounded below on the graph of `Γ`. -/
theorem ind_F_unbounded (hM : 0 < M) (hU : ∀ q z, U q z ≤ A) (B : ℝ) :
    ∃ x y : Ioi (0 : ℝ), (∀ z, y ∈ indΓ (z₁ := z₁) (z₂ := z₂) (3 / 4) M (x, z)) ∧
      ∀ z : Icc z₁ z₂, indF U cq (x, y, z) < -B := by
  set K := |A| + |B| + 1
  set t : ℝ := min (M / 2) (M ^ 2 / (8 * K))
  have hK : 0 < K := by positivity
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ M / 2 := min_le_left _ _
  have ht2 : t ≤ M ^ 2 / (8 * K) := min_le_right _ _
  refine ⟨⟨t, ht⟩, ⟨M, hM⟩, fun z => ⟨by simp only; linarith, le_max_left _ _⟩, fun z => ?_⟩
  change U t z.1 - t * max (M / t - 1 / 2) 0 ^ 2 < -B
  have hMt : 2 ≤ M / t := by rw [le_div_iff₀ ht]; linarith
  have hpos : M / (2 * t) ≤ M / t - 1 / 2 := by
    have : M / t = 2 * (M / (2 * t)) := by field_simp
    have h2 : 1 ≤ M / (2 * t) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  rw [max_eq_left (by linarith)]
  have hsq : (M / (2 * t)) ^ 2 ≤ (M / t - 1 / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hpos 2
  have hbig : 2 * K ≤ t * (M / (2 * t)) ^ 2 := by
    have e : t * (M / (2 * t)) ^ 2 = M ^ 2 / (4 * t) := by field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at ht2
    nlinarith
  have := mul_le_mul_of_nonneg_left hsq ht.le
  have hA := hU t z.1
  have : A ≤ |A| := le_abs_self A
  have : B ≤ |B| := le_abs_self B
  simp only [K] at hbig
  linarith

/-- **Assumption 9.9 fails** for (2′): `Γ(x) ⊄ Γ(x′)` whenever `x < x′`, because the lower bound
`(1 − δ′)x` rises with `x`. -/
theorem ind_Γ_not_mono (hδ0 : 0 ≤ δ') (hδ' : δ' < 1) {x x' : Ioi (0 : ℝ)} (hxx' : x.1 < x'.1)
    (z : Icc z₁ z₂) :
    ¬ indΓ δ' M (x, z) ⊆ indΓ δ' M (x', z) := by
  intro hsub
  have hpos : 0 < (1 - δ') * x.1 := mul_pos (by linarith) x.2
  have hmem : (⟨(1 - δ') * x.1, hpos⟩ : Ioi (0 : ℝ)) ∈ indΓ δ' M (x, z) :=
    ⟨le_rfl, le_trans (by nlinarith [show 0 < x.1 from x.2]) (le_max_right M x.1)⟩
  have h2 : (1 - δ') * x'.1 ≤ (1 - δ') * x.1 := (hsub hmem).1
  nlinarith [mul_lt_mul_of_pos_left hxx' (by linarith : (0 : ℝ) < 1 - δ')]

/-- **Assumption 9.11 fails** for (2′): the graph of `Γ` is not convex. `(M/2, M)` and `(2M, 2M)`
lie in it, but their midpoint `(5M/4, 3M/2)` does not, since `3M/2 > max{M, 5M/4}`. -/
theorem ind_Γ_not_convex (hM : 0 < M) (hδ' : 0 ≤ δ') (z : Icc z₁ z₂) :
    ∃ x x' y y' : Ioi (0 : ℝ), y ∈ indΓ δ' M (x, z) ∧ y' ∈ indΓ δ' M (x', z) ∧
      max M (1 / 2 * x.1 + 1 / 2 * x'.1) < 1 / 2 * y.1 + 1 / 2 * y'.1 := by
  refine ⟨⟨M / 2, mem_Ioi.2 (by positivity)⟩, ⟨2 * M, mem_Ioi.2 (by positivity)⟩, ⟨M, hM⟩,
    ⟨2 * M, mem_Ioi.2 (by positivity)⟩,
    ⟨?_, le_max_left _ _⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only; nlinarith
  · simp only; nlinarith
  · simp only; exact le_max_right _ _
  · simp only
    rw [max_lt_iff]
    constructor <;> linarith

/-! ### The hypotheses of `UpperBounded` -/

/-- An interval correspondence `s ↦ [l(s), u(s)] ⊆ (0, ∞)` with continuous `0 < l ≤ u` is
l.h.c. -/
theorem isLHC_Ioi_interval {S : Type*} [MetricSpace S] {l u : S → ℝ} (hl : Continuous l)
    (hu : Continuous u) (hl0 : ∀ s, 0 < l s) (hlu : ∀ s, l s ≤ u s) (s : S) :
    IsLHC (fun s => {y : Ioi (0 : ℝ) | l s ≤ y.1 ∧ y.1 ≤ u s}) s := by
  refine ⟨⟨⟨l s, hl0 s⟩, le_rfl, hlu s⟩, fun y hy xs hxs => ?_⟩
  refine ⟨0, fun n => ⟨max (l (xs n)) (min y.1 (u (xs n))),
    lt_of_lt_of_le (hl0 _) (le_max_left _ _)⟩, fun n _ => ⟨le_max_left _ _,
      max_le (hlu _) (min_le_right _ _)⟩, ?_⟩
  have := ((hl.tendsto s).comp hxs).max ((tendsto_const_nhds (x := y.1)).min
    ((hu.tendsto s).comp hxs))
  rw [min_eq_left hy.2, max_eq_right hy.1] at this
  exact tendsto_subtype_rng.2 this

/-- An interval correspondence `s ↦ [l(s), u(s)] ⊆ (0, ∞)` with continuous `0 < l ≤ u` is
u.h.c. -/
theorem isUHC_Ioi_interval {S : Type*} [MetricSpace S] {l u : S → ℝ} (hl : Continuous l)
    (hu : Continuous u) (hl0 : ∀ s, 0 < l s) (hlu : ∀ s, l s ≤ u s) (s : S) :
    IsUHC (fun s => {y : Ioi (0 : ℝ) | l s ≤ y.1 ∧ y.1 ≤ u s}) s := by
  refine ⟨⟨⟨l s, hl0 s⟩, le_rfl, hlu s⟩, fun xs hxs ys hys => ?_⟩
  have hut := (hu.tendsto s).comp hxs
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hut).bddAbove
  have hmem : ∀ n, (ys n).1 ∈ Icc 0 B := fun n =>
    ⟨(ys n).2.le, (hys n).2.trans (hB ⟨n, rfl⟩)⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hla : l s ≤ a := le_of_tendsto_of_tendsto ((hl.tendsto s).comp (hxs.comp hφ.tendsto_atTop))
    hlim (Eventually.of_forall fun n => (hys (φ n)).1)
  have hau : a ≤ u s := le_of_tendsto_of_tendsto hlim (hut.comp hφ.tendsto_atTop)
    (Eventually.of_forall fun n => (hys (φ n)).2)
  exact ⟨⟨a, lt_of_lt_of_le (hl0 s) hla⟩, ⟨hla, hau⟩, φ, hφ, tendsto_subtype_rng.2 hlim⟩

namespace IndHyp

variable (h : IndHyp U c δ δ' M r A z₁ z₂)
include h

theorem A_nonneg : 0 ≤ A :=
  (h.U_nonneg 0 z₁ le_rfl ⟨le_rfl, h.z_le⟩).trans (h.U_le 0 z₁ le_rfl ⟨le_rfl, h.z_le⟩)

theorem continuous_F : Continuous (indF (z₁ := z₁) (z₂ := z₂) U c) := by
  have hU : Continuous fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) × Icc z₁ z₂ => U p.1.1 p.2.2.1 :=
    h.U_cont.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd.snd)) fun p =>
      ⟨mem_Ici.2 (le_of_lt p.1.2), p.2.2.2⟩
  have hq : Continuous fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) × Icc z₁ z₂ => p.2.1.1 / p.1.1 :=
    (continuous_subtype_val.comp continuous_snd.fst).div
      (continuous_subtype_val.comp continuous_fst) fun p => ne_of_gt p.1.2
  exact hU.sub ((continuous_subtype_val.comp continuous_fst).mul
    (h.c_cont.comp_continuous hq fun p => mem_Ici.2 (div_nonneg (le_of_lt p.2.1.2)
      (le_of_lt p.1.2))))

theorem F_le (p : Ioi (0 : ℝ) × Ioi (0 : ℝ) × Icc z₁ z₂) : indF U c p ≤ A := by
  have h1 := h.U_le p.1.1 p.2.2.1 (le_of_lt p.1.2) p.2.2.2
  have h2 := mul_nonneg (le_of_lt p.1.2) (h.c_nonneg (div_nonneg (le_of_lt p.2.1.2)
    (le_of_lt p.1.2)))
  unfold indF; linarith

theorem one_sub_δ_pos : 0 < 1 - δ := by linarith [h.δ_lt, h.δ'_lt]

/-- The zero-cost choice `y = (1 − δ)x`. -/
def safeY (x : Ioi (0 : ℝ)) : Ioi (0 : ℝ) :=
  ⟨(1 - δ) * x.1, mem_Ioi.2 (mul_pos h.one_sub_δ_pos x.2)⟩

/-- `y = (1 − δ)x` is feasible and costs nothing. -/
theorem safe_mem (x : Ioi (0 : ℝ)) (z : Icc z₁ z₂) :
    h.safeY x ∈ indΓ δ' M (x, z) ∧ indF U c (x, h.safeY x, z) = U x.1 z.1 := by
  have hx : 0 < x.1 := x.2
  refine ⟨⟨mul_le_mul_of_nonneg_right (by linarith [h.δ_lt]) hx.le,
    le_trans (mul_le_of_le_one_left hx.le (by linarith [h.δ_pos])) (le_max_right _ _)⟩, ?_⟩
  simp only [indF, safeY]
  rw [mul_div_cancel_right₀ _ hx.ne', h.c_zero _ h.one_sub_δ_nonneg le_rfl, mul_zero, sub_zero]

/-- The industry problem (2′) satisfies `UpperDP` with bound `A`. -/
theorem upperDP (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    UpperDP (indModel Q U c δ' M r) A := by
  have hl : Continuous fun s : Ioi (0 : ℝ) × Icc z₁ z₂ => (1 - δ') * s.1.1 :=
    continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  have hu : Continuous fun s : Ioi (0 : ℝ) × Icc z₁ z₂ => max M s.1.1 :=
    continuous_const.max (continuous_subtype_val.comp continuous_fst)
  have hl0 : ∀ s : Ioi (0 : ℝ) × Icc z₁ z₂, 0 < (1 - δ') * s.1.1 := fun s =>
    mul_pos (by linarith [h.δ'_lt]) s.1.2
  have hlu : ∀ s : Ioi (0 : ℝ) × Icc z₁ z₂, (1 - δ') * s.1.1 ≤ max M s.1.1 := fun s =>
    le_trans (by nlinarith [h.δ_pos, h.δ_lt, show 0 < s.1.1 from s.1.2]) (le_max_right _ _)
  have hlhc := isLHC_Ioi_interval hl hu hl0 hlu
  refine ⟨fun s => (hlhc s).1, fun s => ?_, hlhc, isUHC_Ioi_interval hl hu hl0 hlu,
    h.continuous_F.continuousOn, h.A_nonneg, fun p _ => h.F_le p, fun s => ⟨_, (h.safe_mem s.1
      s.2).1, by
      change 0 ≤ indF U c (s.1, h.safeY s.1, s.2)
      rw [(h.safe_mem s.1 s.2).2]; exact h.U_nonneg _ _ (le_of_lt s.1.2) s.2.2⟩,
    one_div_pos.2 (by linarith [h.r_pos]), ?_, continuous_fst.snd.continuousOn,
    contExp_first Q _ _ _ (lemma_9_5_compact Q hQ)⟩
  · rw [Subtype.isCompact_iff]
    have : Subtype.val '' indΓ (z₁ := z₁) (z₂ := z₂) δ' M s =
        Icc ((1 - δ') * s.1.1) (max M s.1.1) := by
      ext y
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hy; exact ⟨⟨y, lt_of_lt_of_le (hl0 s) hy.1⟩, hy, rfl⟩
    rw [this]
    exact isCompact_Icc
  · have := h.r_pos
    rw [div_lt_one (by linarith)]
    linarith

end IndHyp

end StokeyLucasPrescott.StochasticApplications
