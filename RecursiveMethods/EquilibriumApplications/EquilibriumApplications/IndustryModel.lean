/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Industry investment under uncertainty: the model (SLP §16.4, pp. 487–489)

The primitives of §10.4 and the production set (1) of §16.4.

* `IndustryCost c δ`: the adjustment cost `c` of §10.4 (`c = 0` on `[0, 1 − δ]`, strictly
  increasing and strictly convex on `[1 − δ, ∞)`, continuous). `IndustryCost.convexOn`: `c` is
  convex on `[0, ∞)`; `IndustryCost.persp_mono` and `IndustryCost.persp_convex`: the perspective
  `(k, k′) ↦ k c(k′/k)` is nonincreasing in `k` and jointly convex.
* `industryH c`: the inverse `h` of `c` on `[1 − δ, ∞)`, `h(y) = sup {x ≥ 0 : c(x) ≤ y}`;
  `industryH_spec` (`c(h(y)) = y`), `industryH_le_of`, `industryH_ge` (`h ≥ 1 − δ`),
  `industryH_mono` (so `h` is measurable), `industryH_le_one`, `one_le_industryH`,
  `industryH_persp_mono` (`k ↦ k h(I/k)` is nondecreasing).
* `IndustryAdapted ℱ q I`: `(q, I)` lies in the commodity space `L` (adapted to the filtration
  `ℱ` of the shock histories, uniformly bounded).
* `IndustryTech ℱ c δ k₀` (`Y`, (1), pp. 488–489).
* `industryCap c k₀ I`: the capital path determined by the investment plan,
  `k_{t+1} = k_t h(I_t/k_t)`; positive, adapted and bounded (`industryCap_pos`,
  `industryCap_meas`, `industryCap_le`), and `industryTech_of_cap`: a plan producing within this
  capital is in `Y`.
* `industryTech_convex`: `Y` is **convex** (the [Derived] NOTE to (1)); `industryTech_smul`:
  `Y` has constant returns to scale, `Y(λk₀) = λ Y(k₀)`.
* `IndustryDemand D z̲ z̄`: the inverse demand of §10.4; `surplusFn D q z = ∫₀^q D(v, z) dv`
  (`U`, consumers' surplus); `surplusFn_le` (the concavity inequality of the hint to
  Exercise 16.4(b)), `surplusFn_continuous`, `surplusFn_abs_le`, `surplusFn_lipschitz`, `D_le_bar`,
  `D_pos`.

**Modelling choices.** The shock histories `(Z^t, 𝒵^t, μ^t)` are represented by one probability
space `(Ω, μ)` with a filtration `ℱ` (`L_∞(Z^t, 𝒵^t, μ^t)` = bounded `ℱ_t`-measurable functions).
Plans are genuine functions and the constraints of (1) hold at every point; the passage to
equivalence classes is discussed in `IndustryLinfty`. `c` and `D` are taken continuous on all of
`ℝ` (resp. `ℝ²`): any continuous `c` on `ℝ₊`, `D` on `ℝ₊ × Z` extends. The `C¹` hypothesis on `c`
is not needed.

**Corrections.**
* (1), p. 488: `k₀ ≥ 0` must be `k₀ > 0` (`k₀` divides in `I₀ = k₀ c(k₁/k₀)`); here `k₀ > 0`
  wherever it matters, and then every capital path is positive (`industry_witness_pos`).
* (1): the equality `I_t = k_t c(k_{t+1}/k_t)` does not break convexity of `Y`; the proof
  (`industryTech_convex`) constructs the capital of a convex combination with the inverse `h`,
  and uses the joint convexity of the perspective of `c`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

/-- The **adjustment cost function** `c` of §10.4 (p. 293). -/
structure IndustryCost (c : ℝ → ℝ) (δ : ℝ) : Prop where
  delta_pos : 0 < δ
  delta_lt_one : δ < 1
  cont : Continuous c
  zero_on : ∀ x ∈ Icc 0 (1 - δ), c x = 0
  strictMono : StrictMonoOn c (Ici (1 - δ))
  strictConvex : StrictConvexOn ℝ (Ici (1 - δ)) c

namespace IndustryCost

variable {c : ℝ → ℝ} {δ : ℝ}

/-- `c(1 − δ) = 0`. -/
theorem at_one_sub (hc : IndustryCost c δ) : c (1 - δ) = 0 :=
  hc.zero_on _ ⟨by linarith [hc.delta_lt_one], le_rfl⟩

/-- `c ≥ 0` on `[0, ∞)`. -/
theorem nonneg (hc : IndustryCost c δ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ c x := by
  rcases le_total x (1 - δ) with h | h
  · rw [hc.zero_on x ⟨hx, h⟩]
  · rw [← hc.at_one_sub]
    exact hc.strictMono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 h) h

/-- `c(1) > 0`. -/
theorem one_pos (hc : IndustryCost c δ) : 0 < c 1 := by
  rw [← hc.at_one_sub]
  exact hc.strictMono (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith [hc.delta_pos]))
    (by linarith [hc.delta_pos])

/-- `c` is convex on `[0, ∞)` (it is `c ∘ max(·, 1 − δ)` there). -/
theorem convexOn (hc : IndustryCost c δ) : ConvexOn ℝ (Ici 0) c := by
  have hδ1 := hc.delta_lt_one
  set f : ℝ → ℝ := fun x => max x (1 - δ)
  have hf : ConvexOn ℝ (Ici 0) f := by
    refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [f, smul_eq_mul]
    refine max_le ?_ ?_
    · nlinarith [le_max_left x (1 - δ), le_max_left y (1 - δ)]
    · nlinarith [le_max_right x (1 - δ), le_max_right y (1 - δ)]
  have himg : f '' Ici 0 = Ici (1 - δ) := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact mem_Ici.2 (le_max_right x (1 - δ))
    · intro hy
      have hy' := mem_Ici.1 hy
      exact ⟨y, mem_Ici.2 (by linarith), max_eq_left hy'⟩
  have hcomp : ConvexOn ℝ (Ici 0) (c ∘ f) :=
    ConvexOn.comp (himg ▸ hc.strictConvex.convexOn) hf (himg ▸ hc.strictMono.monotoneOn)
  refine hcomp.congr fun x hx => ?_
  simp only [Function.comp, f]
  rcases le_total x (1 - δ) with h | h
  · rw [max_eq_right h, hc.at_one_sub, hc.zero_on x ⟨hx, h⟩]
  · rw [max_eq_left h]

/-- `c(λy) ≤ λ c(y)` for `0 ≤ λ ≤ 1`, `y ≥ 0`. -/
theorem scale_le (hc : IndustryCost c δ) {l y : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hy : 0 ≤ y) :
    c (l * y) ≤ l * c y := by
  have h := hc.convexOn.2 (mem_Ici.2 hy) (mem_Ici.2 le_rfl) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  rwa [hc.zero_on 0 ⟨le_rfl, by linarith [hc.delta_lt_one]⟩, mul_zero, add_zero] at h

/-- The perspective is nonincreasing in the scale: `s′ c(x/s′) ≤ s c(x/s)` for `0 < s ≤ s′`. -/
theorem persp_mono (hc : IndustryCost c δ) {s s' x : ℝ} (hs : 0 < s) (hss : s ≤ s')
    (hx : 0 ≤ x) : s' * c (x / s') ≤ s * c (x / s) := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  have h := hc.scale_le (div_nonneg hs.le hs'.le) ((div_le_one hs').2 hss) (div_nonneg hx hs.le)
  have he : s / s' * (x / s) = x / s' := by field_simp
  rw [he] at h
  calc s' * c (x / s') ≤ s' * (s / s' * c (x / s)) := mul_le_mul_of_nonneg_left h hs'.le
    _ = s * c (x / s) := by field_simp

/-- **Joint convexity of the perspective** `(k, k′) ↦ k c(k′/k)`. -/
theorem persp_convex (hc : IndustryCost c δ) {s s' x x' a b : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * s + b * s') * c ((a * x + b * x') / (a * s + b * s')) ≤
      a * (s * c (x / s)) + b * (s' * c (x' / s')) := by
  have hS : 0 < a * s + b * s' := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have : b = 1 := by linarith
      subst this
      linarith
    · nlinarith
  set S := a * s + b * s'
  have hμ : 0 ≤ a * s / S := div_nonneg (mul_nonneg ha hs.le) hS.le
  have hν : 0 ≤ b * s' / S := div_nonneg (mul_nonneg hb hs'.le) hS.le
  have hμν : a * s / S + b * s' / S = 1 := by rw [← add_div, div_self hS.ne']
  have h := hc.convexOn.2 (mem_Ici.2 (div_nonneg hx hs.le)) (mem_Ici.2 (div_nonneg hx' hs'.le))
    hμ hν hμν
  simp only [smul_eq_mul] at h
  have he : a * s / S * (x / s) + b * s' / S * (x' / s') = (a * x + b * x') / S := by
    field_simp
  rw [he] at h
  calc S * c ((a * x + b * x') / S) ≤ S * (a * s / S * c (x / s) + b * s' / S * c (x' / s')) :=
        mul_le_mul_of_nonneg_left h hS.le
    _ = a * (s * c (x / s)) + b * (s' * c (x' / s')) := by field_simp

/-- A linear lower bound from convexity: `c(1)(x − (1 − δ)) ≤ δ c(x)` for `x ≥ 1`. -/
theorem lower_linear (hc : IndustryCost c δ) {x : ℝ} (hx : 1 ≤ x) :
    c 1 * (x - (1 - δ)) ≤ δ * c x := by
  have hδ := hc.delta_pos
  have hd : 0 < x - (1 - δ) := by linarith
  set l := δ / (x - (1 - δ))
  have hl0 : 0 ≤ l := div_nonneg hδ.le hd.le
  have hl1 : l ≤ 1 := (div_le_one hd).2 (by linarith)
  have h := hc.strictConvex.convexOn.2 (mem_Ici.2 (by linarith : 1 - δ ≤ x))
    (mem_Ici.2 le_rfl) hl0 (by linarith : 0 ≤ 1 - l) (by ring)
  simp only [smul_eq_mul, hc.at_one_sub, mul_zero, add_zero] at h
  have he : l * x + (1 - l) * (1 - δ) = 1 := by
    simp only [l]
    field_simp
    ring
  rw [he] at h
  calc c 1 * (x - (1 - δ)) ≤ l * c x * (x - (1 - δ)) := mul_le_mul_of_nonneg_right h hd.le
    _ = δ * c x := by simp only [l]; field_simp

end IndustryCost

/-- The **inverse** `h` of `c` on `[1 − δ, ∞)`: `h(y) = sup {x ≥ 0 : c(x) ≤ max(y, 0)}`. -/
noncomputable def industryH (c : ℝ → ℝ) (y : ℝ) : ℝ := sSup {x | 0 ≤ x ∧ c x ≤ max y 0}

variable {c : ℝ → ℝ} {δ : ℝ}

/-- The set defining `h(y)` is bounded above. -/
theorem industryH_bdd (hc : IndustryCost c δ) (y : ℝ) :
    BddAbove {x | 0 ≤ x ∧ c x ≤ max y 0} := by
  have hδ := hc.delta_pos
  have h1 := hc.one_pos
  set Y := max y 0
  refine ⟨max 1 (Y * δ / c 1 + 1), fun x ⟨hx0, hcx⟩ => ?_⟩
  by_contra hlt
  push Not at hlt
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hlt.le
  have hx2 : Y * δ / c 1 + 1 < x := lt_of_le_of_lt (le_max_right _ _) hlt
  have hl := hc.lower_linear hx1
  have hY : 0 ≤ Y := le_max_right _ _
  have : Y * δ < c 1 * (x - 1) := by
    rw [div_add_one h1.ne', div_lt_iff₀ h1] at hx2
    nlinarith
  nlinarith

/-- `x ≥ 0` and `c(x) ≤ y` give `x ≤ h(y)`. -/
theorem industryH_le_of (hc : IndustryCost c δ) {x y : ℝ} (hx : 0 ≤ x) (hcx : c x ≤ y) :
    x ≤ industryH c y :=
  le_csSup (industryH_bdd hc y) ⟨hx, hcx.trans (le_max_left _ _)⟩

/-- `h(y) ≥ 1 − δ`. -/
theorem industryH_ge (hc : IndustryCost c δ) (y : ℝ) : 1 - δ ≤ industryH c y :=
  le_csSup (industryH_bdd hc y)
    ⟨by linarith [hc.delta_lt_one], by rw [hc.at_one_sub]; exact le_max_right _ _⟩

/-- `h > 0`. -/
theorem industryH_pos (hc : IndustryCost c δ) (y : ℝ) : 0 < industryH c y :=
  lt_of_lt_of_le (by linarith [hc.delta_lt_one]) (industryH_ge hc y)

/-- `c(h(y)) ≤ max(y, 0)`. -/
theorem industryH_spec_le (hc : IndustryCost c δ) (y : ℝ) : c (industryH c y) ≤ max y 0 := by
  have hcl : IsClosed {x | 0 ≤ x ∧ c x ≤ max y 0} :=
    isClosed_Ici.inter (isClosed_Iic.preimage hc.cont)
  exact (hcl.csSup_mem ⟨1 - δ, by linarith [hc.delta_lt_one], by
    rw [hc.at_one_sub]; exact le_max_right _ _⟩ (industryH_bdd hc y)).2

/-- `c(h(y)) = y` for `y ≥ 0`. -/
theorem industryH_spec (hc : IndustryCost c δ) {y : ℝ} (hy : 0 ≤ y) : c (industryH c y) = y := by
  have hδ := hc.delta_pos
  have hδ1 := hc.delta_lt_one
  have h1 := hc.one_pos
  refine le_antisymm ((industryH_spec_le hc y).trans (max_eq_left hy).le) ?_
  set B := max 1 (y * δ / c 1 + 1)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hcB : y ≤ c B := by
    have hl := hc.lower_linear hB1
    have hB2 : y * δ / c 1 + 1 ≤ B := le_max_right _ _
    rw [div_add_one h1.ne', div_le_iff₀ h1] at hB2
    nlinarith
  obtain ⟨x, hx, hcx⟩ := intermediate_value_Icc (by linarith : 1 - δ ≤ B) hc.cont.continuousOn
    ⟨by rw [hc.at_one_sub]; exact hy, hcB⟩
  have hxh : x ≤ industryH c y := industryH_le_of hc (by linarith [hx.1]) hcx.le
  calc y = c x := hcx.symm
    _ ≤ c (industryH c y) :=
      hc.strictMono.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 (hx.1.trans hxh)) hxh

/-- `h` is monotone. -/
theorem industryH_mono (hc : IndustryCost c δ) : Monotone (industryH c) := by
  intro y y' hyy
  refine csSup_le_csSup (industryH_bdd hc y') ⟨0, le_rfl, ?_⟩ fun x ⟨hx, hcx⟩ =>
    ⟨hx, hcx.trans (max_le_max hyy le_rfl)⟩
  rw [hc.zero_on 0 ⟨le_rfl, by linarith [hc.delta_lt_one]⟩]
  exact le_max_right _ _

/-- `h` is measurable (it is monotone). -/
theorem industryH_measurable (hc : IndustryCost c δ) : Measurable (industryH c) :=
  (industryH_mono hc).measurable

/-- `h(y) ≤ 1` for `y ≤ c(1)`. -/
theorem industryH_le_one (hc : IndustryCost c δ) {y : ℝ} (hy : y ≤ c 1) : industryH c y ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h := hc.strictMono (mem_Ici.2 (by linarith [hc.delta_pos])) (mem_Ici.2
    (le_trans (by linarith [hc.delta_pos]) hlt.le)) hlt
  have := industryH_spec_le hc y
  have := hc.one_pos
  rcases le_total y 0 with h0 | h0
  · rw [max_eq_right h0] at *
    linarith
  · rw [max_eq_left h0] at *
    linarith

/-- `h(y) ≥ 1` for `y ≥ c(1)`. -/
theorem one_le_industryH (hc : IndustryCost c δ) {y : ℝ} (hy : c 1 ≤ y) : 1 ≤ industryH c y :=
  industryH_le_of hc zero_le_one hy

/-- `k ↦ k h(I/k)` is nondecreasing on `(0, ∞)` for `I ≥ 0`. -/
theorem industryH_persp_mono (hc : IndustryCost c δ) {s s' I : ℝ} (hs : 0 < s) (hss : s ≤ s')
    (hI : 0 ≤ I) : s * industryH c (I / s) ≤ s' * industryH c (I / s') := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  set x := s * industryH c (I / s)
  have hx : 0 ≤ x := mul_nonneg hs.le (industryH_pos hc _).le
  have h1 : s' * c (x / s') ≤ I := by
    calc s' * c (x / s') ≤ s * c (x / s) := hc.persp_mono hs hss hx
      _ = I := by
        rw [show x / s = industryH c (I / s) by simp only [x]; field_simp,
          industryH_spec hc (div_nonneg hI hs.le)]
        field_simp
  have h2 : x / s' ≤ industryH c (I / s') :=
    industryH_le_of hc (div_nonneg hx hs'.le) (by rw [le_div_iff₀ hs']; linarith)
  calc x = s' * (x / s') := by field_simp
    _ ≤ s' * industryH c (I / s') := mul_le_mul_of_nonneg_left h2 hs'.le

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `(q, I)` lies in the **commodity space** `L` (p. 488): `q_t, I_t` are `ℱ_t`-measurable and
uniformly bounded. -/
def IndustryAdapted (ℱ : Filtration ℕ mΩ) (q I : ℕ → Ω → ℝ) : Prop :=
  (∀ t, StronglyMeasurable[ℱ t] (q t) ∧ StronglyMeasurable[ℱ t] (I t)) ∧
    ∃ B, ∀ t ω, |q t ω| ≤ B ∧ |I t ω| ≤ B

/-- The **production set** `Y` of (1) (pp. 488–489): `(q, I) ≥ 0` in `L` for which there is a
bounded adapted capital path `k` (`k_{t+1}` `ℱ_t`-measurable, `k₀` given) with
`k_{t+1} ≥ (1 − δ)k_t`, `q_t ≤ k_t`, `I_t = k_t c(k_{t+1}/k_t)`. -/
def IndustryTech (ℱ : Filtration ℕ mΩ) (c : ℝ → ℝ) (δ k0 : ℝ) :
    Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {x | IndustryAdapted ℱ x.1 x.2 ∧ (∀ t ω, 0 ≤ x.1 t ω ∧ 0 ≤ x.2 t ω) ∧
    ∃ k : ℕ → Ω → ℝ, (∀ ω, k 0 ω = k0) ∧ (∀ t, StronglyMeasurable[ℱ t] (k (t + 1))) ∧
      (∃ B, ∀ t ω, |k t ω| ≤ B) ∧
      ∀ t ω, (1 - δ) * k t ω ≤ k (t + 1) ω ∧ x.1 t ω ≤ k t ω ∧
        x.2 t ω = k t ω * c (k (t + 1) ω / k t ω)}

omit mΩ in
/-- Every capital path of (1) is positive (for `k₀ > 0`). -/
theorem industry_witness_pos (hc : IndustryCost c δ) {k0 : ℝ} (hk0 : 0 < k0)
    {k : ℕ → Ω → ℝ} (h0 : ∀ ω, k 0 ω = k0) (hdep : ∀ t ω, (1 - δ) * k t ω ≤ k (t + 1) ω) :
    ∀ t ω, 0 < k t ω := by
  intro t
  induction t with
  | zero => intro ω; rw [h0]; exact hk0
  | succ t ih =>
    intro ω
    have := mul_pos (by linarith [hc.delta_lt_one] : 0 < 1 - δ) (ih ω)
    linarith [hdep t ω]

/-- The **capital path** generated by an investment plan: `k₀` given,
`k_{t+1} = k_t h(I_t/k_t)`. -/
noncomputable def industryCap (c : ℝ → ℝ) (k0 : ℝ) (I : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => k0
  | t + 1 => fun ω => industryCap c k0 I t ω * industryH c (I t ω / industryCap c k0 I t ω)

omit mΩ in
/-- The generated capital path is positive. -/
theorem industryCap_pos (hc : IndustryCost c δ) {k0 : ℝ} (hk0 : 0 < k0) (I : ℕ → Ω → ℝ) :
    ∀ t ω, 0 < industryCap c k0 I t ω := by
  intro t
  induction t with
  | zero => intro ω; exact hk0
  | succ t ih => intro ω; exact mul_pos (ih ω) (industryH_pos hc _)

/-- The generated capital path is adapted: `k_t` and `k_{t+1}` are `ℱ_t`-measurable. -/
theorem industryCap_meas (hc : IndustryCost c δ) (ℱ : Filtration ℕ mΩ) (k0 : ℝ)
    {I : ℕ → Ω → ℝ} (hI : ∀ t, StronglyMeasurable[ℱ t] (I t)) :
    ∀ t, StronglyMeasurable[ℱ t] (industryCap c k0 I t) ∧
      StronglyMeasurable[ℱ t] (industryCap c k0 I (t + 1)) := by
  have step : ∀ t, StronglyMeasurable[ℱ t] (industryCap c k0 I t) →
      StronglyMeasurable[ℱ t] (industryCap c k0 I (t + 1)) := fun t hk =>
    (hk.measurable.mul ((industryH_measurable hc).comp
      ((hI t).measurable.div hk.measurable))).stronglyMeasurable
  intro t
  induction t with
  | zero =>
    have h0 : StronglyMeasurable[ℱ 0] (industryCap c k0 I 0) := stronglyMeasurable_const
    exact ⟨h0, step 0 h0⟩
  | succ t ih =>
    have h1 : StronglyMeasurable[ℱ (t + 1)] (industryCap c k0 I (t + 1)) :=
      ih.2.mono (ℱ.mono (Nat.le_succ t))
    exact ⟨h1, step (t + 1) h1⟩

omit mΩ in
/-- The generated capital path is bounded by `max(k₀, B/c(1))` when `0 ≤ I ≤ B`. -/
theorem industryCap_le (hc : IndustryCost c δ) {k0 B : ℝ} (hk0 : 0 < k0) {I : ℕ → Ω → ℝ}
    (hI : ∀ t ω, 0 ≤ I t ω ∧ I t ω ≤ B) :
    ∀ t ω, industryCap c k0 I t ω ≤ max k0 (B / c 1) := by
  have h1 := hc.one_pos
  set M := max k0 (B / c 1)
  have hM : 0 < M := lt_of_lt_of_le hk0 (le_max_left _ _)
  intro t
  induction t with
  | zero => intro ω; exact le_max_left _ _
  | succ t ih =>
    intro ω
    have hk := industryCap_pos hc hk0 I t ω
    change industryCap c k0 I t ω * industryH c (I t ω / industryCap c k0 I t ω) ≤ M
    have hB : B / M ≤ c 1 := by
      rw [div_le_iff₀ hM]
      have := le_max_right k0 (B / c 1)
      rw [div_le_iff₀ h1] at this
      linarith
    calc industryCap c k0 I t ω * industryH c (I t ω / industryCap c k0 I t ω)
        ≤ M * industryH c (I t ω / M) := industryH_persp_mono hc hk (ih ω) (hI t ω).1
      _ ≤ M * industryH c (B / M) := mul_le_mul_of_nonneg_left
          (industryH_mono hc (div_le_div_of_nonneg_right (hI t ω).2 hM.le)) hM.le
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left (industryH_le_one hc hB) hM.le
      _ = M := mul_one M

omit mΩ in
/-- The generated capital path satisfies the investment equation `I_t = k_t c(k_{t+1}/k_t)`
and `k_{t+1} ≥ (1 − δ) k_t`. -/
theorem industryCap_spec (hc : IndustryCost c δ) {k0 : ℝ} (hk0 : 0 < k0) {I : ℕ → Ω → ℝ}
    (hI : ∀ t ω, 0 ≤ I t ω) (t : ℕ) (ω : Ω) :
    (1 - δ) * industryCap c k0 I t ω ≤ industryCap c k0 I (t + 1) ω ∧
      I t ω = industryCap c k0 I t ω *
        c (industryCap c k0 I (t + 1) ω / industryCap c k0 I t ω) := by
  have hk := industryCap_pos hc hk0 I t ω
  change (1 - δ) * industryCap c k0 I t ω ≤
      industryCap c k0 I t ω * industryH c (I t ω / industryCap c k0 I t ω) ∧
    I t ω = industryCap c k0 I t ω * c (industryCap c k0 I t ω *
      industryH c (I t ω / industryCap c k0 I t ω) / industryCap c k0 I t ω)
  refine ⟨by have := industryH_ge hc (I t ω / industryCap c k0 I t ω); nlinarith, ?_⟩
  rw [mul_div_cancel_left₀ _ hk.ne', industryH_spec hc (div_nonneg (hI t ω) hk.le)]
  field_simp

/-- A nonnegative plan in `L` that produces within the capital generated by its investment lies
in `Y`. -/
theorem industryTech_of_cap (hc : IndustryCost c δ) {ℱ : Filtration ℕ mΩ} {k0 : ℝ} (hk0 : 0 < k0)
    {q I : ℕ → Ω → ℝ} (hA : IndustryAdapted ℱ q I) (hnn : ∀ t ω, 0 ≤ q t ω ∧ 0 ≤ I t ω)
    (hq : ∀ t ω, q t ω ≤ industryCap c k0 I t ω) : (q, I) ∈ IndustryTech ℱ c δ k0 := by
  obtain ⟨B, hB⟩ := hA.2
  have hIB : ∀ t ω, 0 ≤ I t ω ∧ I t ω ≤ B := fun t ω =>
    ⟨(hnn t ω).2, (le_abs_self _).trans (hB t ω).2⟩
  refine ⟨hA, hnn, industryCap c k0 I, fun _ => rfl,
    fun t => (industryCap_meas hc ℱ k0 (fun t => (hA.1 t).2) t).2,
    ⟨max k0 (B / c 1), fun t ω => ?_⟩, fun t ω => ?_⟩
  · rw [abs_of_pos (industryCap_pos hc hk0 I t ω)]
    exact industryCap_le hc hk0 hIB t ω
  · obtain ⟨h1, h2⟩ := industryCap_spec hc hk0 (fun t ω => (hnn t ω).2) t ω
    exact ⟨h1, hq t ω, h2⟩

/-- Convex combinations of adapted plans are adapted. -/
theorem IndustryAdapted.combo {ℱ : Filtration ℕ mΩ} {q I q' I' : ℕ → Ω → ℝ}
    (h : IndustryAdapted ℱ q I) (h' : IndustryAdapted ℱ q' I') (a b : ℝ) :
    IndustryAdapted ℱ (fun t ω => a * q t ω + b * q' t ω) (fun t ω => a * I t ω + b * I' t ω) := by
  obtain ⟨hm, B, hB⟩ := h
  obtain ⟨hm', B', hB'⟩ := h'
  refine ⟨fun t => ⟨((hm t).1.const_mul a).add ((hm' t).1.const_mul b),
    ((hm t).2.const_mul a).add ((hm' t).2.const_mul b)⟩, |a| * B + |b| * B', fun t ω => ?_⟩
  constructor
  · calc |a * q t ω + b * q' t ω| ≤ |a| * |q t ω| + |b| * |q' t ω| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * B + |b| * B' := add_le_add (mul_le_mul_of_nonneg_left (hB t ω).1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hB' t ω).1 (abs_nonneg _))
  · calc |a * I t ω + b * I' t ω| ≤ |a| * |I t ω| + |b| * |I' t ω| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * B + |b| * B' := add_le_add (mul_le_mul_of_nonneg_left (hB t ω).2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hB' t ω).2 (abs_nonneg _))

/-- **`Y` is convex** (the [Derived] NOTE to (1), p. 489), in the pointwise form: if
`(q, I), (q′, I′) ∈ Y` and `a, b ≥ 0`, `a + b = 1`, then `(aq + bq′, aI + bI′) ∈ Y`. The capital of
the combination is generated by its investment (`industryCap`), and dominates `ak + bk′` by the
perspective inequalities. -/
theorem industryTech_combo (hc : IndustryCost c δ) {ℱ : Filtration ℕ mΩ} {k0 : ℝ} (hk0 : 0 < k0)
    {q I q' I' : ℕ → Ω → ℝ} (hx : (q, I) ∈ IndustryTech ℱ c δ k0)
    (hx' : (q', I') ∈ IndustryTech ℱ c δ k0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    ((fun t ω => a * q t ω + b * q' t ω), (fun t ω => a * I t ω + b * I' t ω)) ∈
      IndustryTech ℱ c δ k0 := by
  obtain ⟨hA, hnn, k, hk0', -, -, hk⟩ := hx
  obtain ⟨hA', hnn', k', hk0'', -, -, hk'⟩ := hx'
  dsimp only at hA hnn hk hA' hnn' hk'
  have hkp := industry_witness_pos hc hk0 hk0' fun t ω => (hk t ω).1
  have hkp' := industry_witness_pos hc hk0 hk0'' fun t ω => (hk' t ω).1
  set I'' : ℕ → Ω → ℝ := fun t ω => a * I t ω + b * I' t ω
  set K := industryCap c k0 I''
  have hnn'' : ∀ t ω, 0 ≤ I'' t ω := fun t ω =>
    add_nonneg (mul_nonneg ha (hnn t ω).2) (mul_nonneg hb (hnn' t ω).2)
  have hKp := industryCap_pos hc hk0 I''
  -- the capital of the combination dominates the combination of capitals
  have hdom : ∀ t ω, a * k t ω + b * k' t ω ≤ K t ω := by
    intro t
    induction t with
    | zero =>
      intro ω
      change a * k 0 ω + b * k' 0 ω ≤ k0
      rw [hk0', hk0'', ← add_mul, hab, one_mul]
    | succ t ih =>
      intro ω
      set κ := a * k t ω + b * k' t ω
      set κ1 := a * k (t + 1) ω + b * k' (t + 1) ω
      have hκ : 0 < κ := by
        rcases eq_or_lt_of_le ha with h | h
        · subst h
          have : b = 1 := by linarith
          subst this
          simpa [κ] using hkp' t ω
        · have := mul_pos h (hkp t ω)
          have := mul_nonneg hb (hkp' t ω).le
          linarith
      have hκ1 : 0 ≤ κ1 :=
        add_nonneg (mul_nonneg ha (hkp (t + 1) ω).le) (mul_nonneg hb (hkp' (t + 1) ω).le)
      have hKt : 0 < K t ω := hKp t ω
      have hP1 := hc.persp_mono hκ (ih ω) hκ1
      have hP2 := hc.persp_convex (hkp t ω) (hkp' t ω) (hkp (t + 1) ω).le
        (hkp' (t + 1) ω).le ha hb hab
      have hI : I'' t ω = a * (k t ω * c (k (t + 1) ω / k t ω)) +
          b * (k' t ω * c (k' (t + 1) ω / k' t ω)) := by
        simp only [I'']
        rw [← (hk t ω).2.2, ← (hk' t ω).2.2]
      have hle : c (κ1 / K t ω) ≤ I'' t ω / K t ω := by
        rw [le_div_iff₀ hKt, mul_comm]
        linarith
      have h3 := industryH_le_of hc (div_nonneg hκ1 hKt.le) hle
      change κ1 ≤ K t ω * industryH c (I'' t ω / K t ω)
      calc κ1 = K t ω * (κ1 / K t ω) := by field_simp
        _ ≤ K t ω * industryH c (I'' t ω / K t ω) := mul_le_mul_of_nonneg_left h3 hKt.le
  refine industryTech_of_cap hc hk0 (hA.combo hA' a b) (fun t ω =>
    ⟨add_nonneg (mul_nonneg ha (hnn t ω).1) (mul_nonneg hb (hnn' t ω).1), hnn'' t ω⟩)
    fun t ω => le_trans ?_ (hdom t ω)
  exact add_le_add (mul_le_mul_of_nonneg_left (hk t ω).2.1 ha)
    (mul_le_mul_of_nonneg_left (hk' t ω).2.1 hb)

/-- **`Y` is convex** (as a subset of the space of plans). -/
theorem industryTech_convex (hc : IndustryCost c δ) (ℱ : Filtration ℕ mΩ) {k0 : ℝ}
    (hk0 : 0 < k0) : Convex ℝ (IndustryTech ℱ c δ k0) := by
  rintro ⟨q, I⟩ hx ⟨q', I'⟩ hx' a b ha hb hab
  have h := industryTech_combo hc hk0 hx hx' ha hb hab
  convert h using 1

/-- **Constant returns to scale**: `(q, I) ∈ Y(k₀)` implies `(λq, λI) ∈ Y(λk₀)` for `λ > 0`. -/
theorem industryTech_smul {ℱ : Filtration ℕ mΩ} {k0 l : ℝ} (hl : 0 < l) {q I : ℕ → Ω → ℝ}
    (hx : (q, I) ∈ IndustryTech ℱ c δ k0) :
    ((fun t ω => l * q t ω), (fun t ω => l * I t ω)) ∈ IndustryTech ℱ c δ (l * k0) := by
  obtain ⟨⟨hm, B, hB⟩, hnn, k, hk0, hkm, ⟨Bk, hBk⟩, hk⟩ := hx
  dsimp only at hm hB hnn hk
  refine ⟨⟨fun t => ⟨(hm t).1.const_mul l, (hm t).2.const_mul l⟩, l * B, fun t ω => ?_⟩,
    fun t ω => ⟨mul_nonneg hl.le (hnn t ω).1, mul_nonneg hl.le (hnn t ω).2⟩,
    fun t ω => l * k t ω, fun ω => by simp only [hk0], fun t => (hkm t).const_mul l,
    ⟨l * Bk, fun t ω => ?_⟩, fun t ω => ⟨?_, ?_, ?_⟩⟩
  · rw [abs_mul, abs_mul, abs_of_pos hl]
    exact ⟨mul_le_mul_of_nonneg_left (hB t ω).1 hl.le, mul_le_mul_of_nonneg_left (hB t ω).2 hl.le⟩
  · rw [abs_mul, abs_of_pos hl]
    exact mul_le_mul_of_nonneg_left (hBk t ω) hl.le
  · have := (hk t ω).1
    nlinarith
  · exact mul_le_mul_of_nonneg_left (hk t ω).2.1 hl.le
  · simp only
    rw [mul_div_mul_left _ _ hl.ne', (hk t ω).2.2]
    ring

/-- The **inverse demand function** `D` of §10.4 (p. 292), on `ℝ₊ × Z`, `Z = [z̲, z̄] ⊂ ℝ₊`. -/
structure IndustryDemand (D : ℝ → ℝ → ℝ) (zlo zhi : ℝ) : Prop where
  zlo_nonneg : 0 ≤ zlo
  zlo_le : zlo ≤ zhi
  cont : Continuous (Function.uncurry D)
  nonneg : ∀ q z, 0 ≤ q → z ∈ Icc zlo zhi → 0 ≤ D q z
  antiQ : ∀ z ∈ Icc zlo zhi, StrictAntiOn (fun q => D q z) (Ici 0)
  monoZ : ∀ q, 0 ≤ q → StrictMonoOn (D q) (Icc zlo zhi)
  pos_zero : ∀ z ∈ Icc zlo zhi, 0 < D 0 z
  tendsto_zero : ∀ z ∈ Icc zlo zhi, Tendsto (fun q => D q z) atTop (𝓝 0)
  surplus_bdd : ∃ A, ∀ z ∈ Icc zlo zhi, ∀ q, 0 ≤ q → ∫ v in (0 : ℝ)..q, D v z ≤ A

/-- **Total consumers' surplus** `U(q, z) = ∫₀^q D(v, z) dv` (§10.4). -/
noncomputable def surplusFn (D : ℝ → ℝ → ℝ) (q z : ℝ) : ℝ := ∫ v in (0 : ℝ)..q, D v z

variable {D : ℝ → ℝ → ℝ} {zlo zhi : ℝ}

/-- `D(q, z) ≤ D̄ = D(0, z̄)` on `ℝ₊ × Z`. -/
theorem D_le_bar (hD : IndustryDemand D zlo zhi) {q z : ℝ} (hq : 0 ≤ q) (hz : z ∈ Icc zlo zhi) :
    D q z ≤ D 0 zhi :=
  ((hD.antiQ z hz).antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hq) hq).trans
    ((hD.monoZ 0 le_rfl).monotoneOn hz ⟨hD.zlo_le, le_rfl⟩ hz.2)

/-- `D > 0` on `ℝ₊ × Z`. -/
theorem D_pos (hD : IndustryDemand D zlo zhi) {q z : ℝ} (hq : 0 ≤ q) (hz : z ∈ Icc zlo zhi) :
    0 < D q z := by
  by_contra h
  push Not at h
  have := (hD.antiQ z hz) (mem_Ici.2 hq) (mem_Ici.2 (by linarith : 0 ≤ q + 1)) (by linarith)
  have := hD.nonneg (q + 1) z (by linarith) hz
  simp only at *
  linarith

/-- `v ↦ D(v, z)` is interval integrable. -/
theorem D_intervalIntegrable (hD : IndustryDemand D zlo zhi) (z a b : ℝ) :
    IntervalIntegrable (fun v => D v z) MeasureTheory.volume a b :=
  (hD.cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b

/-- `U` is jointly continuous. -/
theorem surplusFn_continuous (hD : IndustryDemand D zlo zhi) :
    Continuous fun p : ℝ × ℝ => surplusFn D p.1 p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : ℝ × ℝ) (v : ℝ) => D v p.2)
    (hD.cont.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))) continuous_fst

/-- The **concavity inequality** of the hint to Exercise 16.4(b):
`U(q′, z) ≤ U(q, z) + D(q, z)(q′ − q)` for `q, q′ ≥ 0`, `z ∈ Z`. -/
theorem surplusFn_le (hD : IndustryDemand D zlo zhi) {q q' z : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (hz : z ∈ Icc zlo zhi) : surplusFn D q' z ≤ surplusFn D q z + D q z * (q' - q) := by
  have hsub : surplusFn D q' z - surplusFn D q z = ∫ v in q..q', D v z :=
    intervalIntegral.integral_interval_sub_left (D_intervalIntegrable hD z 0 q')
      (D_intervalIntegrable hD z 0 q)
  have hanti := (hD.antiQ z hz).antitoneOn
  rcases le_total q q' with h | h
  · have := intervalIntegral.integral_mono_on h (D_intervalIntegrable hD z q q')
      (intervalIntegrable_const (c := D q z)) fun v hv =>
        hanti (mem_Ici.2 hq) (mem_Ici.2 (hq.trans hv.1)) hv.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have := intervalIntegral.integral_mono_on h (intervalIntegrable_const (c := D q z))
      (D_intervalIntegrable hD z q' q) fun v hv =>
        hanti (mem_Ici.2 (hq'.trans hv.1)) (mem_Ici.2 hq) hv.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [intervalIntegral.integral_symm] at hsub
    linarith

/-- `U(0, z) = 0`. -/
theorem surplusFn_zero (z : ℝ) : surplusFn D 0 z = 0 := intervalIntegral.integral_same

/-- `0 ≤ U(q, z) ≤ D̄ q` for `q ≥ 0`, `z ∈ Z`. -/
theorem surplusFn_bounds (hD : IndustryDemand D zlo zhi) {q z : ℝ} (hq : 0 ≤ q)
    (hz : z ∈ Icc zlo zhi) : 0 ≤ surplusFn D q z ∧ surplusFn D q z ≤ D 0 zhi * q := by
  constructor
  · exact intervalIntegral.integral_nonneg hq fun v hv => hD.nonneg v z hv.1 hz
  · have h := surplusFn_le hD le_rfl hq hz
    rw [surplusFn_zero, zero_add, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (D_le_bar hD le_rfl hz) hq)

/-- `|U(q, z)| ≤ D̄ B` for `0 ≤ q ≤ B`. -/
theorem surplusFn_abs_le (hD : IndustryDemand D zlo zhi) {q z B : ℝ} (hq : 0 ≤ q) (hqB : q ≤ B)
    (hz : z ∈ Icc zlo zhi) : |surplusFn D q z| ≤ D 0 zhi * B := by
  obtain ⟨h1, h2⟩ := surplusFn_bounds hD hq hz
  rw [abs_of_nonneg h1]
  exact h2.trans (mul_le_mul_of_nonneg_left hqB (hD.pos_zero zhi ⟨hD.zlo_le, le_rfl⟩).le)

/-- `U(·, z)` is `D̄`-Lipschitz on `ℝ₊`. -/
theorem surplusFn_lipschitz (hD : IndustryDemand D zlo zhi) {q q' z : ℝ} (hq : 0 ≤ q)
    (hq' : 0 ≤ q') (hz : z ∈ Icc zlo zhi) :
    |surplusFn D q' z - surplusFn D q z| ≤ D 0 zhi * |q' - q| := by
  have h1 := surplusFn_le hD hq hq' hz
  have h2 := surplusFn_le hD hq' hq hz
  have b1 := D_le_bar hD hq hz
  have b2 := D_le_bar hD hq' hz
  have p1 := (D_pos hD hq hz).le
  have p2 := (D_pos hD hq' hz).le
  rw [abs_le]
  constructor
  · have : D q' z * (q - q') ≤ D 0 zhi * |q' - q| := by
      rw [abs_sub_comm]
      exact (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg p2]; gcongr)
    linarith
  · have : D q z * (q' - q) ≤ D 0 zhi * |q' - q| :=
      (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg p1]; gcongr)
    linarith

end StokeyLucasPrescott.EquilibriumApplications
