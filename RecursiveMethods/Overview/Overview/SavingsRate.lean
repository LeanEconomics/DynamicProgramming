/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.Technology
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# A constant savings rate

SLP Exercise 2.4, p. 15: `g(k) = s f(k)` with `f` as in Exercise 2.1.

For any `g` on `[0, ∞)` that is continuous, strictly increasing and strictly concave with
`g(0) = 0`, lying above the 45° line somewhere and below it somewhere:

* `exists_unique_fixedPoint` (Ex 2.4a): there is exactly one positive stationary point `k*`;
  `lt_of_lt_fixed`, `gt_of_gt_fixed`: `g(k) > k` below it and `g(k) < k` above it.
* `tendsto_fixedPoint`, `monotone_of_le`, `antitone_of_ge` (Ex 2.4b): from every `k₀ > 0` the
  sequence `k_{t+1} = g(k_t)` converges monotonically to `k*`; `iterate_eq_fixed_iff`: it reaches
  `k*` in finitely many periods only if it starts there.
* `savings_crossings`, `savings_unique_steady_state`: for `f` neoclassical, `s > 0` and
  `s(1 − δ) < 1` give the two crossings. The book states only `s > 0`; see
  `docs/corrections.md`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.Overview

/-- The assumptions on a savings function `g` on `[0, ∞)`. -/
structure SavingsMap (g : ℝ → ℝ) : Prop where
  zero : g 0 = 0
  cont : ContinuousOn g (Ici 0)
  mono : StrictMonoOn g (Ici 0)
  conc : StrictConcaveOn ℝ (Ici 0) g
  above : ∃ a, 0 < a ∧ a < g a
  below : ∃ b, 0 < b ∧ g b < b

namespace SavingsMap

variable {g : ℝ → ℝ} (hg : SavingsMap g)
include hg

/-- `g(k) − k` is strictly concave and vanishes at `0`, so it changes sign at most once on
`(0, ∞)`: if it is `≥ 0` at `y > 0` it is `> 0` on `(0, y)`. -/
theorem pos_of_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y ≤ g y) : x < g x := by
  have hy0 : 0 < y := hx.trans hxy
  have hA : 0 < 1 - x / y := by rw [sub_pos, div_lt_one hy0]; exact hxy
  have hB : 0 < x / y := by positivity
  have h := hg.conc.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy0.le) hy0.ne hA hB (by ring)
  simp only [smul_eq_mul, hg.zero, mul_zero, zero_add] at h
  rw [show x / y * y = x by field_simp] at h
  have : x / y * y ≤ x / y * g y := mul_le_mul_of_nonneg_left hy (by positivity)
  rw [show x / y * y = x by field_simp] at this
  linarith

/-- **Ex 2.4a.** There is exactly one positive stationary point. -/
theorem exists_unique_fixedPoint : ∃! k, 0 < k ∧ g k = k := by
  obtain ⟨a, ha, hga⟩ := hg.above
  obtain ⟨b, hb, hgb⟩ := hg.below
  have hab : a < b := by
    by_contra h
    push Not at h
    rcases h.eq_or_lt with rfl | h
    · linarith
    · have := hg.pos_of_lt hb h hga.le
      linarith
  -- existence by the intermediate value theorem for `g(k) − k`
  have hcont : ContinuousOn (fun k => g k - k) (Icc a b) :=
    (hg.cont.mono fun x hx => Set.mem_Ici.2 (ha.le.trans hx.1)).sub continuousOn_id
  obtain ⟨k, hk, hk0⟩ := intermediate_value_Icc' hab.le hcont
    (show (0 : ℝ) ∈ Icc (g b - b) (g a - a) from ⟨by linarith, by linarith⟩)
  refine ⟨k, ⟨ha.trans_le hk.1, by linarith⟩, fun j ⟨hj, hgj⟩ => ?_⟩
  -- uniqueness: two positive fixed points contradict strict concavity
  have hk0' : 0 < k := ha.trans_le hk.1
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hg.pos_of_lt hj h (by linarith)
    linarith
  · have := hg.pos_of_lt hk0' h hgj.ge
    linarith

/-- The positive stationary point `k*`. -/
noncomputable def kstar : ℝ := Classical.choose hg.exists_unique_fixedPoint

theorem kstar_pos : 0 < hg.kstar := (Classical.choose_spec hg.exists_unique_fixedPoint).1.1

theorem g_kstar : g hg.kstar = hg.kstar := (Classical.choose_spec hg.exists_unique_fixedPoint).1.2

theorem eq_kstar {k : ℝ} (hk : 0 < k) (hgk : g k = k) : k = hg.kstar :=
  (Classical.choose_spec hg.exists_unique_fixedPoint).2 k ⟨hk, hgk⟩

/-- Below `k*` the map lies above the 45° line. -/
theorem lt_of_lt_fixed {k : ℝ} (hk : 0 < k) (hks : k < hg.kstar) : k < g k :=
  hg.pos_of_lt hk hks hg.g_kstar.ge

/-- Above `k*` the map lies below the 45° line. -/
theorem gt_of_gt_fixed {k : ℝ} (hks : hg.kstar < k) : g k < k := by
  by_contra h
  push Not at h
  have := hg.pos_of_lt hg.kstar_pos hks h
  rw [hg.g_kstar] at this
  exact lt_irrefl _ this

theorem g_pos {k : ℝ} (hk : 0 < k) : 0 < g k := by
  have := hg.mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hk.le) hk
  rwa [hg.zero] at this

/-- Iterates from `k₀ ∈ (0, k*]` stay in `(0, k*]` and increase. -/
theorem iterate_mem_below {k₀ : ℝ} (hk₀ : 0 < k₀) (hle : k₀ ≤ hg.kstar) (t : ℕ) :
    0 < g^[t] k₀ ∧ g^[t] k₀ ≤ hg.kstar ∧ g^[t] k₀ ≤ g^[t + 1] k₀ := by
  induction t with
  | zero =>
    refine ⟨hk₀, hle, ?_⟩
    rcases hle.eq_or_lt with h | h
    · simp [h, hg.g_kstar]
    · exact (hg.lt_of_lt_fixed hk₀ h).le
  | succ t ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hpos : 0 < g^[t + 1] k₀ := by
      rw [Function.iterate_succ_apply']; exact hg.g_pos h0
    have hle' : g^[t + 1] k₀ ≤ hg.kstar := by
      rw [Function.iterate_succ_apply', ← hg.g_kstar]
      exact hg.mono.monotoneOn (Set.mem_Ici.2 h0.le) (Set.mem_Ici.2 hg.kstar_pos.le) h1
    refine ⟨hpos, hle', ?_⟩
    rw [Function.iterate_succ_apply' g (t + 1)]
    rcases hle'.eq_or_lt with h | h
    · rw [h, hg.g_kstar]
    · exact (hg.lt_of_lt_fixed hpos h).le

/-- Iterates from `k₀ ≥ k*` stay above `k*` and decrease. -/
theorem iterate_mem_above {k₀ : ℝ} (hge : hg.kstar ≤ k₀) (t : ℕ) :
    hg.kstar ≤ g^[t] k₀ ∧ g^[t + 1] k₀ ≤ g^[t] k₀ := by
  induction t with
  | zero =>
    refine ⟨hge, ?_⟩
    rcases hge.eq_or_lt with h | h
    · simp [← h, hg.g_kstar]
    · exact (hg.gt_of_gt_fixed h).le
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    have hge' : hg.kstar ≤ g^[t + 1] k₀ := by
      rw [Function.iterate_succ_apply', ← hg.g_kstar]
      exact hg.mono.monotoneOn (Set.mem_Ici.2 hg.kstar_pos.le)
        (Set.mem_Ici.2 (hg.kstar_pos.le.trans h1)) h1
    refine ⟨hge', ?_⟩
    rw [Function.iterate_succ_apply' g (t + 1)]
    rcases hge'.eq_or_lt with h | h
    · rw [← h, hg.g_kstar]
    · exact (hg.gt_of_gt_fixed h).le

/-- **Ex 2.4b (monotonicity).** From `k₀ ∈ (0, k*]` the sequence rises. -/
theorem monotone_of_le {k₀ : ℝ} (hk₀ : 0 < k₀) (hle : k₀ ≤ hg.kstar) :
    Monotone fun t => g^[t] k₀ :=
  monotone_nat_of_le_succ fun t => (hg.iterate_mem_below hk₀ hle t).2.2

/-- **Ex 2.4b (monotonicity).** From `k₀ ≥ k*` the sequence falls. -/
theorem antitone_of_ge {k₀ : ℝ} (hge : hg.kstar ≤ k₀) : Antitone fun t => g^[t] k₀ :=
  antitone_nat_of_succ_le fun t => (hg.iterate_mem_above hge t).2

/-- A limit of the iterates in `(0, ∞)` is a fixed point, hence `k*`. -/
theorem limit_eq_kstar {k₀ L : ℝ} (hL : 0 < L) (hlim : Tendsto (fun t => g^[t] k₀) atTop (𝓝 L))
    (hpos : ∀ t, 0 ≤ g^[t] k₀) : L = hg.kstar := by
  have hcontL : ContinuousWithinAt g (Ici 0) L := hg.cont L (Set.mem_Ici.2 hL.le)
  have h1 : Tendsto (fun t => g (g^[t] k₀)) atTop (𝓝 (g L)) :=
    hcontL.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hpos⟩)
  have h2 : Tendsto (fun t => g (g^[t] k₀)) atTop (𝓝 L) := by
    have := hlim.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Function.iterate_succ_apply'] using this
  exact hg.eq_kstar hL (tendsto_nhds_unique h1 h2)

/-- **Ex 2.4b.** From every `k₀ > 0` the sequence `k_{t+1} = g(k_t)` converges to `k*`. -/
theorem tendsto_fixedPoint {k₀ : ℝ} (hk₀ : 0 < k₀) :
    Tendsto (fun t => g^[t] k₀) atTop (𝓝 hg.kstar) := by
  rcases le_total k₀ hg.kstar with hle | hge
  · have hb := hg.iterate_mem_below hk₀ hle
    have hmono := hg.monotone_of_le hk₀ hle
    have hbdd : BddAbove (range fun t => g^[t] k₀) :=
      ⟨hg.kstar, by rintro _ ⟨t, rfl⟩; exact (hb t).2.1⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hLpos : 0 < ⨆ t, g^[t] k₀ := hk₀.trans_le (le_ciSup hbdd 0)
    rwa [← hg.limit_eq_kstar hLpos hlim fun t => (hb t).1.le]
  · have ha := hg.iterate_mem_above hge
    have hanti := hg.antitone_of_ge hge
    have hbdd : BddBelow (range fun t => g^[t] k₀) :=
      ⟨hg.kstar, by rintro _ ⟨t, rfl⟩; exact (ha t).1⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hLpos : 0 < ⨅ t, g^[t] k₀ :=
      hg.kstar_pos.trans_le (le_ciInf fun t => (ha t).1)
    rwa [← hg.limit_eq_kstar hLpos hlim fun t => (hg.kstar_pos.le.trans (ha t).1)]

/-- **Ex 2.4b (no finite-time arrival).** The sequence reaches `k*` in finitely many periods only
if `k₀ = k*`. -/
theorem iterate_eq_fixed_iff {k₀ : ℝ} (hk₀ : 0 < k₀) (t : ℕ) :
    g^[t] k₀ = hg.kstar ↔ k₀ = hg.kstar := by
  constructor
  · intro h
    induction t generalizing k₀ with
    | zero => exact h
    | succ t ih =>
      rw [Function.iterate_succ_apply] at h
      have := ih (hg.g_pos hk₀) h
      rw [← hg.g_kstar] at this
      exact hg.mono.injOn (Set.mem_Ici.2 hk₀.le) (Set.mem_Ici.2 hg.kstar_pos.le) this
  · intro h
    rw [h]
    exact Function.iterate_fixed hg.g_kstar t

end SavingsMap

namespace Neoclassical

variable {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} (hF : Neoclassical F Fk)
include hF

/-- Near zero `s f(k) > k`: the mean value theorem and `f′(0+) = ∞`. -/
theorem savings_above {δ s : ℝ} (hs : 0 < s) :
    ∃ a, 0 < a ∧ a < s * goods F δ a := by
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), 1 / s < Fk k + (1 - δ) :=
    (hF.f'_tendsto_zero δ).eventually (eventually_gt_atTop (1 / s))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set a := ε / 2
  have ha : 0 < a := by positivity
  refine ⟨a, ha, ?_⟩
  have hcont : ContinuousOn (goods F δ) (Icc 0 a) :=
    ((hF.cont_F).add (continuousOn_const.mul continuousOn_id)).mono Icc_subset_Ici_self
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (goods F δ) (fun k => Fk k + (1 - δ)) ha
    hcont (fun x hx => hF.hasDerivAt_f δ hx.1)
  have hξε : ξ ∈ Metric.ball (0 : ℝ) ε ∩ Ioi 0 :=
    ⟨by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hξ.1]
      have : ξ < ε / 2 := hξ.2
      linarith,
      hξ.1⟩
  have hbig : 1 / s < Fk ξ + (1 - δ) := hball hξε
  rw [hslope, hF.f_zero δ, sub_zero, sub_zero, lt_div_iff₀ ha] at hbig
  have e : s * (1 / s * a) = a := by field_simp
  nlinarith

/-- For large `k`, `s f(k) < k`: concavity and `s f′(∞) = s(1 − δ) < 1`. -/
theorem savings_below {δ s : ℝ} (hs : 0 < s) (hsδ : s * (1 - δ) < 1) :
    ∃ b, 0 < b ∧ s * goods F δ b < b := by
  -- a point `K` where `s f′(K) < 1`
  have hev : ∀ᶠ k in atTop, s * (Fk k + (1 - δ)) < 1 := by
    have := ((hF.f'_tendsto_atTop δ).const_mul s).eventually (gt_mem_nhds hsδ)
    exact this
  obtain ⟨K, hK⟩ := (hev.and (eventually_gt_atTop 0)).exists
  set m := Fk K + (1 - δ)
  have hm : s * m < 1 := hK.1
  -- the tangent line at `K` bounds `f`
  have htan : ∀ k, 0 ≤ k → goods F δ k ≤ goods F δ K + m * (k - K) := fun k hk =>
    concave_le_tangent (hF.strictConcaveOn_f δ).concaveOn (Set.mem_Ici.2 hK.2.le) (Set.mem_Ici.2 hk)
      (hF.hasDerivAt_f δ hK.2)
  set b := max K ((s * |goods F δ K| + s * |m| * K + 1) / (1 - s * m)) + 1
  have h1 : 0 < 1 - s * m := sub_pos.2 hm
  have hbK : K < b := by simp only [b]; linarith [le_max_left K ((s * |goods F δ K| +
    s * |m| * K + 1) / (1 - s * m))]
  have hbig : (s * |goods F δ K| + s * |m| * K + 1) / (1 - s * m) < b := by
    simp only [b]; linarith [le_max_right K ((s * |goods F δ K| + s * |m| * K + 1) / (1 - s * m))]
  have hb0 : 0 < b := hK.2.trans hbK
  refine ⟨b, hb0, ?_⟩
  have ht := mul_le_mul_of_nonneg_left (htan b hb0.le) hs.le
  rw [div_lt_iff₀ h1] at hbig
  have e1 : s * goods F δ K ≤ s * |goods F δ K| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.le
  have e2 : -(s * m * K) ≤ s * |m| * K := by
    have : -(m * K) ≤ |m| * K := by
      have := neg_abs_le m
      nlinarith [hK.2]
    nlinarith
  nlinarith

/-- **Ex 2.4 (crossings).** With `s > 0` and `s(1 − δ) < 1`, `g = s f` is a savings map. -/
theorem savings_crossings {δ s : ℝ} (hδ1 : δ ≤ 1) (hs : 0 < s) (hsδ : s * (1 - δ) < 1) :
    SavingsMap fun k => s * goods F δ k where
  zero := by simp [hF.f_zero δ]
  cont := continuousOn_const.mul ((hF.cont_F).add (continuousOn_const.mul continuousOn_id))
  mono := fun x hx y hy hxy => mul_lt_mul_of_pos_left (hF.strictMonoOn_f hδ1 hx hy hxy) hs
  conc := ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => by
    have := (hF.strictConcaveOn_f δ).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    nlinarith⟩
  above := hF.savings_above hs
  below := hF.savings_below hs hsδ

/-- **Ex 2.4a for the neoclassical model.** There is exactly one positive stationary point of
`k ↦ s f(k)`, and every path from `k₀ > 0` converges monotonically to it. -/
theorem savings_unique_steady_state {δ s : ℝ} (hδ1 : δ ≤ 1) (hs : 0 < s)
    (hsδ : s * (1 - δ) < 1) : ∃! k, 0 < k ∧ s * goods F δ k = k :=
  (hF.savings_crossings hδ1 hs hsδ).exists_unique_fixedPoint

end Neoclassical

end StokeyLucasPrescott.Overview
