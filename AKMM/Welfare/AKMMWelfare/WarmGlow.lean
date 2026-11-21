/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMWelfare.OGProduction
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Dynamic inefficiency in the warm-glow model

AKMM, §6.4.3, p. 183. One-period lives, utility `u(cₜ) + Ab_{t+1}`, budget
`cₜ + b_{t+1} = (1 + rₜ − δ)bₜ + wₜ`, `b = k` in equilibrium.

* The consumption choice `u′(c̄) = A` is optimal (`warmglow_consumption`), and the law of motion
  is `k_{t+1} = (1 − δ)kₜ + F(kₜ, 1) − c̄` (`warmglow_law_of_motion`). Steady states solve
  `φ(k) = c̄` with `φ(k) = F(k, 1) − δk` (`warmglow_steady_iff`).
* With `φ` continuous and strictly concave on `[0, ∞)`, `φ(0) = 0`, `0 < c̄ < φ(k̂)` for some `k̂`
  and `φ < c̄` far out, there are exactly two positive steady states `k₁ < k₂`
  (`warmglow_two_steady_states`); `φ > c̄` between them and `φ < c̄` outside (`warmglow_sign`).
* At `k₂` the slope `1 + F₁ − δ = 1 + φ′(k₂)` is below `1`; at `k₁` it is above `1`
  (`warmglow_slopes`). The upper steady state is stable: every path from `k₀ > k₁` converges to
  `k₂` (`warmglow_stable`); paths from below `k₁` never approach it (`warmglow_lower_unstable`).
* The upper steady state is dynamically inefficient (`warmglow_inefficient`, by Theorem .5(i)).
* A concrete instance, `F(k, 1) = 2√k`, `δ = 1/2`, `c̄ = 3/2`, with steady states `1` and `9`
  (`warmglow_instance`).

**Correction (p. 183).** "There are two positive steady states" needs `c̄ < max_k φ(k)`, which the
book does not state; for `c̄` above the maximum there is no steady state
(`warmglow_no_steady_state`). Footnote 15 (welfare with warm glow) is not formalised.
-/

namespace AKMM.Welfare

open Filter Topology Miao.OverlappingGenerations

/-- **AKMM, p. 183: the consumption choice.** With `u` concave on `(0, ∞)`, `c̄ > 0` and
`u′(c̄) = A`, consumption `c̄` maximises `u(c) + A(W − c)` (bequest `b′ = W − c`). -/
theorem warmglow_consumption {u : ℝ → ℝ} {A W cbar : ℝ} (hu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hc : 0 < cbar) (hd : HasDerivAt u A cbar) :
    ∀ c, 0 < c → u c + A * (W - c) ≤ u cbar + A * (W - cbar) := by
  intro c hc'
  have := op_concave_tangent hu (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') hd
  linarith

/-- **AKMM, p. 183: the law of motion.** With `F(k, 1) = rk + w` (factor payments exhaust
output) and `b = k`, the bequest rule `b′ = (1 + r − δ)b + w − c̄` is
`k′ = (1 − δ)k + F(k, 1) − c̄`. -/
theorem warmglow_law_of_motion {r w δ k cbar Fk : ℝ} (hF : Fk = r * k + w) :
    (1 + r - δ) * k + w - cbar = (1 - δ) * k + Fk - cbar := by
  rw [hF]; ring

/-- AKMM, p. 183: `k` is a steady state of `k′ = (1 − δ)k + F(k, 1) − c̄` iff
`φ(k) = F(k, 1) − δk = c̄`. -/
theorem warmglow_steady_iff {δ k cbar Fk : ℝ} :
    (1 - δ) * k + Fk - cbar = k ↔ Fk - δ * k = cbar := by
  constructor <;> intro h <;> linarith

/-- The shape of `φ` around two roots `k₁ < k₂` of `φ = c̄` (strict concavity on `[0, ∞)`):
`φ > c̄` strictly between them, `φ < c̄` on `[0, k₁)` and on `(k₂, ∞)`. -/
theorem warmglow_sign {φ : ℝ → ℝ} {cbar k1 k2 : ℝ} (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ)
    (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hr1 : φ k1 = cbar) (hr2 : φ k2 = cbar) :
    (∀ x, k1 < x → x < k2 → cbar < φ x) ∧ (∀ x, 0 ≤ x → x < k1 → φ x < cbar) ∧
      (∀ x, k2 < x → φ x < cbar) := by
  have m1 : k1 ∈ Set.Ici (0 : ℝ) := hk1
  have m2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  refine ⟨fun x hx1 hx2 => ?_, fun x hx0 hx1 => ?_, fun x hx => ?_⟩
  · set a := (k2 - x) / (k2 - k1) with ha
    have ha0 : 0 < a := div_pos (by linarith) (by linarith)
    have ha1 : 0 < 1 - a := by rw [ha, sub_pos, div_lt_one (by linarith)]; linarith
    have hne : k2 - k1 ≠ 0 := by linarith
    have hx : a * k1 + (1 - a) * k2 = x := by rw [ha]; field_simp; ring
    have := hφ.2 m1 m2 h12.ne ha0 ha1 (by ring)
    simp only [smul_eq_mul, hx, hr1, hr2] at this
    linarith
  · set a := (k2 - k1) / (k2 - x) with ha
    have ha0 : 0 < a := div_pos (by linarith) (by linarith)
    have ha1 : 0 < 1 - a := by rw [ha, sub_pos, div_lt_one (by linarith)]; linarith
    have hne : k2 - x ≠ 0 := by linarith
    have hx : a * x + (1 - a) * k2 = k1 := by rw [ha]; field_simp; ring
    have := hφ.2 (Set.mem_Ici.2 hx0) m2 (by linarith : x ≠ k2) ha0 ha1 (by ring)
    simp only [smul_eq_mul, hx, hr1, hr2] at this
    nlinarith
  · set a := (k2 - k1) / (x - k1) with ha
    have ha0 : 0 < a := div_pos (by linarith) (by linarith)
    have ha1 : 0 < 1 - a := by rw [ha, sub_pos, div_lt_one (by linarith)]; linarith
    have hne : x - k1 ≠ 0 := by linarith
    have hx' : (1 - a) * k1 + a * x = k2 := by rw [ha]; field_simp; ring
    have := hφ.2 m1 (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x)) (by linarith : k1 ≠ x) ha1 ha0
      (by ring)
    simp only [smul_eq_mul, hx', hr1, hr2] at this
    nlinarith

/-- **AKMM, p. 183: exactly two positive steady states** (under the condition the book omits).
Let `φ` be continuous and strictly concave on `[0, ∞)` with `φ(0) = 0`, `c̄ > 0`, `φ(k̂) > c̄` for
some `k̂ > 0` (so `c̄ < max φ`) and `φ(K) < c̄` for some `K > k̂`. Then there are `0 < k₁ < k₂` with
`φ(k₁) = φ(k₂) = c̄`, and every `k ≥ 0` with `φ(k) = c̄` is `k₁` or `k₂`. -/
theorem warmglow_two_steady_states {φ : ℝ → ℝ} {cbar khat K : ℝ}
    (hcont : ContinuousOn φ (Set.Ici 0)) (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (h0 : φ 0 = 0)
    (hc : 0 < cbar) (hkhat : 0 < khat) (hhat : cbar < φ khat) (hK : khat < K) (hKc : φ K < cbar) :
    ∃ k1 k2, 0 < k1 ∧ k1 < k2 ∧ φ k1 = cbar ∧ φ k2 = cbar ∧
      ∀ k, 0 ≤ k → φ k = cbar → k = k1 ∨ k = k2 := by
  obtain ⟨k1, hk1, hr1⟩ := intermediate_value_Ioo hkhat.le
    (hcont.mono fun x hx => Set.mem_Ici.2 hx.1) ⟨by rw [h0]; exact hc, hhat⟩
  obtain ⟨k2, hk2, hr2⟩ := intermediate_value_Ioo' hK.le
    (hcont.mono fun x hx => Set.mem_Ici.2 (hkhat.le.trans hx.1)) ⟨hKc, hhat⟩
  have h12 : k1 < k2 := hk1.2.trans hk2.1
  refine ⟨k1, k2, hk1.1, h12, hr1, hr2, fun k hk hrk => ?_⟩
  obtain ⟨hmid, hlow, hhigh⟩ := warmglow_sign hφ hk1.1.le h12 hr1 hr2
  rcases lt_trichotomy k k1 with h | h | h
  · exact absurd hrk (hlow k hk h).ne
  · exact Or.inl h
  · rcases lt_trichotomy k k2 with h' | h' | h'
    · exact absurd hrk (hmid k h h').ne'
    · exact Or.inr h'
    · exact absurd hrk (hhigh k h').ne

/-- **AKMM, p. 183: the slopes at the steady states.** If `φ` has derivative `φ′(kᵢ)` at the
roots `k₁ < k₂`, then `g′(k₂) = 1 + φ′(k₂) < 1` and `g′(k₁) = 1 + φ′(k₁) > 1`, where
`g(k) = (1 − δ)k + F(k, 1) − c̄` and `1 + φ′ = 1 + F₁ − δ`. -/
theorem warmglow_slopes {φ : ℝ → ℝ} {cbar k1 k2 d1 d2 : ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hr1 : φ k1 = cbar)
    (hr2 : φ k2 = cbar) (hd1 : HasDerivAt φ d1 k1) (hd2 : HasDerivAt φ d2 k2) :
    1 + d2 < 1 ∧ 1 < 1 + d1 := by
  have m1 : k1 ∈ Set.Ici (0 : ℝ) := hk1
  have m2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  have t2 := op_strictConcave_tangent hφ m2 m1 h12.ne hd2
  have t1 := op_strictConcave_tangent hφ m1 m2 h12.ne' hd1
  rw [hr1, hr2] at t1 t2
  constructor <;> nlinarith

/-- **AKMM, p. 183: the upper steady state is stable.** Let `g(k) = k + φ(k) − c̄` be continuous
and monotone on `[0, ∞)`, with roots `k₁ < k₂` of `φ = c̄` as in `warmglow_sign`. Every path
`k_{t+1} = g(kₜ)` from `k₀ > k₁` converges to `k₂`. -/
theorem warmglow_stable {φ : ℝ → ℝ} {cbar k1 k2 : ℝ} {k : ℕ → ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ)
    (hgc : ContinuousOn (fun x => x + φ x - cbar) (Set.Ici 0))
    (hgm : MonotoneOn (fun x => x + φ x - cbar) (Set.Ici 0)) (hk1 : 0 ≤ k1) (h12 : k1 < k2)
    (hr1 : φ k1 = cbar) (hr2 : φ k2 = cbar) (hpath : ∀ t, k (t + 1) = k t + φ (k t) - cbar)
    (hk0 : k1 < k 0) : Tendsto k atTop (𝓝 k2) := by
  obtain ⟨hmid, -, hhigh⟩ := warmglow_sign hφ hk1 h12 hr1 hr2
  set g := fun x => x + φ x - cbar with hg
  have hg2 : g k2 = k2 := by simp [hg, hr2]
  have hm2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  -- the limit of a convergent path in `[k₁, ∞)` is a fixed point
  have hfix : ∀ L, k1 < L → Tendsto k atTop (𝓝 L) → L = k2 := by
    intro L hL hlim
    have hL0 : L ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
    have h1 : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hlim.comp (tendsto_add_atTop_nat 1)
    have hev : ∀ᶠ t in atTop, k t ∈ Set.Ici (0 : ℝ) :=
      hlim.eventually (Ici_mem_nhds (by linarith : (0 : ℝ) < L) |> fun h =>
        Filter.mem_of_superset (Ioi_mem_nhds (by linarith : (0 : ℝ) < L))
          fun x hx => Set.mem_Ici.2 (le_of_lt hx))
    have h2 : Tendsto (fun t => g (k t)) atTop (𝓝 (g L)) :=
      ((hgc L hL0).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨hlim, hev⟩)
    have h3 : (fun t => k (t + 1)) = fun t => g (k t) := funext hpath
    rw [h3] at h1
    have hgL : g L = L := tendsto_nhds_unique h2 h1
    simp only [hg] at hgL
    have hφL : φ L = cbar := by linarith
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · linarith [hmid L hL h]
    · linarith [hhigh L h]
  rcases le_or_gt (k 0) k2 with hlo | hhi
  · -- increasing and bounded by `k₂`
    have hin : ∀ t, k1 < k t ∧ k t ≤ k2 := by
      intro t
      induction t with
      | zero => exact ⟨hk0, hlo⟩
      | succ t ih =>
        have hm : k t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [ih.1])
        have hup : g (k t) ≤ g k2 := hgm hm hm2 ih.2
        have hφt : cbar ≤ φ (k t) := by
          rcases ih.2.lt_or_eq with h | h
          · exact (hmid _ ih.1 h).le
          · rw [h, hr2]
        rw [hpath t]
        refine ⟨by linarith [ih.1], ?_⟩
        simp only [hg] at hup
        linarith
    have hmono : Monotone k := monotone_nat_of_le_succ fun t => by
      have := hin t
      have hφt : cbar ≤ φ (k t) := by
        rcases this.2.lt_or_eq with h | h
        · exact (hmid _ this.1 h).le
        · rw [h, hr2]
      rw [hpath t]; linarith
    have hbdd : BddAbove (Set.range k) := ⟨k2, by rintro _ ⟨t, rfl⟩; exact (hin t).2⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hL : k1 < ⨆ t, k t := lt_of_lt_of_le hk0 (le_ciSup hbdd 0)
    rw [hfix _ hL hlim] at hlim
    exact hlim
  · -- decreasing and bounded below by `k₂`
    have hin : ∀ t, k2 ≤ k t := by
      intro t
      induction t with
      | zero => exact hhi.le
      | succ t ih =>
        have hm : k t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
        have := hgm hm2 hm ih
        rw [hpath t]
        simp only [hg] at this
        linarith
    have hanti : Antitone k := antitone_nat_of_succ_le fun t => by
      have hφt : φ (k t) ≤ cbar := by
        rcases (hin t).lt_or_eq with h | h
        · exact (hhigh _ h).le
        · rw [← h, hr2]
      rw [hpath t]; linarith
    have hbdd : BddBelow (Set.range k) := ⟨k2, by rintro _ ⟨t, rfl⟩; exact hin t⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hL : k1 < ⨅ t, k t := lt_of_lt_of_le h12 (le_ciInf hin)
    rw [hfix _ hL hlim] at hlim
    exact hlim

/-- **AKMM, p. 183: the lower steady state is unstable from below.** If `0 ≤ k₀ < k₁` and the
path stays in `[0, ∞)`, it decreases: `kₜ ≤ k₀ < k₁` for all `t`, so it never approaches `k₁`. -/
theorem warmglow_lower_unstable {φ : ℝ → ℝ} {cbar k1 k2 : ℝ} {k : ℕ → ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hr1 : φ k1 = cbar)
    (hr2 : φ k2 = cbar) (hpath : ∀ t, k (t + 1) = k t + φ (k t) - cbar)
    (hk0 : k 0 < k1) (hnn : ∀ t, 0 ≤ k t) : (∀ t, k t ≤ k 0) ∧ ¬ Tendsto k atTop (𝓝 k1) := by
  obtain ⟨-, hlow, -⟩ := warmglow_sign hφ hk1 h12 hr1 hr2
  have hdec : ∀ t, k t ≤ k 0 := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      rw [hpath t]
      linarith [hlow (k t) (hnn t) (by linarith)]
  refine ⟨hdec, fun hlim => ?_⟩
  have := le_of_tendsto' hlim hdec
  linarith

/-- **AKMM, p. 183: the upper steady state is dynamically inefficient.** With
`f(k) = F(k, 1) + (1 − δ)k = k + φ(k)` and `f′(k₂) = 1 + φ′(k₂) < 1` (`warmglow_slopes`), the
steady state `k₂` (consumption `c̄ ≥ 0`) is inefficient by Theorem .5(i). -/
theorem warmglow_inefficient {φ : ℝ → ℝ} {cbar k1 k2 d2 : ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hc : 0 ≤ cbar)
    (hr1 : φ k1 = cbar) (hr2 : φ k2 = cbar) (hd2 : HasDerivAt φ d2 k2) :
    ¬ deEfficient (fun _ => fun x => x + φ x) (fun _ => k2) := by
  have m1 : k1 ∈ Set.Ici (0 : ℝ) := hk1
  have m2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  have t2 := op_strictConcave_tangent hφ m2 m1 h12.ne hd2
  rw [hr1, hr2] at t2
  have hneg : d2 < 0 := by nlinarith
  exact theorem_A5_inefficient (by linarith)
    (show 0 ≤ k2 + φ k2 - k2 by rw [hr2]; linarith) ((hasDerivAt_id k2).add hd2) (by linarith)

/-- **AKMM, p. 183: an instance.** With `F(k, 1) = 2√k`, `δ = 1/2` and `c̄ = 3/2`,
`φ(k) = 2√k − k/2` satisfies every hypothesis of `warmglow_two_steady_states` (with `k̂ = 4`,
`K = 16`), its steady states are `1` and `9`, and at `9` the slope is `1 + φ′(9) = 5/6 < 1`. -/
theorem warmglow_instance :
    ContinuousOn (fun k : ℝ => 2 * √k - k / 2) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k - k / 2) ∧
      (2 * √0 - 0 / 2 : ℝ) = 0 ∧ (3 / 2 : ℝ) < 2 * √4 - 4 / 2 ∧ 2 * √16 - 16 / 2 < (3 / 2 : ℝ) ∧
      (2 * √1 - 1 / 2 : ℝ) = 3 / 2 ∧ (2 * √9 - 9 / 2 : ℝ) = 3 / 2 ∧
      HasDerivAt (fun k : ℝ => 2 * √k - k / 2) (-1 / 6) 9 := by
  have e4 : √(4 : ℝ) = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e9 : √(9 : ℝ) = 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e16 : √(16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨(continuous_const.mul Real.continuous_sqrt).sub (continuous_id.div_const 2)
    |>.continuousOn, ?_, by simp, by rw [e4]; norm_num, by rw [e16]; norm_num,
    by simp; norm_num, by rw [e9]; norm_num, ?_⟩
  · have hsq := Real.strictConcaveOn_sqrt
    refine ⟨hsq.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := hsq.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
  · have h := ((Real.hasDerivAt_sqrt (by norm_num : (9 : ℝ) ≠ 0)).const_mul 2).sub
      ((hasDerivAt_id (9 : ℝ)).div_const 2)
    rw [e9] at h
    exact h.congr_deriv (by norm_num)

/-- **AKMM, p. 183 (correction): no steady state when `c̄` exceeds `max φ`.** In the instance,
`φ(k) = 2√k − k/2 ≤ 2` for all `k ≥ 0`, so with `c̄ = 3` there is no steady state. -/
theorem warmglow_no_steady_state : ∀ k : ℝ, 0 ≤ k → 2 * √k - k / 2 ≠ 3 := by
  intro k hk h
  have hs := Real.sq_sqrt hk
  nlinarith [sq_nonneg (√k - 2), Real.sqrt_nonneg k]

end AKMM.Welfare
