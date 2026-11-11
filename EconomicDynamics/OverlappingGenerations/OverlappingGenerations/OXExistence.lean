/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OXEconomy
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Existence of monetary equilibrium (Proposition 16.1.1)

Miao, §16.1, pp. 537–538.

* (16.8): in a monetary equilibrium `m̂_{t+1}/m̂_t = R_{t+1}g_m/g_n > R_aut g_m/g_n`
  (`eq_16_8`).
* **Proposition 16.1.1**: a monetary equilibrium exists iff `R_aut g_m < g_n`
  (`proposition_16_1_1`). Necessity (`proposition_16_1_1_necessity`), the book's limiting step
  (`proposition_16_1_1_limit`), the stationary monetary equilibrium: existence and uniqueness of
  `m̂ ∈ (0, e₁)` with `u'(e₁ − m̂)/(βu'(e₂ + g_n m̂)) = g_n/g_m` (`proposition_16_1_1_root`), the
  constant path is a monetary equilibrium (`proposition_16_1_1_sufficiency`) and is the unique
  monetary equilibrium with constant real balances (`proposition_16_1_1_unique_stationary`); its
  interest rate is `g_n/g_m`, the golden rule `R = g_n` when `g_m = 1` (`ox_stationary_R`).

**Correction (necessity proof).** The book splits on `R_aut g_m/g_n > 1` and `= 1` and in the
second case takes limits in (16.6)–(16.7). The limit `m̂_∞` is always finite (`m̂_t < e₁`); what
the limiting argument needs is `m̂_∞ < e₁` (so that `u'` is continuous at `e₁ − m̂_∞`), which the
book does not check. `proposition_16_1_1_limit` proves the limit equation for `0 < m̂_∞ < e₁`.
The necessity proof given here avoids limits: since `m̂_t ≥ m̂₁`, `R_{t+1} ≥ u'(e₁ − m̂₁)/(βu'(e₂))
> R_aut`, so `m̂_t` grows at a rate bounded above one in both cases.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, (16.8), p. 538: in a monetary equilibrium
`m̂_{t+1}/m̂_t = R_{t+1} g_m/g_n > R_aut g_m/g_n`. -/
theorem eq_16_8 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_mhat q (t + 1) / E.ox_mhat q t = q (t + 1) / q t * E.ox_gm / E.ox_gn ∧
      E.ox_Raut * E.ox_gm / E.ox_gn < E.ox_mhat q (t + 1) / E.ox_mhat q t := by
  have h7 := E.eq_16_7 q (h.2 t ht)
  obtain ⟨-, hpos, -, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have he : E.ox_mhat q (t + 1) / E.ox_mhat q t = q (t + 1) / q t * E.ox_gm / E.ox_gn := by
    rw [h7]; field_simp
  refine ⟨he, ?_⟩
  rw [he]
  have := (E.eq_16_6 h ht).2
  have : E.ox_Raut * E.ox_gm < q (t + 1) / q t * E.ox_gm := mul_lt_mul_of_pos_right this hgm
  exact div_lt_div_of_pos_right this hgn

/-- **Proposition 16.1.1**, necessity (Miao, pp. 537–538): if a monetary equilibrium exists then
`R_aut g_m < g_n`. -/
theorem proposition_16_1_1_necessity {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    E.ox_Raut * E.ox_gm < E.ox_gn := by
  by_contra hcon
  have hge : E.ox_gn ≤ E.ox_Raut * E.ox_gm := not_lt.1 hcon
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have hβ := E.ox_P.ox_β_pos
  have alloc := (E.ox_monetary_alloc h).1
  set x := E.ox_mhat q
  have hx : ∀ t, 1 ≤ t → 0 < x t ∧ x t < E.ox_e1 := fun t ht =>
    ⟨(alloc t ht).2.1, (alloc t ht).2.2.1⟩
  -- real balances increase
  have hinc : ∀ t, 1 ≤ t → x t < x (t + 1) := fun t ht => by
    have h8 := (E.eq_16_8 h ht).2
    have h1 : 1 ≤ E.ox_Raut * E.ox_gm / E.ox_gn := (le_div_iff₀ hgn).2 (by linarith)
    have := (hx t ht).1
    have : 1 < x (t + 1) / x t := lt_of_le_of_lt h1 h8
    rwa [lt_div_iff₀ (hx t ht).1, one_mul] at this
  have hmono : ∀ n, x 1 ≤ x (n + 1) := fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact ih.trans (hinc (n + 1) (by omega)).le
  -- uniform lower bound on the interest rate
  set Rb := E.ox_P.ox_du (E.ox_e1 - x 1) / (E.ox_P.ox_β * E.ox_P.ox_du E.ox_e2)
  have hRb : E.ox_Raut < Rb := by
    have := E.ox_P.ox_du_lt (x := E.ox_e1 - x 1) (y := E.ox_e1) (by linarith [hx 1 le_rfl])
      (by linarith [(hx 1 le_rfl).1])
    have := E.ox_P.ox_du_pos _ E.ox_e2_pos
    unfold ox_Raut; simp only [Rb]
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  have hRt : ∀ n, Rb ≤ q (n + 2) / q (n + 1) := fun n => by
    have he := (E.eq_16_6 h (t := n + 1) (by omega)).1
    rw [← he]
    have hxn := hmono n
    have hxn1 := hx (n + 1) (by omega)
    have hxn2 := hx (n + 2) (by omega)
    have d1 : E.ox_P.ox_du (E.ox_e1 - x 1) ≤ E.ox_P.ox_du (E.ox_e1 - x (n + 1)) :=
      E.ox_P.ox_du_anti.antitoneOn (show (0 : ℝ) < E.ox_e1 - x (n + 1) by linarith)
        (show (0 : ℝ) < E.ox_e1 - x 1 by linarith [hx 1 le_rfl]) (by linarith)
    have d2 : E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (n + 2)) ≤ E.ox_P.ox_du E.ox_e2 :=
      E.ox_P.ox_du_anti.antitoneOn E.ox_e2_pos
        (show (0 : ℝ) < E.ox_e2 + E.ox_gn * x (n + 2) by nlinarith [E.ox_e2_pos])
        (by nlinarith)
    have p1 := E.ox_P.ox_du_pos _ (show (0 : ℝ) < E.ox_e1 - x 1 by linarith [hx 1 le_rfl])
    have p2 := E.ox_P.ox_du_pos _
      (show (0 : ℝ) < E.ox_e2 + E.ox_gn * x (n + 2) by nlinarith [E.ox_e2_pos])
    simp only [Rb]
    exact div_le_div₀ (by linarith) d1 (by positivity) (mul_le_mul_of_nonneg_left d2 hβ.le)
  set k := Rb * E.ox_gm / E.ox_gn
  have hk : 1 < k := by
    have : E.ox_Raut * E.ox_gm < Rb * E.ox_gm := mul_lt_mul_of_pos_right hRb hgm
    exact (lt_div_iff₀ hgn).2 (by linarith)
  have hgrow : ∀ n, k ^ n * x 1 ≤ x (n + 1) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have h8 := (E.eq_16_8 h (t := n + 1) (by omega)).1
      have hxn := (hx (n + 1) (by omega)).1
      have hr : k ≤ x (n + 2) / x (n + 1) := by
        rw [h8]
        have := mul_le_mul_of_nonneg_right (hRt n) hgm.le
        exact div_le_div_of_nonneg_right this hgn.le
      rw [le_div_iff₀ hxn] at hr
      calc k ^ (n + 1) * x 1 = k * (k ^ n * x 1) := by ring
        _ ≤ k * x (n + 1) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ x (n + 2) := by linarith
  have hx1 := (hx 1 le_rfl).1
  have htend : Tendsto (fun n => k ^ n * x 1) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hx1
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop E.ox_e1).exists
  linarith [hgrow n, (hx (n + 1) (by omega)).2]

/-- Miao, p. 538 (the limiting step of the necessity proof): if along a monetary equilibrium
`m̂_t → m̂_∞` with `0 < m̂_∞ < e₁`, then `u'(e₁ − m̂_∞)/(βu'(e₂ + g_n m̂_∞)) = R_∞ = g_n/g_m`;
since the left side exceeds `R_aut`, `R_aut g_m = g_n` is impossible. -/
theorem proposition_16_1_1_limit {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {L : ℝ}
    (hL : Tendsto (E.ox_mhat q) atTop (𝓝 L)) (hL0 : 0 < L) (hLe : L < E.ox_e1) :
    E.ox_P.ox_du (E.ox_e1 - L) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * L)) =
      E.ox_gn / E.ox_gm ∧ E.ox_Raut < E.ox_gn / E.ox_gm := by
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  set x := E.ox_mhat q
  have hL1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  -- the right side of (16.7) converges to g_n/g_m
  have hR : Tendsto (fun t => E.ox_gn * x (t + 1) / (E.ox_gm * x t)) atTop
      (𝓝 (E.ox_gn * L / (E.ox_gm * L))) :=
    (hL1.const_mul _).div (hL.const_mul _) (by positivity)
  have hRe : E.ox_gn * L / (E.ox_gm * L) = E.ox_gn / E.ox_gm := by field_simp
  rw [hRe] at hR
  -- the left side of (16.6) converges by continuity of `u'`
  have hc1 : ContinuousAt E.ox_P.ox_du (E.ox_e1 - L) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by linarith))
  have hc2 : ContinuousAt E.ox_P.ox_du (E.ox_e2 + E.ox_gn * L) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by nlinarith [E.ox_e2_pos]))
  have hp2 := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + E.ox_gn * L by nlinarith [E.ox_e2_pos])
  have hβ := E.ox_P.ox_β_pos
  have hlhs : Tendsto (fun t => E.ox_P.ox_du (E.ox_e1 - x t) /
      (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (t + 1)))) atTop
      (𝓝 (E.ox_P.ox_du (E.ox_e1 - L) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * L)))) :=
    (hc1.tendsto.comp (hL.const_sub _)).div
      ((hc2.tendsto.comp ((hL1.const_mul _).const_add _)).const_mul _) (by positivity)
  have heq : ∀ᶠ t in atTop, E.ox_P.ox_du (E.ox_e1 - x t) /
      (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (t + 1))) =
        E.ox_gn * x (t + 1) / (E.ox_gm * x t) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [(E.eq_16_6 h ht).1, E.eq_16_7 q (h.2 t ht)]
  have hlim := tendsto_nhds_unique (hlhs.congr' heq) hR
  refine ⟨hlim, ?_⟩
  rw [← hlim]
  exact E.ox_Raut_lt hL0 hLe (mul_pos hgn hL0)

/-- **Proposition 16.1.1**, the stationary root (Miao, p. 538): if `R_aut g_m < g_n` there is a
unique `m̂ ∈ (0, e₁)` with `u'(e₁ − m̂) = β(g_n/g_m)u'(e₂ + g_n m̂)`. -/
theorem proposition_16_1_1_root (hR : E.ox_Raut * E.ox_gm < E.ox_gn) :
    ∃! mh, 0 < mh ∧ mh < E.ox_e1 ∧ E.ox_P.ox_du (E.ox_e1 - mh) =
      E.ox_P.ox_β * (E.ox_gn / E.ox_gm) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * mh) := by
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have hβ := E.ox_P.ox_β_pos
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hd2 := E.ox_P.ox_du_pos _ he2
  set K := E.ox_P.ox_β * (E.ox_gn / E.ox_gm)
  have hK : 0 < K := by positivity
  set F : ℝ → ℝ := fun x => E.ox_P.ox_du (E.ox_e1 - x) - K * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x)
  have hF0 : F 0 < 0 := by
    simp only [F, sub_zero, mul_zero, add_zero]
    have : E.ox_Raut < E.ox_gn / E.ox_gm := (lt_div_iff₀ hgm).2 hR
    unfold ox_Raut at this
    rw [div_lt_iff₀ (by positivity)] at this
    simp only [K]; linarith
  -- an interior point where `F > 0`, from the Inada condition
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), K * E.ox_P.ox_du E.ox_e2 < E.ox_P.ox_du y ∧ y < E.ox_e1 ∧
      0 < y :=
    (E.ox_P.ox_inada.eventually_gt_atTop _).and
      ((show ∀ᶠ y in 𝓝[>] (0 : ℝ), y < E.ox_e1 from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds he1)).and self_mem_nhdsWithin)
  obtain ⟨δ, hδK, hδe, hδ0⟩ := hev.exists
  set b := E.ox_e1 - δ
  have hb0 : 0 < b := by simp only [b]; linarith
  have hFb : 0 < F b := by
    simp only [F, b, sub_sub_cancel]
    have : E.ox_P.ox_du (E.ox_e2 + E.ox_gn * (E.ox_e1 - δ)) ≤ E.ox_P.ox_du E.ox_e2 :=
      E.ox_P.ox_du_anti.antitoneOn he2 (show (0 : ℝ) < _ by nlinarith) (by nlinarith)
    nlinarith
  have hcont : ContinuousOn F (Set.Icc 0 b) := by
    refine ContinuousOn.sub ?_ (ContinuousOn.mul continuousOn_const ?_)
    · refine E.ox_P.ox_du_cont.comp (continuousOn_const.sub continuousOn_id) fun x hx => ?_
      simp only [Set.mem_Ioi]; linarith [hx.2]
    · refine E.ox_P.ox_du_cont.comp (continuousOn_const.add
        (continuousOn_const.mul continuousOn_id)) fun x hx => ?_
      simp only [Set.mem_Ioi]; nlinarith [hx.1]
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hb0.le hcont ⟨hF0.le, hFb.le⟩
  have hx0 : 0 < x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h] at hFx; linarith
    · exact h
  have hxe : x < E.ox_e1 := by linarith [hx.2]
  -- `F` is strictly increasing
  have hFmono : ∀ y z, 0 < y → y < z → z < E.ox_e1 → F y < F z := fun y z hy hyz hz => by
    have d1 := E.ox_P.ox_du_lt (x := E.ox_e1 - z) (y := E.ox_e1 - y) (by linarith) (by linarith)
    have d2 := E.ox_P.ox_du_lt (x := E.ox_e2 + E.ox_gn * y) (y := E.ox_e2 + E.ox_gn * z)
      (by nlinarith) (by nlinarith)
    simp only [F]; nlinarith
  refine ⟨x, ⟨hx0, hxe, by simp only [F] at hFx; linarith⟩, ?_⟩
  rintro y ⟨hy0, hye, hy⟩
  have hFy : F y = 0 := by simp only [F]; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · linarith [hFmono y x hy0 hlt hxe]
  · linarith [hFmono x y hx0 hlt hye]

/-- The constant saving path `m̂` satisfies the saving difference equation iff `m̂` is the
stationary root. -/
theorem ox_eulerRel_const_iff {mh : ℝ} (h0 : 0 < mh) (he : mh < E.ox_e1) :
    E.ox_EulerRel mh mh ↔ E.ox_P.ox_du (E.ox_e1 - mh) =
      E.ox_P.ox_β * (E.ox_gn / E.ox_gm) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * mh) := by
  have : E.ox_gn * mh / (E.ox_gm * mh) = E.ox_gn / E.ox_gm := by
    have := E.ox_gm_pos.ne'; field_simp
  unfold ox_EulerRel
  rw [this]
  exact ⟨fun h => h.2.2.2.2, fun h => ⟨h0, he, h0, he, h⟩⟩

/-- **Proposition 16.1.1**, sufficiency (Miao, p. 538): if `R_aut g_m < g_n`, the constant path
`m̂_t = m̂` (the stationary root) is a monetary equilibrium. -/
theorem proposition_16_1_1_sufficiency (hR : E.ox_Raut * E.ox_gm < E.ox_gn) :
    ∃ mh : ℝ, 0 < mh ∧ mh < E.ox_e1 ∧ E.ox_IsMonetary (E.ox_qOf fun _ => mh)
      (fun _ => E.ox_e1 - mh) (fun _ => E.ox_e2 + E.ox_gn * mh)
      (fun t => E.ox_M t / E.ox_N t) := by
  obtain ⟨mh, ⟨h0, he, hroot⟩, -⟩ := E.proposition_16_1_1_root hR
  exact ⟨mh, h0, he, E.ox_ofSaving_isMonetary (mh := fun _ => mh)
    fun _ _ => (E.ox_eulerRel_const_iff h0 he).2 hroot⟩

/-- **Proposition 16.1.1** (Miao, p. 537): `R_aut g_m < g_n` is necessary and sufficient for the
existence of at least one monetary equilibrium. -/
theorem proposition_16_1_1 :
    (∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m) ↔ E.ox_Raut * E.ox_gm < E.ox_gn := by
  constructor
  · rintro ⟨q, cy, co, m, h⟩
    exact E.proposition_16_1_1_necessity h
  · intro hR
    obtain ⟨mh, -, -, h⟩ := E.proposition_16_1_1_sufficiency hR
    exact ⟨_, _, _, _, h⟩

/-- Miao, p. 538: the equilibrium with constant per-capita real balances is unique: in every
monetary equilibrium with `m̂_t = m̂` for all `t ≥ 1`, `m̂` is the stationary root. -/
theorem proposition_16_1_1_unique_stationary {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m)
    {mh : ℝ} (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) :
    0 < mh ∧ mh < E.ox_e1 ∧ E.ox_P.ox_du (E.ox_e1 - mh) =
      E.ox_P.ox_β * (E.ox_gn / E.ox_gm) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * mh) := by
  have hrel := E.ox_monetary_eulerRel h (t := 1) le_rfl
  rw [hc 1 le_rfl, hc 2 (by omega)] at hrel
  exact ⟨hrel.1, hrel.2.1, (E.ox_eulerRel_const_iff hrel.1 hrel.2.1).1 hrel⟩

/-- Miao, p. 538 (the golden rule): in a monetary equilibrium with constant real balances the
gross interest rate is `R_{t+1} = g_n/g_m`; with `g_m = 1` it is the population growth factor. -/
theorem ox_stationary_R {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {mh : ℝ}
    (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) {t : ℕ} (ht : 1 ≤ t) :
    q (t + 1) / q t = E.ox_gn / E.ox_gm := by
  rw [E.eq_16_7 q (h.2 t ht), hc t ht, hc (t + 1) (by omega)]
  have := (E.proposition_16_1_1_unique_stationary h hc).1
  have := E.ox_gm_pos.ne'
  field_simp

end OXEconomy

end Miao.OverlappingGenerations
